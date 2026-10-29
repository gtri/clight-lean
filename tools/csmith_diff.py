#!/usr/bin/env python3
"""Run one fixed-signature CSmith checksum source through native and Lean paths.

This is deliberately a source-input harness.  It does not invoke CSmith or
claim that a random-generation profile has been selected yet.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
import traceback
from typing import Any, Sequence


SCRIPT_PATH = Path(__file__).resolve()
WORKSPACE = SCRIPT_PATH.parent.parent
CONFIG_PATH = SCRIPT_PATH.with_name("csmith-diff-phase0.json")
ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
ENVELOPE_RE = re.compile(
    rb"CLIGHT_LEAN_RUNNER_V1 "
    rb"status=([A-Za-z][A-Za-z0-9_-]*) "
    rb"steps=([0-9]+) "
    rb"exit=(-|[+-]?[0-9]+) "
    rb"error_code=(-|[A-Za-z][A-Za-z0-9_-]*) "
    rb"stdout_hex=([0-9A-Fa-f]*)"
)


class HarnessError(RuntimeError):
    """A configuration, filesystem, or process-supervision error."""


class EnvelopeError(ValueError):
    """The Lean host stdout is not one unambiguous CSmithIO envelope."""


@dataclasses.dataclass(frozen=True)
class Envelope:
    status: str
    steps: int
    c_exit: str
    error_code: str
    stdout: bytes

    def as_json(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "steps": self.steps,
            "c_main_exit": self.c_exit,
            "error_code": self.error_code,
            "stdout_bytes": len(self.stdout),
            "stdout_sha256": sha256_bytes(self.stdout),
            "stdout_hex": self.stdout.hex(),
        }


@dataclasses.dataclass
class ProcessResult:
    argv: list[str]
    cwd: str
    started_at: str
    finished_at: str
    duration_seconds: float
    returncode: int | None
    stdout: bytes
    stderr: bytes
    spawn_error: str | None = None

    def as_json(self) -> dict[str, Any]:
        result: dict[str, Any] = {
            "argv": self.argv,
            "cwd": self.cwd,
            "started_at": self.started_at,
            "finished_at": self.finished_at,
            "duration_seconds": self.duration_seconds,
            "returncode": self.returncode,
            "stdout_bytes": len(self.stdout),
            "stdout_sha256": sha256_bytes(self.stdout),
            "stderr_bytes": len(self.stderr),
            "stderr_sha256": sha256_bytes(self.stderr),
        }
        if self.spawn_error is not None:
            result["spawn_error"] = self.spawn_error
        return result


@dataclasses.dataclass(frozen=True)
class Paths:
    workspace: Path
    source: Path
    compcert_root: Path
    csmith_root: Path
    ccomp: Path
    clightgen: Path
    compcert_runtime: Path
    native_runtime_source: Path
    include_dirs: tuple[Path, ...]
    generated_max_rec_depth: int
    timeout: Path
    lake: Path
    generated_root: Path
    build_root: Path
    artifact_root: Path


@dataclasses.dataclass
class CaseContext:
    paths: Paths
    config: dict[str, Any]
    run_id: str
    case_id: str
    timeout_seconds: float
    artifact_dir: Path
    generated_dir: Path
    case_build_dir: Path
    source_copy: Path
    native_dir: Path
    lean_dir: Path
    metadata: dict[str, Any]
    records: dict[str, Any]


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="milliseconds").replace(
        "+00:00", "Z"
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: Any) -> None:
    """Serialize only JSON-compatible data, deterministically and without shelling out."""
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=True)
        handle.write("\n")


def write_bytes(path: Path, value: bytes) -> None:
    with path.open("wb") as handle:
        handle.write(value)


def require_file(path: Path, description: str, executable: bool = False) -> None:
    if not path.is_file():
        raise HarnessError(f"{description} is not a file: {path}")
    if executable and not os.access(path, os.X_OK):
        raise HarnessError(f"{description} is not executable: {path}")


def require_dir(path: Path, description: str) -> None:
    if not path.is_dir():
        raise HarnessError(f"{description} is not a directory: {path}")


def require_safe_id(value: str, option: str) -> str:
    if not ID_RE.fullmatch(value):
        raise HarnessError(
            f"{option} must be a nonempty Lean module identifier "
            "([A-Za-z][A-Za-z0-9_]*): "
            f"{value!r}"
        )
    return value


def require_under(path: Path, root: Path, description: str) -> None:
    try:
        path.relative_to(root)
    except ValueError as error:
        raise HarnessError(f"{description} escapes its allowed root {root}: {path}") from error


def absolute_cli_path(value: str) -> Path:
    return Path(value).expanduser().resolve()


def workspace_relative_path(value: str) -> Path:
    return (WORKSPACE / value).resolve()


def load_config() -> dict[str, Any]:
    require_file(CONFIG_PATH, "committed Phase 0 tool configuration")
    try:
        with CONFIG_PATH.open("r", encoding="utf-8") as handle:
            config = json.load(handle)
    except (OSError, json.JSONDecodeError) as error:
        raise HarnessError(f"could not read Phase 0 tool configuration {CONFIG_PATH}: {error}") from error
    if not isinstance(config, dict) or config.get("schema_version") != 1:
        raise HarnessError(f"unsupported Phase 0 tool configuration schema in {CONFIG_PATH}")
    siblings = config.get("sibling_checkouts")
    layout = config.get("workspace_layout")
    elaboration = config.get("generated_program_elaboration")
    if not isinstance(siblings, dict) or not isinstance(layout, dict) or not isinstance(elaboration, dict):
        raise HarnessError(f"incomplete sibling/layout data in {CONFIG_PATH}")
    for key in ("compcert", "csmith"):
        if not isinstance(siblings.get(key), str):
            raise HarnessError(f"missing sibling_checkouts.{key} in {CONFIG_PATH}")
    expected_layout = {
        "generated_case_modules": "GeneratedCases",
        "case_build_output": ".csmith-diff-build",
        "retained_artifacts": "artifacts/csmith",
    }
    if {key: layout.get(key) for key in expected_layout} != expected_layout:
        raise HarnessError(
            "Phase 0 layout does not match the repository's restricted ignored output roots"
        )
    max_rec_depth = elaboration.get("max_rec_depth")
    if not isinstance(max_rec_depth, int) or isinstance(max_rec_depth, bool) or max_rec_depth <= 0:
        raise HarnessError(
            f"generated_program_elaboration.max_rec_depth must be a positive integer in {CONFIG_PATH}"
        )
    return config


def validate_ignored_policy() -> None:
    policy = WORKSPACE / ".gitignore"
    require_file(policy, "ignored-path policy")
    try:
        entries = set(policy.read_text(encoding="utf-8").splitlines())
    except OSError as error:
        raise HarnessError(f"could not read ignored-path policy {policy}: {error}") from error
    for entry in ("/GeneratedCases/", "/.csmith-diff-build/", "/artifacts/csmith/"):
        if entry not in entries:
            raise HarnessError(f"ignored-path policy does not contain required entry {entry}")


def executable_from_path(name: str) -> Path:
    found = shutil.which(name)
    if found is None:
        raise HarnessError(f"required host tool is not on PATH: {name}")
    path = Path(found).resolve()
    require_file(path, f"host tool {name}", executable=True)
    return path


def format_timeout_seconds(seconds: float) -> str:
    return f"{seconds:g}s"


def parse_timeout_seconds(value: str) -> float:
    try:
        seconds = float(value)
    except ValueError as error:
        raise HarnessError("--timeout-seconds must be a finite positive number") from error
    if not math.isfinite(seconds) or seconds <= 0:
        raise HarnessError("--timeout-seconds must be a finite positive number")
    return seconds


def default_run_id() -> str:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"run{stamp}_pid{os.getpid()}"


def read_cli(args: argparse.Namespace) -> tuple[Paths, dict[str, Any], str, str, float]:
    if args.source is None:
        raise HarnessError("--source PATH is required unless --self-test-envelope is used")
    config = load_config()
    validate_ignored_policy()
    require_dir(WORKSPACE, "workspace root")

    siblings = config["sibling_checkouts"]
    compcert_root = (
        absolute_cli_path(args.compcert_root)
        if args.compcert_root is not None
        else workspace_relative_path(siblings["compcert"])
    )
    csmith_root = (
        absolute_cli_path(args.csmith_root)
        if args.csmith_root is not None
        else workspace_relative_path(siblings["csmith"])
    )
    source = absolute_cli_path(args.source)
    native_runtime_source = (
        absolute_cli_path(args.native_runtime_source)
        if args.native_runtime_source is not None
        else workspace_relative_path("Test/CSmithSeeds/csmith_checksum_runtime.c")
    )
    include_dirs = tuple(
        absolute_cli_path(value)
        for value in (args.include_dir or ["Test/CSmithSeeds"])
    )

    require_file(source, "C source input")
    require_dir(compcert_root, "CompCert root")
    require_dir(csmith_root, "CSmith root")
    ccomp = (compcert_root / "ccomp").resolve()
    clightgen = (compcert_root / "clightgen").resolve()
    compcert_runtime = (compcert_root / "runtime").resolve()
    require_file(ccomp, "CompCert ccomp", executable=True)
    require_file(clightgen, "CompCert clightgen", executable=True)
    require_dir(compcert_runtime, "CompCert runtime directory")
    require_file(native_runtime_source, "native checksum companion runtime")
    for index, include_dir in enumerate(include_dirs, start=1):
        require_dir(include_dir, f"C include directory {index}")

    timeout_seconds = parse_timeout_seconds(args.timeout_seconds)

    layout = config["workspace_layout"]
    generated_max_rec_depth = config["generated_program_elaboration"]["max_rec_depth"]
    generated_root = workspace_relative_path(layout["generated_case_modules"])
    build_root = workspace_relative_path(layout["case_build_output"])
    artifact_root = workspace_relative_path(layout["retained_artifacts"])
    workspace_resolved = WORKSPACE.resolve()
    for root, label in (
        (generated_root, "GeneratedCases root"),
        (build_root, ".csmith-diff-build root"),
        (artifact_root, "artifact root"),
    ):
        require_under(root, workspace_resolved, label)

    run_id = require_safe_id(args.run_id or default_run_id(), "--run-id")
    case_id = require_safe_id(args.case_id, "--case-id")
    paths = Paths(
        workspace=workspace_resolved,
        source=source,
        compcert_root=compcert_root,
        csmith_root=csmith_root,
        ccomp=ccomp,
        clightgen=clightgen,
        compcert_runtime=compcert_runtime,
        native_runtime_source=native_runtime_source,
        include_dirs=include_dirs,
        generated_max_rec_depth=generated_max_rec_depth,
        timeout=executable_from_path("timeout"),
        lake=executable_from_path("lake"),
        generated_root=generated_root,
        build_root=build_root,
        artifact_root=artifact_root,
    )
    return paths, config, run_id, case_id, timeout_seconds


def run_capture(argv: Sequence[str], cwd: Path) -> ProcessResult:
    started_at = utc_now()
    started = time.monotonic()
    try:
        completed = subprocess.run(
            list(argv),
            cwd=str(cwd),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        returncode = completed.returncode
        stdout = completed.stdout
        stderr = completed.stderr
        spawn_error = None
    except OSError as error:
        returncode = None
        stdout = b""
        stderr = b""
        spawn_error = f"{type(error).__name__}: {error}"
    finished_at = utc_now()
    return ProcessResult(
        argv=[str(value) for value in argv],
        cwd=str(cwd),
        started_at=started_at,
        finished_at=finished_at,
        duration_seconds=round(time.monotonic() - started, 6),
        returncode=returncode,
        stdout=stdout,
        stderr=stderr,
        spawn_error=spawn_error,
    )


def probe_version(argv: Sequence[str], cwd: Path) -> dict[str, Any]:
    result = run_capture(argv, cwd)
    output = result.as_json()
    output["stdout_text"] = result.stdout.decode("utf-8", errors="replace")
    output["stderr_text"] = result.stderr.decode("utf-8", errors="replace")
    return output


def timeout_argv(paths: Paths, timeout_seconds: float, argv: Sequence[str]) -> list[str]:
    return [
        str(paths.timeout),
        "--signal=TERM",
        "--kill-after=1s",
        format_timeout_seconds(timeout_seconds),
        *[str(item) for item in argv],
    ]


def child_reporter_argv(record_path: Path, argv: Sequence[str]) -> list[str]:
    return [
        str(Path(sys.executable).resolve()),
        str(SCRIPT_PATH),
        "--_record-child-result",
        str(record_path),
        "--",
        *[str(item) for item in argv],
    ]


def run_child_reporter(record_path: Path, argv: Sequence[str]) -> int:
    """Run one command and preserve its raw termination status for the parent.

    GNU `timeout` reports a signal as an ordinary 128+signal exit status, which
    is indistinguishable from a program that explicitly returned that value.
    This small self-invocation records the `Popen` return code before exiting
    successfully.  It also forwards TERM from `timeout` to the program, so the
    parent can distinguish a real program signal from a timeout.
    """
    child_argv = list(argv)
    if child_argv[:1] == ["--"]:
        child_argv = child_argv[1:]
    if not child_argv:
        write_json(record_path, {"spawn_error": "no child command supplied"})
        return 0
    try:
        child = subprocess.Popen(
            child_argv, stdin=None, stdout=None, stderr=None, start_new_session=True
        )
    except OSError as error:
        write_json(record_path, {"argv": child_argv, "spawn_error": f"{type(error).__name__}: {error}"})
        return 0

    received_signals: list[int] = []
    termination_received_at: float | None = None
    forced_kill = False

    def forward_signal(signum: int, _frame: Any) -> None:
        nonlocal termination_received_at
        received_signals.append(signum)
        if child.poll() is None:
            # The independently created process group includes descendants of a
            # shell launcher, not only its immediate process.
            os.killpg(child.pid, signum)
        if signum == signal.SIGTERM and termination_received_at is None:
            termination_received_at = time.monotonic()

    previous_handlers: dict[int, Any] = {}
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        previous_handlers[signum] = signal.signal(signum, forward_signal)
    try:
        while True:
            try:
                returncode = child.wait(timeout=0.05)
                break
            except subprocess.TimeoutExpired:
                # Do not let a TERM-ignoring program outlive the reporter when
                # GNU timeout subsequently KILLs it after the documented 1 s.
                if (
                    termination_received_at is not None
                    and not forced_kill
                    and time.monotonic() - termination_received_at >= 0.9
                ):
                    os.killpg(child.pid, signal.SIGKILL)
                    forced_kill = True
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    write_json(
        record_path,
        {
            "argv": [str(item) for item in child_argv],
            "returncode": returncode,
            "received_signals": received_signals,
            "forced_kill": forced_kill,
        },
    )
    return 0


def read_child_report(record_path: Path) -> dict[str, Any] | None:
    if not record_path.is_file():
        return None
    try:
        with record_path.open("r", encoding="utf-8") as handle:
            report = json.load(handle)
    except (OSError, json.JSONDecodeError) as error:
        raise HarnessError(f"invalid supervised child result {record_path}: {error}") from error
    if not isinstance(report, dict):
        raise HarnessError(f"invalid supervised child result {record_path}: expected object")
    if "spawn_error" in report:
        if not isinstance(report["spawn_error"], str):
            raise HarnessError(f"invalid supervised child result {record_path}: invalid spawn_error")
    elif not isinstance(report.get("returncode"), int):
        raise HarnessError(f"invalid supervised child result {record_path}: missing integer returncode")
    return report


def supervised_outcome(result: ProcessResult, report: dict[str, Any] | None) -> dict[str, Any]:
    """Classify a timeout-supervised reporter and its actual child result."""
    if result.spawn_error is not None:
        return {"kind": "spawn_error", "detail": result.spawn_error}
    if result.returncode == 124:
        return {"kind": "timeout", "timeout_exit_code": 124}
    if report is None:
        # A timeout that escalates to KILL has no opportunity to emit the child
        # report.  The reporter otherwise exits zero, so a nonzero timeout
        # process here is supervision failure rather than program behavior.
        if result.returncode in (137, 143):
            return {"kind": "timeout", "timeout_exit_code": result.returncode}
        return {"kind": "report_missing", "timeout_exit_code": result.returncode}
    if "spawn_error" in report:
        return {"kind": "spawn_error", "detail": report["spawn_error"]}
    received_signals = report.get("received_signals", [])
    if not isinstance(received_signals, list) or not all(
        isinstance(signum, int) for signum in received_signals
    ):
        return {"kind": "report_invalid", "detail": "invalid received_signals"}
    if signal.SIGTERM in received_signals:
        return {"kind": "timeout", "timeout_exit_code": result.returncode}
    returncode = report["returncode"]
    if returncode < 0:
        return {"kind": "signal", "signal": -returncode, "program_returncode": returncode}
    if result.returncode != 0:
        return {
            "kind": "supervisor_error",
            "timeout_exit_code": result.returncode,
            "program_returncode": returncode,
        }
    return {"kind": "normal_exit", "exit_code": returncode, "program_returncode": returncode}


def process_outcome(result: ProcessResult) -> dict[str, Any]:
    if result.spawn_error is not None:
        return {"kind": "spawn_error", "detail": result.spawn_error}
    if result.returncode == 124:
        return {"kind": "timeout"}
    if result.returncode is not None and result.returncode < 0:
        return {"kind": "signal", "signal": -result.returncode, "encoding": "subprocess"}
    return {"kind": "normal_exit", "exit_code": result.returncode}


def write_phase(
    directory: Path,
    phase: str,
    result: ProcessResult,
    extra: dict[str, Any] | None = None,
    outcome: dict[str, Any] | None = None,
) -> dict[str, Any]:
    write_json(
        directory / f"{phase}.command.json",
        {"argv": result.argv, "cwd": result.cwd},
    )
    write_bytes(directory / f"{phase}.stdout", result.stdout)
    write_bytes(directory / f"{phase}.stderr", result.stderr)
    record = result.as_json()
    record["status"] = "executed"
    record["process_outcome"] = outcome if outcome is not None else process_outcome(result)
    if extra:
        record.update(extra)
    write_json(directory / f"{phase}.result.json", record)
    return record


def write_not_run_phase(directory: Path, phase: str, reason: str) -> None:
    write_bytes(directory / f"{phase}.stdout", b"")
    write_bytes(directory / f"{phase}.stderr", b"")
    write_json(directory / f"{phase}.result.json", {"status": "not_run", "reason": reason})


def parse_envelope(stdout: bytes) -> Envelope:
    """Parse exactly one CSmithIO protocol line and decode its raw stdout bytes."""
    if not stdout.endswith(b"\n"):
        raise EnvelopeError("expected exactly one LF-terminated CSmithIO stdout line")
    line = stdout[:-1]
    if not line or b"\n" in line or b"\r" in line:
        raise EnvelopeError("expected exactly one nonempty CSmithIO stdout line")
    matched = ENVELOPE_RE.fullmatch(line)
    if matched is None:
        raise EnvelopeError("stdout does not match the fixed CSmithIO envelope grammar")
    status, steps, c_exit, error_code, stdout_hex = (
        group.decode("ascii") for group in matched.groups()
    )
    if len(stdout_hex) % 2 != 0:
        raise EnvelopeError("stdout_hex must contain an even number of hex digits")
    try:
        modeled_stdout = bytes.fromhex(stdout_hex)
    except ValueError as error:
        raise EnvelopeError(f"stdout_hex is not hexadecimal: {error}") from error
    return Envelope(
        status=status,
        steps=int(steps),
        c_exit=c_exit,
        error_code=error_code,
        stdout=modeled_stdout,
    )


def validate_envelope_semantics(envelope: Envelope) -> str | None:
    if envelope.status == "completed":
        if envelope.c_exit == "-" or envelope.error_code != "-":
            return "completed envelope must contain a C exit value and error_code=-"
    elif envelope.status in {"unsupported", "stuck", "initialization_error"}:
        if envelope.c_exit != "-" or envelope.error_code == "-":
            return f"{envelope.status} envelope has inconsistent exit/error fields"
    return None


def generated_module_name(run_id: str, case_id: str) -> str:
    return f"GeneratedCases.{run_id}.{case_id}.Program"


def case_main_source(module_name: str) -> str:
    return f"""import CLightLean.Exec.CSmithIO
import {module_name}

open CLightLean.Exec

def main : IO Unit := do
  let result ← runCSmithProgramUntilTermination _root_.prog
  IO.println (renderCSmithProgramEnvelope result)
  match result with
  | .ok (.completed ..) => pure ()
  | _ => IO.Process.exit 1
"""


def case_build_lakefile(paths: Paths) -> str:
    """A per-case Lake package exposes the ignored GeneratedCases module tree.

    The main package deliberately does not declare `GeneratedCases` as a shared
    library.  This isolated package avoids editing its lakefile while letting
    Lake resolve the static import generated for one case.
    """
    mathlib = paths.workspace / ".lake" / "packages" / "mathlib"
    require_dir(mathlib, "main workspace mathlib dependency")
    floatlib = paths.workspace / ".lake" / "packages" / "floatlib"
    require_dir(floatlib, "main workspace floatlib dependency")
    return f"""name = \"CSmithDiffCase\"
version = \"0.1.0\"

[[lean_lib]]
name = \"CLightLean\"
moreLeanArgs = [\"-DautoImplicit=false\"]

[[lean_lib]]
name = \"GeneratedCases\"
moreLeanArgs = [\"-DmaxRecDepth={paths.generated_max_rec_depth}\"]

[[require]]
name = \"mathlib\"
path = {json.dumps(str(mathlib))}

[[require]]
name = \"floatlib\"
path = {json.dumps(str(floatlib))}
"""


def create_replay_script(context: CaseContext) -> None:
    command_prefix = [
        str(Path(sys.executable).resolve()),
        str(SCRIPT_PATH),
        "--source",
        str(context.source_copy),
        "--run-id",
    ]
    command_suffix = [
        "--case-id",
        context.case_id,
        "--timeout-seconds",
        format_timeout_seconds(context.timeout_seconds)[:-1],
        "--compcert-root",
        str(context.paths.compcert_root),
        "--csmith-root",
        str(context.paths.csmith_root),
        "--native-runtime-source",
        str(context.paths.native_runtime_source),
        *[
            option
            for include_dir in context.paths.include_dirs
            for option in ("--include-dir", str(include_dir))
        ],
    ]
    shell_command = (
        shlex.join(command_prefix) + " \"$replay_run_id\" " + shlex.join(command_suffix)
    )
    replay_path = context.artifact_dir / "replay.sh"
    replay_path.write_text(
        "#!/bin/sh\n"
        "# Replay with a fresh immutable artifact/module namespace on every invocation.\n"
        f"replay_run_id=replay_{context.run_id}_$(date -u +%Y%m%dT%H%M%SZ)_$$\n"
        f"exec {shell_command}\n",
        encoding="utf-8",
        newline="\n",
    )
    replay_path.chmod(0o755)
    context.metadata["replay_command"] = {
        "argv_prefix": command_prefix,
        "run_id": "generated at replay time by replay.sh",
        "argv_suffix": command_suffix,
    }


def create_context(args: argparse.Namespace) -> CaseContext:
    paths, config, run_id, case_id, timeout_seconds = read_cli(args)
    artifact_dir = (paths.artifact_root / run_id / case_id).resolve()
    generated_dir = (paths.generated_root / run_id / case_id).resolve()
    case_build_dir = (paths.build_root / run_id / case_id).resolve()
    require_under(artifact_dir, paths.artifact_root, "case artifact directory")
    require_under(generated_dir, paths.generated_root, "generated case directory")
    require_under(case_build_dir, paths.build_root, "case build directory")
    if artifact_dir.exists():
        raise HarnessError(f"refusing to overwrite existing artifact case directory: {artifact_dir}")
    if generated_dir.exists():
        raise HarnessError(f"refusing to overwrite existing generated case directory: {generated_dir}")
    if case_build_dir.exists():
        raise HarnessError(f"refusing to overwrite existing case build directory: {case_build_dir}")

    # These are the only directories created directly by the harness. Lake may
    # maintain its own package cache while executing the required `lake build`.
    artifact_dir.mkdir(parents=True, exist_ok=False)
    generated_dir.mkdir(parents=True, exist_ok=False)
    case_build_dir.mkdir(parents=True, exist_ok=False)
    for name in ("CLightLean", "GeneratedCases"):
        os.symlink(paths.workspace / name, case_build_dir / name, target_is_directory=True)
    (case_build_dir / "lakefile.toml").write_text(
        case_build_lakefile(paths), encoding="utf-8", newline="\n"
    )
    native_dir = artifact_dir / "native"
    lean_dir = artifact_dir / "lean"
    native_dir.mkdir()
    lean_dir.mkdir()

    source_copy = artifact_dir / "source.c"
    shutil.copyfile(paths.source, source_copy)
    metadata: dict[str, Any] = {
        "schema_version": 1,
        "harness": {
            "script": str(SCRIPT_PATH),
            "python_executable": str(Path(sys.executable).resolve()),
            "python_version": sys.version,
            "argv": sys.argv,
            "workspace": str(paths.workspace),
            "source_generation": "not invoked; this harness accepts an explicit source only",
        },
        "identifiers": {"run_id": run_id, "case_id": case_id},
        "started_at": utc_now(),
        "paths": {
            "source": str(paths.source),
            "source_copy": str(source_copy),
            "compcert_root": str(paths.compcert_root),
            "csmith_root": str(paths.csmith_root),
            "ccomp": str(paths.ccomp),
            "clightgen": str(paths.clightgen),
            "compcert_runtime": str(paths.compcert_runtime),
            "native_runtime_source": str(paths.native_runtime_source),
            # Retain the original singular field for existing consumers while
            # recording the complete ordered preprocessing contract.
            "include_dir": str(paths.include_dirs[0]),
            "include_dirs": [str(include_dir) for include_dir in paths.include_dirs],
            "generated_dir": str(generated_dir),
            "case_build_dir": str(case_build_dir),
            "artifact_dir": str(artifact_dir),
        },
        "source": {
            "bytes": paths.source.stat().st_size,
            "sha256": sha256_file(paths.source),
        },
        "generated_program_elaboration": {
            "max_rec_depth": paths.generated_max_rec_depth,
            "max_heartbeats": "Lean default",
            "scope": "isolated GeneratedCases library only",
        },
        "config": {
            "path": str(CONFIG_PATH),
            "sha256": sha256_file(CONFIG_PATH),
            "content": config,
        },
        "timeouts": {
            "seconds": timeout_seconds,
            "timeout_argv_prefix": [
                str(paths.timeout),
                "--signal=TERM",
                "--kill-after=1s",
                format_timeout_seconds(timeout_seconds),
            ],
        },
        "environment_delta": {
            "policy": "inherited unchanged; no environment variables are added, removed, or overridden"
        },
        "tool_versions": {
            "ccomp": probe_version([str(paths.ccomp), "-version"], paths.workspace),
            "clightgen": probe_version([str(paths.clightgen), "-version"], paths.workspace),
            "lake": probe_version([str(paths.lake), "--version"], paths.workspace),
            "gnu_timeout": probe_version([str(paths.timeout), "--version"], paths.workspace),
            "csmith": {
                "root": str(paths.csmith_root),
                "version": "not probed: random source generation is out of scope for this phase",
            },
        },
    }
    context = CaseContext(
        paths=paths,
        config=config,
        run_id=run_id,
        case_id=case_id,
        timeout_seconds=timeout_seconds,
        artifact_dir=artifact_dir,
        generated_dir=generated_dir,
        case_build_dir=case_build_dir,
        source_copy=source_copy,
        native_dir=native_dir,
        lean_dir=lean_dir,
        metadata=metadata,
        records={},
    )
    create_replay_script(context)
    write_json(artifact_dir / "metadata.json", metadata)
    return context


def update_not_run_records(context: CaseContext, native_reason: str, lean_reason: str) -> None:
    for phase in ("compile", "run"):
        path = context.native_dir / f"{phase}.result.json"
        if not path.exists():
            write_not_run_phase(context.native_dir, phase, native_reason)
    for phase in ("clightgen", "build", "run"):
        path = context.lean_dir / f"{phase}.result.json"
        if not path.exists():
            write_not_run_phase(context.lean_dir, phase, lean_reason)


def finish(context: CaseContext, verdict: str, reason: str, extra: dict[str, Any] | None = None) -> dict[str, Any]:
    update_not_run_records(context, "not reached", "not reached")
    verdict_record: dict[str, Any] = {
        "schema_version": 1,
        "verdict": verdict,
        "reason": reason,
        "run_id": context.run_id,
        "case_id": context.case_id,
        "artifact_dir": str(context.artifact_dir),
        "source": str(context.paths.source),
        "native": context.records.get("native", {}),
        "lean": context.records.get("lean", {}),
        "comparison": context.records.get("comparison", {}),
        "finished_at": utc_now(),
    }
    if extra:
        verdict_record["detail"] = extra
    write_json(context.artifact_dir / "verdict.json", verdict_record)
    context.metadata["finished_at"] = verdict_record["finished_at"]
    context.metadata["final_verdict"] = verdict
    write_json(context.artifact_dir / "metadata.json", context.metadata)
    return verdict_record


def run_pipeline(context: CaseContext) -> dict[str, Any]:
    paths = context.paths
    native_program = context.native_dir / "program"
    # CSmith's safe floating wrappers call the exact fabs/fabsf support ABIs.
    # The restricted Lean executor models those calls; the native CompCert
    # executable links libm for their host implementation.
    native_compile_argv = [
        str(paths.ccomp),
        "-stdlib",
        str(paths.compcert_runtime),
        *[f"-I{include_dir}" for include_dir in paths.include_dirs],
        str(paths.source),
        str(paths.native_runtime_source),
        "-lm",
        "-o",
        str(native_program),
    ]
    native_compile = run_capture(native_compile_argv, paths.workspace)
    native_compile_record = write_phase(context.native_dir, "compile", native_compile)
    context.records.setdefault("native", {})["compile"] = native_compile_record
    if native_compile.spawn_error is not None:
        return finish(context, "HARNESS_ERROR", "could not start native compiler")
    if native_compile.returncode != 0:
        return finish(context, "NATIVE_FAILED", "native compilation returned a nonzero status")
    if not native_program.is_file():
        return finish(context, "HARNESS_ERROR", "native compiler returned success without creating program")

    native_child_report = context.native_dir / "child.result.json"
    native_run_command = timeout_argv(
        paths,
        context.timeout_seconds,
        child_reporter_argv(native_child_report, [str(native_program)]),
    )
    native_run = run_capture(native_run_command, paths.workspace)
    native_outcome = supervised_outcome(native_run, read_child_report(native_child_report))
    native_run_record = write_phase(
        context.native_dir, "run", native_run, outcome=native_outcome
    )
    context.records["native"]["run"] = native_run_record
    context.records["native"]["unix_process"] = native_outcome
    if native_outcome["kind"] == "timeout":
        return finish(context, "NATIVE_TIMEOUT", "native program exceeded the wall-clock timeout")
    if native_outcome["kind"] == "signal":
        return finish(context, "NATIVE_SIGNAL", "native program terminated by a signal")
    if native_outcome["kind"] == "spawn_error":
        return finish(context, "HARNESS_ERROR", "could not start native program under GNU timeout")
    if native_outcome["kind"] != "normal_exit":
        return finish(context, "HARNESS_ERROR", "native process supervision did not yield a normal child result")

    generated_program = context.generated_dir / "Program.lean"
    clightgen_argv = [
        str(paths.clightgen),
        "-clight",
        "-lean",
        *[f"-I{include_dir}" for include_dir in paths.include_dirs],
        "-o",
        str(generated_program),
        str(paths.source),
    ]
    clightgen = run_capture(clightgen_argv, paths.workspace)
    clightgen_record = write_phase(context.lean_dir, "clightgen", clightgen)
    context.records.setdefault("lean", {})["clightgen"] = clightgen_record
    artifact_program = context.lean_dir / "Program.lean"
    if clightgen.spawn_error is not None:
        return finish(context, "HARNESS_ERROR", "could not start clightgen")
    if clightgen.returncode != 0:
        return finish(context, "CLIGHTGEN_FAILED", "clightgen returned a nonzero status")
    if not generated_program.is_file():
        return finish(context, "HARNESS_ERROR", "clightgen returned success without Program.lean")

    # CompCert's Lean backend currently leaves the language parameter of
    # `globvar _` unresolved.  Make that backend omission explicit before Lean
    # consumes an exported program; source-input callers retain their original
    # behavior apart from this parser-level repair.
    try:
        generated_text = generated_program.read_text(encoding="utf-8")
    except OSError as error:
        return finish(context, "HARNESS_ERROR", f"could not read generated Program.lean: {error}")
    unresolved_globvar_count = generated_text.count("globvar _ :=")
    if unresolved_globvar_count:
        generated_program.write_text(
            generated_text.replace("globvar _ :=", "globvar type :="),
            encoding="utf-8",
            newline="\n",
        )
    context.metadata["clightgen_postprocess"] = {
        "globvar_placeholder_replacements": unresolved_globvar_count,
        "replacement": "globvar type :=",
    }
    shutil.copyfile(generated_program, artifact_program)

    module_name = generated_module_name(context.run_id, context.case_id)
    case_main = context.generated_dir / "CaseMain.lean"
    case_main.write_text(case_main_source(module_name), encoding="utf-8", newline="\n")
    shutil.copyfile(case_main, context.lean_dir / "CaseMain.lean")
    context.metadata["generated_module"] = module_name
    write_json(context.artifact_dir / "metadata.json", context.metadata)

    case_main_relative = Path("GeneratedCases") / context.run_id / context.case_id / "CaseMain.lean"
    # The main package has no GeneratedCases library stanza.  The isolated case
    # package supplies it, so Lake must receive the module target (not a source
    # path target, which Lake resolves only against the main package's sources).
    case_main_module = f"GeneratedCases.{context.run_id}.{context.case_id}.CaseMain"
    build_argv = [str(paths.lake), "build", f"+{case_main_module}"]
    build = run_capture(build_argv, context.case_build_dir)
    build_record = write_phase(context.lean_dir, "build", build)
    context.records["lean"]["build"] = build_record
    if build.spawn_error is not None:
        return finish(context, "HARNESS_ERROR", "could not start lake build")
    if build.returncode != 0:
        return finish(context, "LEAN_BUILD_FAILED", "lake build returned a nonzero status")

    lean_run_base = [str(paths.lake), "env", "lean", "--run", str(case_main_relative)]
    lean_child_report = context.lean_dir / "child.result.json"
    lean_run = run_capture(
        timeout_argv(
            paths,
            context.timeout_seconds,
            child_reporter_argv(lean_child_report, lean_run_base),
        ),
        context.case_build_dir,
    )
    lean_outcome = supervised_outcome(lean_run, read_child_report(lean_child_report))
    lean_run_record = write_phase(context.lean_dir, "run", lean_run, outcome=lean_outcome)
    context.records["lean"]["run"] = lean_run_record
    context.records["lean"]["host_process"] = lean_outcome
    if lean_outcome["kind"] == "timeout":
        return finish(context, "LEAN_TIMEOUT", "Lean case runner exceeded the wall-clock timeout")
    if lean_outcome["kind"] == "signal":
        return finish(context, "LEAN_RUN_FAILED", "Lean case runner terminated by a signal")
    if lean_outcome["kind"] == "spawn_error":
        return finish(context, "HARNESS_ERROR", "could not start Lean case runner under GNU timeout")
    if lean_outcome["kind"] != "normal_exit":
        return finish(context, "HARNESS_ERROR", "Lean process supervision did not yield a normal child result")

    try:
        envelope = parse_envelope(lean_run.stdout)
    except EnvelopeError as error:
        write_json(
            context.lean_dir / "runner-envelope.json",
            {"valid": False, "error": str(error)},
        )
        return finish(context, "LEAN_ENVELOPE_INVALID", str(error))
    semantic_error = validate_envelope_semantics(envelope)
    if semantic_error is not None:
        write_json(
            context.lean_dir / "runner-envelope.json",
            {"valid": False, "error": semantic_error, "envelope": envelope.as_json()},
        )
        return finish(context, "LEAN_ENVELOPE_INVALID", semantic_error)
    write_json(context.lean_dir / "runner-envelope.json", {"valid": True, "envelope": envelope.as_json()})
    context.records["lean"]["envelope"] = envelope.as_json()

    if envelope.status == "unsupported":
        return finish(context, "LEAN_UNSUPPORTED", "executor reported an unsupported feature or external")
    if envelope.status == "stuck":
        return finish(context, "LEAN_STUCK", "executor reported a concrete stuck outcome")
    if envelope.status != "completed":
        return finish(context, "LEAN_RUN_FAILED", f"unexpected Lean runner status: {envelope.status}")
    if lean_outcome["exit_code"] != 0:
        return finish(
            context,
            "LEAN_RUN_FAILED",
            "completed Lean envelope was accompanied by a nonzero host process exit",
        )

    comparison = {
        "native_stdout_bytes": len(native_run.stdout),
        "native_stdout_sha256": sha256_bytes(native_run.stdout),
        "lean_modeled_stdout_bytes": len(envelope.stdout),
        "lean_modeled_stdout_sha256": sha256_bytes(envelope.stdout),
        "native_unix_exit_code": native_outcome["exit_code"],
        "lean_c_main_exit": envelope.c_exit,
        "c_main_exit_compared": False,
        "stdout_equal": native_run.stdout == envelope.stdout,
    }
    context.records["comparison"] = comparison
    if native_run.stdout != envelope.stdout:
        return finish(context, "OUTPUT_MISMATCH", "native stdout and Lean modeled stdout differ")
    return finish(context, "PASS", "native and Lean completed with byte-identical stdout")


def run_self_test_envelope() -> dict[str, Any]:
    valid_non_utf8 = (
        b"CLIGHT_LEAN_RUNNER_V1 status=completed steps=12 exit=-7 "
        b"error_code=- stdout_hex=fF80\n"
    )
    parsed = parse_envelope(valid_non_utf8)
    if parsed.status != "completed" or parsed.steps != 12 or parsed.c_exit != "-7":
        raise AssertionError("valid envelope fields did not round-trip")
    if parsed.stdout != b"\xff\x80":
        raise AssertionError("non-UTF-8 modeled stdout did not decode exactly")
    empty = parse_envelope(
        b"CLIGHT_LEAN_RUNNER_V1 status=unsupported steps=0 exit=- "
        b"error_code=unsupported_external stdout_hex=\n"
    )
    if empty.stdout != b"":
        raise AssertionError("empty stdout_hex did not decode to empty bytes")
    malformed = [
        b"",
        b"CLIGHT_LEAN_RUNNER_V1 status=completed steps=1 exit=0 stdout_hex=00 error_code=-",
        b"CLIGHT_LEAN_RUNNER_V1 status=completed steps=1 exit=0 error_code=- stdout_hex=0",
        b"CLIGHT_LEAN_RUNNER_V1 status=completed steps=1 exit=0 error_code=- stdout_hex=0g",
        b"CLIGHT_LEAN_RUNNER_V1 status=completed steps=1 exit=0 error_code=- stdout_hex=00",
        valid_non_utf8 + b"extra\n",
        b"CLIGHT_LEAN_RUNNER_V1 status=completed steps=1 exit=0 error_code=- stdout_hex=00\r\n",
    ]
    for candidate in malformed:
        try:
            parse_envelope(candidate)
        except EnvelopeError:
            continue
        raise AssertionError(f"malformed envelope was accepted: {candidate!r}")
    return {"verdict": "PASS", "self_test": "envelope", "cases": 2 + len(malformed)}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run one explicit C source through the Phase 0 checksum differential harness."
    )
    parser.add_argument("--source", metavar="PATH", help="C source input (required except for self-test)")
    parser.add_argument("--run-id", help="safe Lean-identifier run name; default is timestamp plus PID")
    parser.add_argument("--case-id", default="case000001", help="safe Lean-identifier case name")
    parser.add_argument("--timeout-seconds", default="30", help="positive wall-clock limit for native and Lean runs")
    parser.add_argument("--compcert-root", help="CompCert checkout; defaults from tools/csmith-diff-phase0.json")
    parser.add_argument("--csmith-root", help="CSmith checkout; validated but not executed in this source-only phase")
    parser.add_argument(
        "--native-runtime-source",
        help="native checksum companion source; default is Test/CSmithSeeds/csmith_checksum_runtime.c",
    )
    parser.add_argument(
        "--include-dir",
        action="append",
        metavar="PATH",
        help=(
            "C include directory; may be repeated in preprocessing order; "
            "default is Test/CSmithSeeds"
        ),
    )
    parser.add_argument(
        "--self-test-envelope",
        action="store_true",
        help="run pure envelope parsing checks without external tools or --source",
    )
    parser.add_argument(
        "--_record-child-result",
        metavar="PATH",
        help=argparse.SUPPRESS,
    )
    parser.add_argument("child_argv", nargs=argparse.REMAINDER, help=argparse.SUPPRESS)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args._record_child_result is not None:
        return run_child_reporter(absolute_cli_path(args._record_child_result), args.child_argv)
    if args.self_test_envelope:
        try:
            print(json.dumps(run_self_test_envelope(), sort_keys=True, separators=(",", ":")))
            return 0
        except Exception as error:  # pragma: no cover - assertion failure is diagnostic only
            print(
                json.dumps(
                    {"verdict": "HARNESS_ERROR", "self_test": "envelope", "error": str(error)},
                    sort_keys=True,
                    separators=(",", ":"),
                )
            )
            return 2

    context: CaseContext | None = None
    try:
        context = create_context(args)
        result = run_pipeline(context)
    except HarnessError as error:
        if context is None:
            print(
                json.dumps(
                    {"verdict": "HARNESS_ERROR", "artifact_dir": None, "error": str(error)},
                    sort_keys=True,
                    separators=(",", ":"),
                )
            )
            return 2
        write_bytes(context.artifact_dir / "harness-error.txt", traceback.format_exc().encode("utf-8"))
        result = finish(context, "HARNESS_ERROR", str(error))
    except Exception as error:  # Retain an unexpected exception in the case artifact.
        if context is None:
            print(
                json.dumps(
                    {
                        "verdict": "HARNESS_ERROR",
                        "artifact_dir": None,
                        "error": f"{type(error).__name__}: {error}",
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                )
            )
            return 2
        write_bytes(context.artifact_dir / "harness-error.txt", traceback.format_exc().encode("utf-8"))
        result = finish(context, "HARNESS_ERROR", f"{type(error).__name__}: {error}")

    summary = {
        "verdict": result["verdict"],
        "artifact_dir": str(context.artifact_dir),
        "run_id": context.run_id,
        "case_id": context.case_id,
    }
    print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
    return 0 if result["verdict"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())

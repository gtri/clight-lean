#!/usr/bin/env python3
"""Generate and run a sequential deterministic CSmith checksum corpus."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Any, Sequence


SCRIPT_PATH = Path(__file__).resolve()
WORKSPACE = SCRIPT_PATH.parent.parent
HARNESS_PATH = SCRIPT_PATH.with_name("csmith_diff.py")
DEFAULT_PROFILE_PATH = SCRIPT_PATH.with_name("csmith-profile-fixed-checksum.json")
PHASE0_CONFIG_PATH = SCRIPT_PATH.with_name("csmith-diff-phase0.json")
SAFE_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
DIRECT_PRINTF_RE = re.compile(r"\bprintf\s*\(")
UNION_FUNCTION_RETURN_RE = re.compile(
    r"(?m)^\s*(?:static\s+)?(?:const\s+)?union\s+[A-Za-z_]\w*\s+"
    r"(?:\*\s*)?[A-Za-z_]\w*\s*\("
)
UNION_FUNCTION_PARAMETER_RE = re.compile(
    r"\([^;{}()]*\bunion\s+[A-Za-z_]\w*\s+(?:\*\s*)?[A-Za-z_]\w*"
)

REQUIRED_INCLUDE = '#include "csmith.h"'
INJECTED_INCLUDE = '#include "csmith_checksum_runtime.h"'
FINAL_CHECKSUM_CALL = "platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);"
REPLACEMENT_CHECKSUM_CALL = (
    "csmith_checksum_print((unsigned int)(crc32_context ^ 0xFFFFFFFFUL));"
)
EXPECTED_PROFILE_ARGV = [
    "--float",
    "--strict-float",
    "--no-volatiles",
    "--no-bitfields",
    "--no-builtins",
    "--no-argc",
    "--max-struct-fields",
    "6",
    "--no-packed-struct",
    "--no-arg-structs",
    "--no-return-structs",
    "--max-union-fields",
    "3",
    "--no-arg-unions",
    "--no-return-unions",
    "--take-no-union-field-addr",
    "--max-pointer-depth",
    "3",
    "--no-volatile-pointers",
    "--no-const-pointers",
    "--max-array-dim",
    "3",
    "--max-array-len-per-dim",
    "4",
    "--max-funcs",
    "3",
    "--max-block-depth",
    "3",
    "--max-block-size",
    "3",
    "--max-expr-complexity",
    "5",
    "--checksum",
    "--no-hash-value-printf",
    "--concise",
]
EXPECTED_TRANSFORM_CONTRACT = {
    "required_include": REQUIRED_INCLUDE,
    "required_include_count": 1,
    "injected_include": INJECTED_INCLUDE,
    "final_checksum_call": FINAL_CHECKSUM_CALL,
    "final_checksum_call_count": 1,
    "replacement_call": REPLACEMENT_CHECKSUM_CALL,
    "forbid_direct_generated_printf": True,
    "reject_union_abi_functions": True,
}
MAX_CSMITH_SEED = (1 << 64) - 1


class CorpusError(RuntimeError):
    """A validation or retained-corpus policy error."""


class TransformError(ValueError):
    """The generated source violates the checksum transformation contract."""


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


def absolute_cli_path(value: str) -> Path:
    return Path(value).expanduser().resolve()


def workspace_relative_path(value: str) -> Path:
    return (WORKSPACE / value).resolve()


def require_file(path: Path, description: str, executable: bool = False) -> None:
    if not path.is_file():
        raise CorpusError(f"{description} is not a file: {path}")
    if executable and not os.access(path, os.X_OK):
        raise CorpusError(f"{description} is not executable: {path}")


def require_dir(path: Path, description: str) -> None:
    if not path.is_dir():
        raise CorpusError(f"{description} is not a directory: {path}")


def require_under(path: Path, root: Path, description: str) -> None:
    try:
        path.relative_to(root)
    except ValueError as error:
        raise CorpusError(f"{description} escapes its allowed root {root}: {path}") from error


def require_safe_id(value: str, option: str) -> str:
    if not SAFE_ID_RE.fullmatch(value):
        raise CorpusError(
            f"{option} must be a nonempty Lean module identifier "
            f"([A-Za-z][A-Za-z0-9_]*): {value!r}"
        )
    return value


def parse_positive_count(value: str) -> int:
    try:
        count = int(value, 10)
    except ValueError as error:
        raise argparse.ArgumentTypeError("--count must be a positive integer") from error
    if count <= 0:
        raise argparse.ArgumentTypeError("--count must be a positive integer")
    return count


def parse_seed_start(value: str) -> int:
    try:
        seed = int(value, 10)
    except ValueError as error:
        raise argparse.ArgumentTypeError("--seed-start must be a nonnegative integer") from error
    if seed < 0 or seed > MAX_CSMITH_SEED:
        raise argparse.ArgumentTypeError("--seed-start is outside CSmith's unsigned-long range")
    return seed


def parse_timeout_seconds(value: str) -> float:
    try:
        seconds = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("--timeout-seconds must be a finite positive number") from error
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("--timeout-seconds must be a finite positive number")
    return seconds


def format_timeout_seconds(seconds: float) -> str:
    return f"{seconds:g}"


def default_run_id() -> str:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"run{stamp}_pid{os.getpid()}"


def write_json_new(path: Path, value: Any) -> None:
    try:
        with path.open("x", encoding="utf-8", newline="\n") as handle:
            json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=True)
            handle.write("\n")
    except FileExistsError as error:
        raise CorpusError(f"refusing to overwrite existing file: {path}") from error


def write_bytes_new(path: Path, value: bytes) -> None:
    try:
        with path.open("xb") as handle:
            handle.write(value)
    except FileExistsError as error:
        raise CorpusError(f"refusing to overwrite existing file: {path}") from error


def replace_json_atomically(path: Path, value: Any) -> None:
    """Replace the single mutable run index without touching case artifacts."""
    temporary = path.with_name(path.name + ".tmp")
    if temporary.exists():
        raise CorpusError(f"refusing to overwrite stale corpus update file: {temporary}")
    try:
        with temporary.open("x", encoding="utf-8", newline="\n") as handle:
            json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except Exception:
        if temporary.exists():
            try:
                temporary.unlink()
            except OSError:
                pass
        raise


def load_json(path: Path, description: str) -> dict[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, json.JSONDecodeError) as error:
        raise CorpusError(f"could not read {description} {path}: {error}") from error
    if not isinstance(value, dict):
        raise CorpusError(f"{description} must contain a JSON object: {path}")
    return value


def load_profile(path: Path) -> tuple[dict[str, Any], str]:
    require_file(path, "CSmith profile")
    profile = load_json(path, "CSmith profile")
    expected_keys = {"schema_version", "profile", "generator_argv", "transform_contract"}
    if set(profile) != expected_keys or profile.get("schema_version") != 1:
        raise CorpusError(f"unsupported CSmith profile schema in {path}")
    if profile.get("profile") != "fixed-checksum-floats-v1":
        raise CorpusError(f"unexpected CSmith profile name in {path}")
    argv = profile.get("generator_argv")
    if not isinstance(argv, list) or not all(isinstance(option, str) for option in argv):
        raise CorpusError(f"CSmith profile generator_argv must be an array of strings: {path}")
    if argv != EXPECTED_PROFILE_ARGV:
        raise CorpusError(
            "CSmith profile options do not exactly match the confirmed restricted profile: "
            f"{path}"
        )
    if profile.get("transform_contract") != EXPECTED_TRANSFORM_CONTRACT:
        raise CorpusError(f"CSmith profile transform contract is not the fixed checksum contract: {path}")
    return profile, sha256_file(path)


def validate_ignored_policy() -> None:
    policy_path = WORKSPACE / ".gitignore"
    require_file(policy_path, "ignored-path policy")
    try:
        entries = set(policy_path.read_text(encoding="utf-8").splitlines())
    except OSError as error:
        raise CorpusError(f"could not read ignored-path policy {policy_path}: {error}") from error
    for entry in ("/GeneratedCases/", "/.csmith-diff-build/", "/artifacts/csmith/"):
        if entry not in entries:
            raise CorpusError(f"ignored-path policy does not contain required entry {entry}")


def load_phase0_layout() -> dict[str, str]:
    config = load_json(PHASE0_CONFIG_PATH, "Phase 0 configuration")
    if config.get("schema_version") != 1 or not isinstance(config.get("workspace_layout"), dict):
        raise CorpusError(f"unsupported Phase 0 configuration schema in {PHASE0_CONFIG_PATH}")
    layout = config["workspace_layout"]
    expected = {
        "generated_case_modules": "GeneratedCases",
        "case_build_output": ".csmith-diff-build",
        "retained_artifacts": "artifacts/csmith",
    }
    if {key: layout.get(key) for key in expected} != expected:
        raise CorpusError("Phase 0 configuration does not declare the restricted output roots")
    return expected


def process_record(argv: Sequence[str], cwd: Path, timeout_seconds: float | None = None) -> dict[str, Any]:
    started_at = utc_now()
    started = time.monotonic()
    record: dict[str, Any] = {
        "argv": [str(item) for item in argv],
        "cwd": str(cwd),
        "started_at": started_at,
    }
    try:
        completed = subprocess.run(
            list(argv),
            cwd=str(cwd),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=timeout_seconds,
        )
        stdout = completed.stdout
        stderr = completed.stderr
        record["returncode"] = completed.returncode
        record["outcome"] = "normal_exit"
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout or b""
        stderr = error.stderr or b""
        record["returncode"] = None
        record["outcome"] = "timeout"
        record["timeout_seconds"] = timeout_seconds
    except OSError as error:
        stdout = b""
        stderr = b""
        record["returncode"] = None
        record["outcome"] = "spawn_error"
        record["spawn_error"] = f"{type(error).__name__}: {error}"
    record["finished_at"] = utc_now()
    record["duration_seconds"] = round(time.monotonic() - started, 6)
    record["stdout_bytes"] = len(stdout)
    record["stdout_sha256"] = sha256_bytes(stdout)
    record["stderr_bytes"] = len(stderr)
    record["stderr_sha256"] = sha256_bytes(stderr)
    record["_stdout"] = stdout
    record["_stderr"] = stderr
    return record


def stored_process_record(record: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in record.items() if key not in {"_stdout", "_stderr"}}


def probe_csmith_version(csmith_bin: Path) -> dict[str, Any]:
    record = process_record([str(csmith_bin), "--version"], WORKSPACE)
    if record["outcome"] != "normal_exit" or record["returncode"] != 0:
        raise CorpusError(f"could not obtain a successful CSmith --version from {csmith_bin}")
    result = stored_process_record(record)
    result["stdout_text"] = record["_stdout"].decode("utf-8", errors="replace")
    result["stderr_text"] = record["_stderr"].decode("utf-8", errors="replace")
    return result


def transform_source(raw: str) -> tuple[str, dict[str, int]]:
    """Apply only the narrow fixed-checksum source transformation."""
    lines = raw.splitlines(keepends=True)
    include_lines = [
        index
        for index, line in enumerate(lines)
        if line.rstrip("\r\n").strip() == REQUIRED_INCLUDE
    ]
    checksum_call_count = raw.count(FINAL_CHECKSUM_CALL)
    direct_printf_count = len(DIRECT_PRINTF_RE.findall(raw))
    union_function_return_count = len(UNION_FUNCTION_RETURN_RE.findall(raw))
    union_function_parameter_count = len(UNION_FUNCTION_PARAMETER_RE.findall(raw))
    counts = {
        "csmith_include": len(include_lines),
        "platform_main_end_checksum_call": checksum_call_count,
        "direct_printf": direct_printf_count,
        "union_function_returns": union_function_return_count,
        "union_function_parameters": union_function_parameter_count,
    }
    if len(include_lines) != 1:
        raise TransformError(
            f"expected exactly one {REQUIRED_INCLUDE!r} line; found {len(include_lines)}"
        )
    if checksum_call_count != 1:
        raise TransformError(
            f"expected exactly one final checksum call; found {checksum_call_count}"
        )
    if direct_printf_count != 0:
        raise TransformError(f"generated source contains {direct_printf_count} direct printf call(s)")
    if union_function_return_count != 0 or union_function_parameter_count != 0:
        raise TransformError(
            "generated source uses union-valued function return(s) or parameter(s); "
            "the pinned CompCert target requires unsupported -fstruct-passing"
        )
    if INJECTED_INCLUDE in raw:
        raise TransformError("generated source already contains the checksum helper include")

    include_index = include_lines[0]
    line_ending = "\r\n" if lines[include_index].endswith("\r\n") else "\n"
    lines.insert(include_index + 1, INJECTED_INCLUDE + line_ending)
    transformed = "".join(lines).replace(
        FINAL_CHECKSUM_CALL, REPLACEMENT_CHECKSUM_CALL, 1
    )
    if transformed.count(INJECTED_INCLUDE) != 1:
        raise TransformError("transformed source does not contain exactly one checksum helper include")
    if transformed.count(REPLACEMENT_CHECKSUM_CALL) != 1:
        raise TransformError("transformed source does not contain exactly one replacement checksum call")
    if FINAL_CHECKSUM_CALL in transformed:
        raise TransformError("transformed source retains the platform_main_end checksum call")
    if DIRECT_PRINTF_RE.search(transformed):
        raise TransformError("transformed source contains a direct printf call")
    return transformed, counts


def transform_raw_bytes(raw: bytes) -> tuple[bytes, dict[str, int]]:
    try:
        raw_text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise TransformError(f"generated source is not UTF-8: {error}") from error
    transformed_text, counts = transform_source(raw_text)
    return transformed_text.encode("utf-8"), counts


def run_self_test_transform() -> dict[str, Any]:
    valid = (
        "// artificial source\n"
        '#include "csmith.h"\n'
        "int main(void) {\n"
        "  platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);\n"
        "  return 0;\n"
        "}\n"
    )
    transformed, counts = transform_source(valid)
    if counts != {
        "csmith_include": 1,
        "platform_main_end_checksum_call": 1,
        "direct_printf": 0,
        "union_function_returns": 0,
        "union_function_parameters": 0,
    }:
        raise AssertionError("valid source counts did not match the transformation contract")
    expected_prefix = REQUIRED_INCLUDE + "\n" + INJECTED_INCLUDE + "\n"
    if expected_prefix not in transformed or REPLACEMENT_CHECKSUM_CALL not in transformed:
        raise AssertionError("valid source did not receive the exact include and replacement")
    rejected = {
        "multiple_include": valid.replace(REQUIRED_INCLUDE, REQUIRED_INCLUDE + "\n" + REQUIRED_INCLUDE),
        "missing_include": valid.replace(REQUIRED_INCLUDE + "\n", ""),
        "multiple_final_call": valid.replace(
            FINAL_CHECKSUM_CALL, FINAL_CHECKSUM_CALL + "\n  " + FINAL_CHECKSUM_CALL
        ),
        "missing_final_call": valid.replace(FINAL_CHECKSUM_CALL, "return 0;"),
        "direct_printf": valid.replace("  return 0;", '  printf("not admitted");'),
        "union_function_return": valid.replace(
            "int main(void) {",
            "union cell { unsigned value; };\nunion cell helper(void);\n"
            "int main(void) {",
        ),
        "union_function_parameter": valid.replace(
            "int main(void) {",
            "union cell { unsigned value; };\nint helper(union cell value);\n"
            "int main(void) {",
        ),
    }
    for label, source in rejected.items():
        try:
            transform_source(source)
        except TransformError:
            continue
        raise AssertionError(f"transformer accepted invalid artificial source: {label}")
    return {"verdict": "PASS", "self_test": "transform", "cases": 1 + len(rejected)}


def case_id_for_seed(seed: int) -> str:
    return f"case{seed:06d}"


def terminal_case_ids(corpus: dict[str, Any]) -> set[str]:
    cases = corpus.get("cases")
    if not isinstance(cases, list):
        raise CorpusError("corpus.json cases must be an array")
    identifiers: set[str] = set()
    terminal: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or not isinstance(case.get("case_id"), str):
            raise CorpusError("corpus.json contains an invalid case record")
        case_id = case["case_id"]
        if case_id in identifiers:
            raise CorpusError(f"corpus.json records duplicate case ID: {case_id}")
        identifiers.add(case_id)
        if case.get("terminal") is True:
            if not isinstance(case.get("verdict"), str):
                raise CorpusError(f"terminal corpus case has no verdict: {case_id}")
            terminal.add(case_id)
    return terminal


def update_corpus_summary(corpus: dict[str, Any]) -> None:
    counts: dict[str, int] = {}
    attempted = 0
    for case in corpus["cases"]:
        if case.get("terminal") is True:
            attempted += 1
            verdict = case["verdict"]
            counts[verdict] = counts.get(verdict, 0) + 1
    corpus["counts_by_verdict"] = dict(sorted(counts.items()))
    corpus["attempted_cases"] = attempted
    corpus["updated_at"] = utc_now()


def append_invocation(corpus: dict[str, Any], argv: Sequence[str]) -> None:
    invocation = {"at": utc_now(), "argv": [str(value) for value in argv]}
    invocations = corpus.setdefault("invocations", [])
    if not isinstance(invocations, list):
        raise CorpusError("corpus.json invocations must be an array")
    invocations.append(invocation)
    corpus["cli_argv"] = invocation["argv"]


def parse_harness_summary(record: dict[str, Any]) -> tuple[str, dict[str, Any] | None, str | None]:
    if record["outcome"] != "normal_exit":
        return "HARNESS_ERROR", None, "could not execute source harness"
    try:
        lines = record["_stdout"].decode("utf-8").splitlines()
    except UnicodeDecodeError:
        return "HARNESS_ERROR", None, "source harness summary is not UTF-8 JSON"
    if len(lines) != 1:
        return "HARNESS_ERROR", None, "source harness did not emit exactly one JSON summary line"
    try:
        summary = json.loads(lines[0])
    except json.JSONDecodeError:
        return "HARNESS_ERROR", None, "source harness summary is not JSON"
    if not isinstance(summary, dict) or not isinstance(summary.get("verdict"), str):
        return "HARNESS_ERROR", None, "source harness summary has no string verdict"
    if summary["verdict"] == "PASS" and record["returncode"] != 0:
        return "HARNESS_ERROR", summary, "source harness reported PASS with a nonzero exit"
    return summary["verdict"], summary, None


def source_paths(run_root: Path, case_id: str) -> dict[str, Path]:
    generated_root = run_root / "generated"
    return {
        "raw": generated_root / f"{case_id}.raw.c",
        "transformed": generated_root / f"{case_id}.c",
        "transform_record": generated_root / f"{case_id}.transform.json",
        "generator_record": generated_root / f"{case_id}.generator.json",
        "generator_stdout": generated_root / f"{case_id}.generator.stdout",
        "generator_stderr": generated_root / f"{case_id}.generator.stderr",
        "harness_record": generated_root / f"{case_id}.harness.json",
        "harness_stdout": generated_root / f"{case_id}.harness.stdout",
        "harness_stderr": generated_root / f"{case_id}.harness.stderr",
    }


def case_has_existing_artifacts(
    paths: dict[str, Path], run_root: Path, generated_modules_root: Path, build_root: Path, case_id: str
) -> bool:
    candidates = [*paths.values(), run_root / case_id, generated_modules_root / case_id, build_root / case_id]
    return any(path.exists() for path in candidates)


def append_case_and_persist(corpus: dict[str, Any], corpus_path: Path, case: dict[str, Any]) -> None:
    corpus["cases"].append(case)
    update_corpus_summary(corpus)
    replace_json_atomically(corpus_path, corpus)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate sequential fixed-checksum CSmith cases and run the source harness."
    )
    parser.add_argument("--csmith-bin", metavar="PATH", help="required CSmith executable")
    parser.add_argument(
        "--csmith-runtime-include",
        metavar="PATH",
        help="required directory containing csmith.h and generated safe_math.h",
    )
    parser.add_argument("--count", type=parse_positive_count, help="required positive number of seeds")
    parser.add_argument("--seed-start", type=parse_seed_start, default=1, help="first seed (default: 1)")
    parser.add_argument("--run-id", help="safe run identifier; default is timestamp plus PID")
    parser.add_argument("--profile", metavar="PATH", default=str(DEFAULT_PROFILE_PATH))
    parser.add_argument("--timeout-seconds", type=parse_timeout_seconds, default=30.0)
    parser.add_argument("--compcert-root", metavar="PATH", help="forwarded to tools/csmith_diff.py")
    parser.add_argument("--csmith-root", metavar="PATH", help="forwarded to tools/csmith_diff.py")
    parser.add_argument(
        "--include-dir",
        metavar="PATH",
        help="owned checksum include directory (default: Test/CSmithSeeds)",
    )
    parser.add_argument(
        "--native-runtime-source",
        metavar="PATH",
        help="native checksum companion (default: Test/CSmithSeeds/csmith_checksum_runtime.c)",
    )
    parser.add_argument("--resume", action="store_true", help="resume a retained corpus run")
    parser.add_argument("--fail-fast", action="store_true", help="stop after the first non-PASS case")
    parser.add_argument(
        "--self-test-transform",
        action="store_true",
        help="run pure source-transform checks without external tools",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.self_test_transform:
        try:
            print(json.dumps(run_self_test_transform(), sort_keys=True, separators=(",", ":")))
            return 0
        except Exception as error:  # pragma: no cover - diagnostic path only
            print(
                json.dumps(
                    {"verdict": "HARNESS_ERROR", "self_test": "transform", "error": str(error)},
                    sort_keys=True,
                    separators=(",", ":"),
                )
            )
            return 2

    try:
        if args.csmith_bin is None or args.csmith_runtime_include is None or args.count is None:
            raise CorpusError(
                "--csmith-bin PATH, --csmith-runtime-include PATH, and --count N are required"
            )
        if args.seed_start + args.count - 1 > MAX_CSMITH_SEED:
            raise CorpusError("seed range exceeds CSmith's unsigned-long range")
        require_dir(WORKSPACE, "workspace root")
        require_file(HARNESS_PATH, "committed source harness")
        validate_ignored_policy()
        layout = load_phase0_layout()
        profile_path = absolute_cli_path(args.profile)
        profile, profile_hash = load_profile(profile_path)
        csmith_bin = absolute_cli_path(args.csmith_bin)
        require_file(csmith_bin, "CSmith binary", executable=True)
        csmith_version = probe_csmith_version(csmith_bin)
        runtime_include = absolute_cli_path(args.csmith_runtime_include)
        require_dir(runtime_include, "CSmith runtime include directory")
        require_file(runtime_include / "csmith.h", "CSmith runtime include csmith.h")
        require_file(runtime_include / "safe_math.h", "CSmith runtime include generated safe_math.h")
        owned_include = (
            absolute_cli_path(args.include_dir)
            if args.include_dir is not None
            else workspace_relative_path("Test/CSmithSeeds")
        )
        native_runtime_source = (
            absolute_cli_path(args.native_runtime_source)
            if args.native_runtime_source is not None
            else workspace_relative_path("Test/CSmithSeeds/csmith_checksum_runtime.c")
        )
        require_dir(owned_include, "owned checksum include directory")
        require_file(
            owned_include / "csmith_checksum_runtime.h", "owned checksum declaration header"
        )
        require_file(native_runtime_source, "native checksum companion runtime")
        run_id = require_safe_id(args.run_id or default_run_id(), "--run-id")

        workspace = WORKSPACE.resolve()
        artifact_root = workspace_relative_path(layout["retained_artifacts"])
        generated_modules_root = workspace_relative_path(layout["generated_case_modules"])
        build_root = workspace_relative_path(layout["case_build_output"])
        run_root = (artifact_root / run_id).resolve()
        source_root = (run_root / "generated").resolve()
        harness_generated_run_root = (generated_modules_root / run_id).resolve()
        harness_build_run_root = (build_root / run_id).resolve()
        for path, root, description in (
            (artifact_root, workspace, "artifact root"),
            (generated_modules_root, workspace, "generated module root"),
            (build_root, workspace, "case build root"),
            (run_root, artifact_root, "corpus run root"),
            (source_root, run_root, "corpus generated-source root"),
            (harness_generated_run_root, generated_modules_root, "harness generated run root"),
            (harness_build_run_root, build_root, "harness build run root"),
        ):
            require_under(path, root, description)
        # The committed ignored policy authorizes these exact output roots.  The
        # corpus owns artifacts/csmith; the source harness creates its run
        # children under the other two roots only after its own no-overwrite
        # checks.
        require_dir(artifact_root.parent, "artifact root parent")
        require_dir(generated_modules_root.parent, "generated module root parent")
        require_dir(build_root.parent, "case build root parent")
        artifact_root.mkdir(exist_ok=True)
        require_dir(artifact_root, "artifact root")
        corpus_path = run_root / "corpus.json"

        include_dirs = [owned_include, runtime_include]
        invocation_argv = list(sys.argv if argv is None else [str(value) for value in argv])
        if args.resume:
            if not run_root.is_dir() or not corpus_path.is_file() or not source_root.is_dir():
                raise CorpusError("--resume requires an existing corpus run with corpus.json and generated/")
            corpus = load_json(corpus_path, "corpus index")
            if corpus.get("schema_version") != 1 or corpus.get("run_id") != run_id:
                raise CorpusError("corpus.json does not describe the requested schema-version-1 run")
            recorded_profile = corpus.get("profile")
            if not isinstance(recorded_profile, dict) or recorded_profile.get("sha256") != profile_hash:
                raise CorpusError("--resume profile hash differs from the retained corpus run")
            terminal_ids = terminal_case_ids(corpus)
            append_invocation(corpus, invocation_argv)
            update_corpus_summary(corpus)
            replace_json_atomically(corpus_path, corpus)
        else:
            if run_root.exists():
                raise CorpusError(f"refusing to overwrite existing corpus run directory: {run_root}")
            if harness_generated_run_root.exists() or harness_build_run_root.exists():
                raise CorpusError(
                    "refusing to reuse run ID with existing generated-module or build artifacts"
                )
            run_root.mkdir(parents=True, exist_ok=False)
            source_root.mkdir(exist_ok=False)
            started_at = utc_now()
            corpus = {
                "schema_version": 1,
                "run_id": run_id,
                "started_at": started_at,
                "updated_at": started_at,
                "profile": {
                    "path": str(profile_path),
                    "sha256": profile_hash,
                    "content": profile,
                },
                "csmith": {"binary": str(csmith_bin), "version": csmith_version},
                "paths": {
                    "run_root": str(run_root),
                    "source_root": str(source_root),
                    "owned_include_dir": str(owned_include),
                    "csmith_runtime_include_dir": str(runtime_include),
                    "include_dirs": [str(directory) for directory in include_dirs],
                    "native_runtime_source": str(native_runtime_source),
                    "harness": str(HARNESS_PATH),
                },
                "initial_cli_argv": invocation_argv,
                "cli_argv": invocation_argv,
                "invocations": [{"at": started_at, "argv": invocation_argv}],
                "cases": [],
                "counts_by_verdict": {},
                "attempted_cases": 0,
            }
            write_json_new(corpus_path, corpus)
            terminal_ids = set()

        attempted_this_invocation = 0
        skipped_terminal = 0
        stopped_early = False
        for seed in range(args.seed_start, args.seed_start + args.count):
            case_id = case_id_for_seed(seed)
            if case_id in terminal_ids:
                skipped_terminal += 1
                continue
            paths = source_paths(run_root, case_id)
            if case_has_existing_artifacts(
                paths, run_root, harness_generated_run_root, harness_build_run_root, case_id
            ):
                case = {
                    "case_id": case_id,
                    "seed": seed,
                    "started_at": utc_now(),
                    "updated_at": utc_now(),
                    "terminal": True,
                    "verdict": "CORPUS_ERROR",
                    "reason": "refusing to overwrite pre-existing case source or harness artifact",
                    "artifact_dir": str(run_root / case_id),
                    "source_artifact_dir": str(source_root),
                    "harness_exit": None,
                }
                append_case_and_persist(corpus, corpus_path, case)
                terminal_ids.add(case_id)
                attempted_this_invocation += 1
                if args.fail_fast:
                    stopped_early = True
                    break
                continue

            case_started_at = utc_now()
            generator_argv = [
                str(csmith_bin),
                "--seed",
                str(seed),
                *profile["generator_argv"],
                "--output",
                str(paths["raw"]),
            ]
            generator = process_record(generator_argv, workspace, args.timeout_seconds)
            write_bytes_new(paths["generator_stdout"], generator["_stdout"])
            write_bytes_new(paths["generator_stderr"], generator["_stderr"])
            write_json_new(paths["generator_record"], stored_process_record(generator))
            case: dict[str, Any] = {
                "case_id": case_id,
                "seed": seed,
                "started_at": case_started_at,
                "updated_at": utc_now(),
                "terminal": True,
                "artifact_dir": str(run_root / case_id),
                "source_artifact_dir": str(source_root),
                "source": {"raw": str(paths["raw"]), "transformed": str(paths["transformed"])},
                "generator": stored_process_record(generator),
                "harness_exit": None,
            }
            if generator["outcome"] != "normal_exit" or generator["returncode"] != 0:
                case["verdict"] = "GENERATOR_FAILED"
                case["reason"] = "CSmith did not exit successfully"
            elif not paths["raw"].is_file():
                case["verdict"] = "GENERATOR_FAILED"
                case["reason"] = "CSmith exited successfully without creating the requested raw source"
            else:
                raw = paths["raw"].read_bytes()
                try:
                    transformed, transform_counts = transform_raw_bytes(raw)
                except TransformError as error:
                    case["verdict"] = "TRANSFORM_REJECTED"
                    case["reason"] = str(error)
                else:
                    write_bytes_new(paths["transformed"], transformed)
                    transform_record = {
                        "schema_version": 1,
                        "contract": EXPECTED_TRANSFORM_CONTRACT,
                        "raw": {
                            "path": str(paths["raw"]),
                            "bytes": len(raw),
                            "sha256": sha256_bytes(raw),
                        },
                        "transformed": {
                            "path": str(paths["transformed"]),
                            "bytes": len(transformed),
                            "sha256": sha256_bytes(transformed),
                        },
                        "counts": transform_counts,
                    }
                    write_json_new(paths["transform_record"], transform_record)
                    case["transform"] = transform_record
                    harness_argv = [
                        str(Path(sys.executable).resolve()),
                        str(HARNESS_PATH),
                        "--source",
                        str(paths["transformed"]),
                        "--run-id",
                        run_id,
                        "--case-id",
                        case_id,
                        "--timeout-seconds",
                        format_timeout_seconds(args.timeout_seconds),
                        "--native-runtime-source",
                        str(native_runtime_source),
                    ]
                    if args.compcert_root is not None:
                        harness_argv.extend(["--compcert-root", str(absolute_cli_path(args.compcert_root))])
                    if args.csmith_root is not None:
                        harness_argv.extend(["--csmith-root", str(absolute_cli_path(args.csmith_root))])
                    for include_dir in include_dirs:
                        harness_argv.extend(["--include-dir", str(include_dir)])
                    harness = process_record(harness_argv, workspace)
                    write_bytes_new(paths["harness_stdout"], harness["_stdout"])
                    write_bytes_new(paths["harness_stderr"], harness["_stderr"])
                    write_json_new(paths["harness_record"], stored_process_record(harness))
                    verdict, harness_summary, harness_error = parse_harness_summary(harness)
                    case["harness"] = stored_process_record(harness)
                    case["harness_exit"] = harness["returncode"]
                    if harness_summary is not None:
                        case["harness_summary"] = harness_summary
                    case["verdict"] = verdict
                    if harness_error is not None:
                        case["reason"] = harness_error
                    elif harness_summary is not None:
                        case["reason"] = f"source harness verdict: {harness_summary['verdict']}"
                    else:  # Defensive: parse_harness_summary always supplies an error in this branch.
                        case["reason"] = "source harness did not produce a usable result"
            case["updated_at"] = utc_now()
            append_case_and_persist(corpus, corpus_path, case)
            terminal_ids.add(case_id)
            attempted_this_invocation += 1
            if case["verdict"] != "PASS" and args.fail_fast:
                stopped_early = True
                break

        update_corpus_summary(corpus)
        replace_json_atomically(corpus_path, corpus)
        all_requested_pass = True
        requested_case_ids = {case_id_for_seed(seed) for seed in range(args.seed_start, args.seed_start + args.count)}
        for case in corpus["cases"]:
            if case["case_id"] in requested_case_ids and case.get("verdict") != "PASS":
                all_requested_pass = False
                break
        summary = {
            "verdict": "PASS" if all_requested_pass and not stopped_early else "FAIL",
            "run_id": run_id,
            "corpus": str(corpus_path),
            "attempted": attempted_this_invocation,
            "skipped_terminal": skipped_terminal,
            "counts_by_verdict": corpus["counts_by_verdict"],
            "stopped_early": stopped_early,
        }
        print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
        return 0 if summary["verdict"] == "PASS" else 1
    except CorpusError as error:
        print(
            json.dumps(
                {"verdict": "CORPUS_ERROR", "error": str(error)},
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 2
    except Exception as error:  # Preserve a concise host protocol on unexpected failures too.
        print(
            json.dumps(
                {"verdict": "CORPUS_ERROR", "error": f"{type(error).__name__}: {error}"},
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

import Test.CSmithSeeds.GlobalChecksumGenerated

/-!
Stable module-qualified access to the generated global-initialization checksum
fixture. It uses the same `globvar _` placeholder repair as the source harness.
-/

namespace Test.CSmithSeeds.GlobalChecksumProgram

def prog : program_type function := _root_.prog

end Test.CSmithSeeds.GlobalChecksumProgram

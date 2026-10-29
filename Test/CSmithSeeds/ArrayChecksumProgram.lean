import Test.CSmithSeeds.ArrayChecksumGenerated

/-!
Stable module-qualified access to the generated array-initialization checksum
fixture. It uses the same `globvar _` placeholder repair as the source harness.
-/

namespace Test.CSmithSeeds.ArrayChecksumProgram

def prog : program_type function := _root_.prog

end Test.CSmithSeeds.ArrayChecksumProgram

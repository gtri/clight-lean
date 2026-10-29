-- This module serves as the root of the `CLightLean` library.
-- Import modules here that should be built as part of the library.
import CLightLean.CTypes

-- inductive expr : Type where
--   | Econst_int :
--   | No

-- #check expr
import CLightLean.AST
import CLightLean.Archi
#check Tptr
#check Tptr_name
#check x86_64

theorem x86_64_has_ptr64 : x86_64.ptr64 = true := rfl
theorem x86_32_no_ptr64 : x86_32.ptr64 = false := rfl
theorem ptr64_differs : x86_64.ptr64 ≠ x86_32.ptr64 := by simp

theorem Tptr_name_differs : @Tptr_name x86_64 ≠ @Tptr_name x86_32 := by
  unfold Tptr_name
  simp only [show x86_64.ptr64 = true from rfl,
             show x86_32.ptr64 = false from rfl]
  decide

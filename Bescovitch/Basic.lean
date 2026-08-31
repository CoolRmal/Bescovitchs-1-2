import Mathlib.Data.Nat.Basic

/-!
# Basic declarations

This file provides a small checked declaration confirming that Mathlib is available.
-/

namespace Bescovitch

/-- A minimal theorem used to verify the project setup. -/
theorem two_add_two : 2 + 2 = 4 := by
  rfl

end Bescovitch

import Mathlib

/-!
# Environment smoke test

This file checks that Mathlib and its `norm_num` tactic are available.
-/

example : (2 : ℝ) + 2 = 4 := by
  norm_num

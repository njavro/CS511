import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  -- Case split
  cases h with
  | inl h_x =>
    -- Case 1: Assume hx : x = 2
    rw [h_x]
    ring
  | inr h_y =>
    -- Case 2: Assume hy : y = -2
    rw [h_y]
    ring

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rw [show x ^ 2 - 3 * x + 2 = (x - 2)*(x - 1) by ring]
  cases h with
  | inl h1 =>
    rw [h1]
    norm_num -- find all instances
  | inr h2 =>
    rw [h2]
    norm_num

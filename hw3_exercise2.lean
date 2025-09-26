import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  -- Split the hypothesis in two cases
  cases h with
  | inl h1 =>
    rw [h1]
    -- norm_num solves calculation
    norm_num
  | inr h2 =>
    rw [h2]
    norm_num

import Mathlib

-- Tested in: www.live.lean-lang.org

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 := by
  rw [h3] at h2
  have hypothesis_b : b = 1 := by
   linarith [h2]
  rw [hypothesis_b] at h1
  rw [h3] at h1
  linarith [h1]

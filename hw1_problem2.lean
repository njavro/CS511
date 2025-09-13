import Mathlib

-- Tested in: www.live.lean-lang.org


example {a b : ℚ} (h1 : a - 3 = 2 * b) : a^2 - a + 3 = 4 * b^2 + 10 * b + 9 :=
  calc
    a^2 - a + 3 = (a - 3)^2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b)^2 + 5 * (2 * b) + 9   := by rw [h1]
    _ = 4 * b^2 + 10 * b + 9          := by ring

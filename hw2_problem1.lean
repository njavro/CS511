-- Done by Cases: First A assumed to be true then B
-- Done in: https://live.lean-lang.org/
example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D := by
  cases h₁ with
  | inl h_assumeA =>
    have h_assumeC : C := h₂ h_assumeA
    exact Or.inl h_assumeC
  | inr h_assumeB =>
    have h_assumeD : D := h₃ h_assumeB
    exact Or.inr h_assumeD

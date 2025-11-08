/- # CS 511, 31 Oct 2025, hw09_partial_solution.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic           -- needed for math2001_init
import Library.Tactic.Rel

math2001_init          --  needed to access Macbeth's tactics:
                       -- `addarith`, `cancel`, `extra`, `numbers`

/- # Execise 3 in Homework Assignment 09 -/

/- Exercise 5.3.6.3 in Macbeth's [MOP] -/
example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_cases h_e : ∃ x, ¬ P x
    · apply h_e
    · have h_all : ∀ x, P x
      · intro a
        by_cases ha : P a
        · apply ha
        · have h_ei : ∃ x, ¬ P x
          · use a
            apply ha
          contradiction
      contradiction
  ·
    intro h_e
    intro h_all
    rcases h_e with ⟨x, hx⟩
    have h_px : P x := h_all x
    apply hx h_px

/- Exercise 5.3.6.4 in Macbeth's [MOP] -/
example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc
    ¬ (∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a, ¬ (∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬ (a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ (a ≠ 1 ∧ b ≠ 1) := by rel [not_or]

/- # Exercise 4 in Homework Assignment 09 -/

/- Exercise 5.3.6.11 in Macbeth's [MOP]-/
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  · apply hk
  constructor
  · apply hk1
  · apply hkp

/- Exercise 5.3.6.13 in Macbeth's [MOP]-/
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have : Prime p
    · unfold Prime
      constructor
      · assumption
      · intro m h_div
        have hp_pos : 0 < p := by addarith [hp2]
        have hle : m ≤ p := Nat.le_of_dvd hp_pos h_div
        rcases hle.eq_or_lt with (h_eq | h_lt)
        · right
          assumption
        · left
          have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos h_div hp_pos
          have hmge_1 : 1 ≤ m := Nat.one_le_of_lt hm_pos
          rcases hmge_1.eq_or_lt with (h_m_eq_1 | h_m_gt_1)
          · exact h_m_eq_1.symm
          · have h_m_ge_2 : 2 ≤ m := h_m_gt_1
            have h_not_div := H m h_m_ge_2 h_lt
            contradiction
    contradiction
  push_neg at H
  exact H

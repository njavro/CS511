/- CS 511, 26 Sept 2025 -/
/- template for Exercise 4 in Homework Assignment 04 -/
import Mathlib.Tactic
import Mathlib.Logic.Basic
import Mathlib.Tactic.ByContra


-- Apologies for having it across multiple files before, hope this helps! :)

-- Exercise 3.1
-- MOP: 2.5.5
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6,5
  norm_num
  

-- Exercise 3.2
-- MOP: 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1,a
  ring


-- Exercise 3.3
-- MOP: 2.5.7
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · 
    linarith
  · 
    linarith



lemma prove_implication_negation (p q : Prop) : (p → q) → ¬ (p ∧ ¬ q) := by
  intro h_pq       -- introduce hypothesis h_pq : p → q
  by_contra h_pnq  -- introduce hypothesis h_pnq : p ∧ ¬ q
  obtain ⟨ h_p , h_nq ⟩ := h_pnq  -- break up h_npnq into h_p : p and h_nq : ¬ q
  have h_q : q := h_pq h_p -- introduce hypothesis h_q : q by applying h_pq to h_p
  contradiction    -- complete proof immediately by the contradiction { h_nq , h_q }

lemma prove_negation_implication (p q : Prop) :  ¬ (p ∧ ¬ q) → (p → q) := by
  intro h_neg_pnq    -- introduce hypothesis h_neg_pnq : ¬ (p ∧ q)
  intro h_p          -- introduce hypothesis h_p : p
  by_cases h_q : q   -- consider two cases: (1) q is true, (2) q is false, resulting in 2 goals
  exact h_q          -- complete first goal
  have h_pnq : (p ∧ ¬ q) := And.intro h_p h_q
  contradiction  -- complete the proof immediately by the contradiction { h_pnq , h_neg_pnq }




-- 1)
example {p q : Prop} : (p → q) → (¬p ∨ q)  := by
  intro h_pq
  have h_neg_pnq : ¬(p ∧ ¬q) := prove_implication_negation p q h_pq
  by_cases h_p : p
  ·
    right
    by_contra h_nq
    have h_pnq : p ∧ ¬q := And.intro h_p h_nq 
    contradiction
  · 
    left 
    exact h_p


-- 2)
example {p q : Prop} : (¬q → ¬p) → (p → q) := by
  intro h_nqnp
  have h_t : ¬(p ∧ ¬q) := by
    intro h_pnq 
    obtain ⟨h_p, h_nq⟩ := h_pnq 
    have h_np : ¬p := h_nqnp h_nq 
    contradiction
  exact prove_negation_implication p q h_t


-- 3)
example {p q : Prop} : (((p → q) → p) → p) := by
  intro hMain   
  by_contra hnp 
  have h_pq : p → q := by 
    intro h_p_t
    contradiction
  have h_p_d : p := hMain h_pq 
  contradiction 

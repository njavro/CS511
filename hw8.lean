/- # CS 511, 23 Oct 2025, hw08_template.lean -/

import Mathlib.Data.Real.Basic -- needed in order to use tactic `contrapose`

import Library.Basic   -- needed for math2001_init
math2001_init          -- needed to access Macbeth's tactics:
                       -- `addarith`, `cancel`, `extra`, `numbers`

/- # Exercise 3 in Homework 08 -/
/- Consult page 25 in Slides 18 for hints -/

example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  obtain ⟨x, hx⟩ := h
  intro x_h
  intro y_h
  have h_x_eq_x' : x = x_h := hx x_h
  have hx_eq_y' : x = y_h := hx y_h
  rw [Eq.symm h_x_eq_x']
  exact hx_eq_y'

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intro h_a
  obtain ⟨x, hx⟩ := h_a
  intro v_h
  intro w_h
  rw [Eq.symm (hx v_h)]
  exact hx w_h

-- 5.2.7.2
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  apply Iff.intro

  ·
    intro _ha
    intro h_q
    by_contra _hanp
    have h_nq : ¬Q := _ha _hanp
    contradiction
  ·
    intro _ha
    intro hnp
    intro he_aq
    have h_p : P := _ha he_aq
    contradiction


-- 5.3.6.9
example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t_h
  by_cases _h : t_h ≤ 4
  .
    apply Or.inr
    have _h4lt5 : (4 : ℝ) < 5 := by norm_num
    exact lt_of_le_of_lt _h _h4lt5
  ·
    apply Or.inl
    rw [not_le] at _h
    exact _h

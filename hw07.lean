/- # CS 511, 17 Oct 2025, hw07_template.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init

/- # EXERCISE 3 -/

/- # Example 4.5.5 -/
example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro odd_h even_h
    rw [Int.odd_iff_modEq] at odd_h
    rw [Int.even_iff_modEq] at even_h
    have h_contra :=
      calc 1≡n[ZMOD 2] :=by rel [odd_h]
        _≡0[ZMOD 2] :=by rel [even_h]
    numbers at h_contra
  · intro h_not_even
    obtain even_h|odd_h := Int.even_or_odd n
    · contradiction
    · apply odd_h

/- # Example 4.5.6 -/
example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  sorry

/- # EXERCISE 4 -/

/- # Exercise 5.1.7.11 -/
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro P_exist
    obtain ⟨w, hw⟩ := P_exist
    use w
    exact (h w).mp hw
  · intro Q_exist
    obtain ⟨w, hw⟩ := Q_exist
    use w
    exact (h w).mpr hw

/- # Exercise 5.1.7.12 -/
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro hxy
    obtain ⟨wx, hy⟩ := hxy
    obtain ⟨ay, h_P⟩ := hy
    use ay
    use wx
    exact h_P
  · intro hyx
    obtain ⟨bey, hx⟩ := hyx
    obtain ⟨wx, h_P⟩ := hx
    use wx
    use bey
    exact h_P

/- # Exercise 5.1.7.14 -/
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro ar
    obtain ⟨h_exists_P, h_Q⟩ := ar
    obtain ⟨hyp_W, a⟩ := h_exists_P
    use hyp_W
    exact ⟨a, h_Q⟩
  · intro ar
    obtain ⟨war_hW, and_⟩ := ar
    constructor
    · use war_hW
      exact and_.left
    · exact and_.right

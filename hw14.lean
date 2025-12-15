/- # 8 December 2025 hw14_template.lean -/

import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

-- Exercise 9.1.10.1 in [MOP]

--Disprove
--example : 4 ∈ {a : ℚ | a < 3} := by
--  sorry

-- disproof of the above
example : ¬ (4 ∈ {a : ℚ | a < 3}) := by
  norm_num


example : 4 ∉ {a : ℚ | a < 3} := by
  norm_num

-- Exercise 9.1.10.2 in [MOP]
example : 6 ∈ {n : ℕ | n ∣ 42} := by
  change (6:ℕ)∣42
  refine ⟨7,?_⟩
  rfl

-- Disprove
--example : 6 ∉ {n : ℕ | n ∣ 42} := by
--  sorry

--Disproof
example : ¬ (6 ∉ {n : ℕ | n ∣ 42}) := by
  intro hnot
  have hmem : 6∈{n:ℕ|n∣42} := by
    change (6:ℕ)∣42
    refine ⟨7,rfl⟩
  exact hnot hmem

-- Exercise 9.1.10.3 in [MOP]
-- Disprove
--example : 8 ∈ {k : ℤ | 5 ∣ k} := by
--  sorry

-- Disproof
example : ¬ (8 ∈ {k : ℤ | 5 ∣ k}) := by
  intro h
  have hmod0 : (8:ℤ)%5=0 := by
    exact Int.emod_eq_zero_of_dvd h
  have hmod3 : (8:ℤ)%5=3 := by
    norm_num
  have h3eq0 : (3:ℤ)=0 := by
    calc
      (3:ℤ)=(8:ℤ)%5 := by exact hmod3.symm
      _ = 0 := hmod0
  have h3ne0 : (3:ℤ)≠0 := by
    norm_num
  exact h3ne0 h3eq0

example : 8 ∉ {k:ℤ|5∣k} := by
  intro h
  have hmod0 :(8:ℤ)%5=0 := by
    exact Int.emod_eq_zero_of_dvd h
  have hmod3 :(8:ℤ)%5=3 := by
    norm_num
  have h3eq0 :(3:ℤ)=0 := by
    calc
      (3:ℤ)=(8:ℤ)%5 := by exact hmod3.symm
      _ = 0 := hmod0
  have h3ne0 : (3:ℤ)≠0 := by
    norm_num
  exact h3ne0 h3eq0


/-# Exercise 5 -/

-- Exercise 9.1.10.6 in [MOP]

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  intro n hn
  change (20:ℕ) ∣ n at hn
  rcases hn with ⟨k, hk⟩
  change (5 : ℕ) ∣ n
  refine ⟨4*k, ?_⟩
  have h54 : (5:ℕ)*4=20 := by
    norm_num
  calc
    n = 20*k := hk
    _ = ((5:ℕ)*4)*k := by
      rw [← h54]
    _ = (5:ℕ)*(4*k) := by
      exact Nat.mul_assoc 5 4 k




-- Disprove
--example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
--  sorry

-- Disproof
example : ¬ ({a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x}) := by
  intro hnot
  have hsub : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
    intro n hn
    change (20:ℕ) ∣ n at hn
    rcases hn with ⟨k, hk⟩
    change (5:ℕ) ∣ n
    refine ⟨4*k, ?_⟩
    have h54:(5:ℕ)*4=20 := by
      norm_num
    calc
      n = 20*k := hk
      _ = ((5:ℕ)*4)*k := by
        rw [← h54]
      _ = (5:ℕ)*(4*k) := by
        exact Nat.mul_assoc 5 4 k
  exact hnot hsub



-- Exercise 9.1.10.7 in [MOP]

-- Disproved
--example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
--  sorry

-- Disproof
example : ¬ ({a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x}) := by
  rw [subset_def]
  push_neg
  use 5
  constructor
  · use 1
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    have h_le : 20 ≤ 5 := by
      rw [hk]
      have k_pos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro k_zero
        rw [k_zero, mul_zero] at hk
        numbers at hk
      apply Nat.mul_le_mul_left 20 k_pos
    numbers at h_le


example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  rw [Set.not_subset]
  use 5
  constructor
  · exact Nat.dvd_refl 5
  · intro h
    have h_le : 20≤5 := Nat.le_of_dvd (by norm_num) h
    norm_num at h_le





--Exercise 9.2.8.5 in [MOP]
example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  intro x hx
  obtain ⟨k, hk⟩ := hx
  rw [sub_eq_iff_eq_add] at hk
  rw [hk]
  constructor
  · use k*5+3
    ring
  · use k*2+1
    ring


/-# PROBLEM 1 -/

-- Exercise 9.2.8.6 in [MOP]
example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  intro n h
  obtain ⟨h5, h8⟩:=h
  obtain ⟨a, ha⟩:=h5
  obtain ⟨b, hb⟩:=h8
  use 2*a-3*b
  have h_eqn : n=(5*a)*16-(8*b)*15 := by
    rw [← ha, ← hb]
    ring
  rw [h_eqn]
  ring

-- Exercise 9.3.6.1 in [MOP]

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  rw [Injective]
  push_neg
  use {3}, ∅
  constructor
  · rw [r,r]
    rw [union_self]
    rw [empty_union]
  · intro h
    have h1 : 3 ∈ ({3}:Set ℕ) := mem_singleton 3
    rw [h] at h1
    exact not_mem_empty 3 h1

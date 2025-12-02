/- # 21 November 2025, hw12_template1.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.InjectiveSurjective

math2001_init

open Set Function Nat

/-# Exercise 3 in HW 12 -/

--Exercise 6.4.3.1 in [MOP]
theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Nat.Odd x ∧ n = 2 ^ a * x := by
  revert hn
  refine Nat.strong_induction_on n ?_
  intro k IH hk_pos
  -- Even / Odd
  have hEO : Nat.Even k ∨ Nat.Odd k := Nat.even_or_odd k
  cases hEO with
  | inr hodd =>
      refine ⟨0, k, hodd, ?_⟩
      have hpow : 2 ^ 0 = (1 : ℕ) := by rfl
      rw [hpow, one_mul]
  | inl heven =>
      rcases heven with ⟨m, hm⟩
      cases m with
      | zero =>
          have hk0 : k = 0 := by
            have h2 : 0 = 0 := Nat.mul_zero 0
            exact Eq.trans hm h2
          have : False := by
            have hk0_lt : 0 < 0 := hk0 ▸ hk_pos
            exact Nat.lt_irrefl 0 hk0_lt
          cases this
      | succ m' =>
          have hmpos : 0 < Nat.succ m' := Nat.succ_pos m'
          have hlt : Nat.succ m' < k := by
            have htemp : Nat.succ m' < Nat.succ m' + Nat.succ m' :=
              lt_add_of_pos_right (Nat.succ m') hmpos
            have htwo : Nat.succ m' + Nat.succ m' = 2 * Nat.succ m' :=
              (two_mul (Nat.succ m')).symm
            have htemp2 : Nat.succ m' < 2 * Nat.succ m' :=
              htwo ▸ htemp
            have hk : k = 2 * Nat.succ m' := hm
            exact hk ▸ htemp2
          rcases IH (Nat.succ m') hlt hmpos with ⟨a, x, hxodd, hmx⟩
          have h1 : k = 2*(2^a*x) := by
            calc
              k = 2*Nat.succ m' := hm
              _ = 2*(2^a*x) := by
                    have h : 2*Nat.succ m' = 2*(2^a*x) :=
                      congrArg (fun t => 2*t) hmx
                    exact h
          have h2 : 2*(2^a*x) = 2^Nat.succ a*x := by
            calc
              2*(2^a*x)
                  = (2*2^a)*x := by
                        exact (Nat.mul_assoc 2 (2^a) x).symm
              _ = (2^a*2)*x := by
                        have hc : 2*2^a = 2^a*2 :=
                          Nat.mul_comm 2 (2^a)
                        exact congrArg (fun t => t*x) hc
              _ = 2 ^ Nat.succ a * x := by
                        have hp : 2 ^ Nat.succ a = 2^a*2 :=
                          pow_succ 2 a
                        have : (2^a*2)*x = 2^Nat.succ a*x :=
                          congrArg (fun t => t*x) hp.symm
                        exact this
          have hk_eq : k = 2 ^ Nat.succ a*x :=
            Eq.trans h1 h2
          refine ⟨Nat.succ a, x, hxodd, hk_eq⟩

/-# Exercise 4 in HW 12 -/

-- Exercise 8.3.10.2 in [MOP]

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

example : Inverse u v := by
  constructor
  · ext x
    dsimp [u,v]
    ring
  · ext x
    dsimp [u,v]
    ring

-- Exercise 8.3.10.3 in [MOP]

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
  Injective (g∘f) := by
  intro x_1 x_2 h_
  apply hf
  apply hg
  exact h_

-- Exercise 8.3.10.4 in [MOP]

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro z_
  obtain ⟨y_, hy⟩ := hg z_
  obtain ⟨x_, hx⟩ := hf y_
  use x_
  dsimp
  rw [hx]
  exact hy

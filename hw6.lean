import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  rel [ha]


example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    _ = 2 + 5 * 8 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra


example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra


example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

/-! # Exercises -/

-- Exercise 3.4.5.1
example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  calc
  n^3+7*n ≡ 1^3+7*1[ZMOD 3] := by rel [hn]
    _= 2+3*2 := by numbers
    _≡ 2[ZMOD 3] := by extra

-- Exercise 3.4.5.3
example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] :=
  calc
    (a+b)^3 = a^3+3*a^2*b+3*a*b^2+b^3 := by ring
    _ = a^3+b^3+3*(a^2*b+a*b^2) := by ring
    _ ≡ a^3+b^3[ZMOD 3] := by extra

-- Exercise 3.4.5.4
example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2
  calc
    4*2=1+7*1:= by numbers
    _  ≡1[ZMOD 7]  := by extra


--Example 4.1.3
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  contrapose! h
  use (a+b)/2
  constructor
  · have h1 :a+b<2*a:=
      calc
      a+b<a+a:= by rel [h]
      _ =2*a:= by ring
    apply(div_lt_iff' (by numbers : (0 : ℝ) < 2)).mpr
    exact h1
  · have h1:2*b<a+b:=
      calc
      2*b=b+b:= by ring
      _<a+b := by rel [h]
    apply (lt_div_iff' (by numbers : (0 : ℝ) < 2)).mpr
    exact h1

--Example 4.1.4
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  ·
    apply hb2
    apply ha1
  ·
    apply ha2
    apply hb1

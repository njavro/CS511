import Library.Basic
import Library.Theory.ModEq.Defs

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


--Exercise 3.3.4
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨a_1, h_a1⟩ := h2
  obtain ⟨a_2, h_a2⟩ := h1
  use a_2 - a_1
  calc
    (a - c)-(b - d) =(a - b)-(c - d) := by ring 
    _ =n*a_2-(n * a_1) := by rw [h_a2, h_a1]          
    _ =n*(a_2 - a_1) := by ring                   



-- Exercise 3.3.5
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨m, hm⟩ := h1
  use -m
  calc
    -a - -b = -(a-b) := by ring
    _ = -(n*m)   := by rw [hm]
    _ = n*(-m)   := by ring


--Exercise 3.3.12.3
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨a_1, h_a1⟩ := h1
  obtain ⟨a_2, h_a2⟩ := h2
  use a_1 + a_2
  calc
    a - c = (a-b)+(b-c) := by ring 
    _ = n*a_1+n*a_2 := by rw [h_a1, h_a2] 
    _ = n*(a_1+a_2) := by ring 

--Exercise 3.3.12.6
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  obtain ⟨a1, h_a1⟩ := h
  use 2 * a1
  linear_combination 2 * h_a1

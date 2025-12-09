/- # 20 November 2025 hw13_template.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic

import Library.Theory.InjectiveSurjective

math2001_init

open Set Function Nat

/-# Exercise 3-/

--Exercise 8.3.10.5 in [MOP]
example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  classical
  choose g hg using hf
  refine ⟨g, ?_⟩
  funext y
  simpa [Function.comp] using hg y


--Exercise 8.3.10.7 in [MOP]
example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1=g2:=by
  rcases h1 with ⟨h1_left,h1_right⟩
  rcases h2 with ⟨h2_left,h2_right⟩
  funext y
  have h1' := congrArg (fun h=>h (g2 y)) h1_left
  have h2' := congrArg (fun h=>h y) h2_right
  dsimp [Function.comp, id] at h1' h2'
  have h3 : g1 y=g1 (f (g2 y)) :=
    congrArg g1 h2'.symm
  exact h3.trans h1'



/-# Exercise 4-/
--Exercise 8.4.10.1 in [MOP]
example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (x,y)↦(y+x,x)
  constructor
  · ext ⟨r,s⟩
    dsimp
    ring
  · ext ⟨u,v⟩
    dsimp
    ring



--Exercise 8.4.10.2.1 in [MOP]
example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  intro h
  have output_eq : (fun((x,y):ℤ×ℤ)↦x-2*y-1) (0,0) =
                   (fun((x,y):ℤ×ℤ)↦x-2*y-1) (2,1) := by
    rfl
  have input_eq : (0,0)=((2:ℤ),(1:ℤ)):=h output_eq
  injection input_eq with x_eq _
  have contra : (0:ℤ)≠2:= by norm_num
  exact contra x_eq




--Exercise 8.4.10.2.2 in [MOP]
example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  rw [Surjective]
  intro z
  use (z+1,0)
  dsimp
  ring

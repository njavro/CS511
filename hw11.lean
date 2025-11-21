/- # CS 511, 14 November 2025, hw11_template.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust --
    -- The `exhaust` tactic is typically used to solve goals that involve
    -- finite-case analysis, primarily in the context of sets or other
    -- inductive types with a small number of elements. It is generally
    -- used after the tactics `dsimp` or `intro` in a by block.
math2001_init
    --  needed to access Macbeth's tactics `addarith`, `cancel`, `extra`, `numbers`

open Function
namespace Int

/- # Exercise 3 in Homework 11 -/

--Exercise 8.1.13.2
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  intro _Arg
  have eq_arg :0=1:= _Arg (show (fun x ↦ 3) 0 = (fun x↦3) 1 by rfl)
  norm_num at eq_arg

--Exercise 8.1.13.3
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  intro x_ y_ h_
  have h' : 3*x_+(-1) = 3*y_+(-1) := by
    simpa [sub_eq_add_neg] using h_
  have h_arg1 : 3*x_ = 3*y_ := by
    addarith [h']
  have h_arg2 : x_ = y_ := by
    cancel 3 at h_arg1
  exact h_arg2

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry

--Exercise 8.1.13.5
--# Prove one-------------------------------------------------------

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  intro y_arg
  refine ⟨y_arg/2,?_⟩
  have _arg : (2:ℝ) ≠ 0 := by numbers
  calc
    2*(y_arg/2)
        =(2*y_arg)/2 := by
            ring
    _   = y_arg := by
            have := mul_div_cancel_left y_arg _arg
            simpa [mul_comm, mul_left_comm, mul_assoc] using this

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

--# -----------------------------------------------------------------

/- # Exercise 4 in Homework 11 -/

inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

--Exercise 8.1.13.8
--# Prove one-------------------------------------------------------

example : Injective h := by
  sorry

example : ¬ Injective h := by
  intro final_hypothesis
  have output_1 : h athos = h aramis := by rfl
  have same_input : athos = aramis := final_hypothesis output_1
  contradiction

--Exercise 8.1.13.9
--# Prove one-------------------------------------------------------

example : Surjective h := by
  intro y_Arg
  cases y_Arg
  . use porthos
    rfl
  . use athos
    rfl

example : ¬ Surjective h := by
  sorry

--# ----------------------------------------------------------------

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

--Exercise 8.1.13.11
--# Prove one-------------------------------------------------------

example : Surjective l := by
  sorry

example : ¬ Surjective l := by
  intro h
  have exists_input := h athos
  cases exists_input with
  | intro l_aw hw =>
    cases l_aw
    . dsimp [l] at hw
      contradiction
    . dsimp [l] at hw
      contradiction

--# ----------------------------------------------------------------

/- # Problem 2 in Homework 11 -/

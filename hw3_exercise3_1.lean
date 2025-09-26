-- Tested in Live Lean Lang
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

theorem exercise4 : (¬P ∧ ¬Q) → ¬(Q ∨ P) := by
  intro first_assumption --Assume: (¬P ∧ ¬Q) / New Goal ¬(Q ∨ P)

  intro second_assumption --Assume for the purpose of contradiction: (Q v P) 

  -- Split cases for the proof of second_assumption
  cases second_assumption with
  | inl case_Q =>
    -- Assume Q and extract notQ from first_assumption, hence contradiction
    exact first_assumption.2 case_Q

  | inr case_P =>
     -- Assume P / Contradiction
    exact first_assumption.1 case_P

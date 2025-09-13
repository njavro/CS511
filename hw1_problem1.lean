import Mathlib

-- Tested in: www.live.lean-lang.org


example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w =((3*w + 1)-1)/3   := by simp       
    _ =(4-1)/3           := by rw [h1]     
    _ =3/3               := by norm_num   
    _ =1                 := by norm_num 

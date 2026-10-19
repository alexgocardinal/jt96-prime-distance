import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace JT96

/-- The union of the closed intervals [3k+1, 3k+2]. -/
def AllowedPhase (x : ℝ) : Prop :=
  ∃ k : ℤ, 3 * (k : ℝ) + 1 ≤ x ∧
    x ≤ 3 * (k : ℝ) + 2

theorem allowedPhase_small
    (x : ℝ)
    (hlo : -(1 / 2 : ℝ) ≤ x)
    (hhi : x ≤ 5 / 3)
    (hx : AllowedPhase x) :
    1 ≤ x := by
  rcases hx with ⟨k, hklo, hkhi⟩
  have ha : (-1 : ℝ) < (k : ℝ) := by linarith
  have hb : (k : ℝ) < 1 := by linarith
  have ha' : (-1 : ℤ) < k := by exact_mod_cast ha
  have hb' : k < (1 : ℤ) := by exact_mod_cast hb
  have hk : k = 0 := by omega
  subst k
  norm_num at hklo
  exact hklo

theorem allowedPhase_large
    (x : ℝ)
    (hlo : (9 / 2 : ℝ) ≤ x)
    (hhi : x ≤ 22 / 3)
    (hx : AllowedPhase x) :
    x ≤ 5 ∨ 7 ≤ x := by
  rcases hx with ⟨k, hklo, hkhi⟩
  have ha : (0 : ℝ) < (k : ℝ) := by linarith
  have hb : (k : ℝ) < 3 := by linarith
  have ha' : (0 : ℤ) < k := by exact_mod_cast ha
  have hb' : k < (3 : ℤ) := by exact_mod_cast hb
  have hk : k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl
  · left
    norm_num at hkhi
    exact hkhi
  · right
    norm_num at hklo
    exact hklo

end JT96

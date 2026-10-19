import JT96.PhaseBounds
import Mathlib.Tactic

namespace JT96

theorem endpoint_forces_three_dvd
    (p a : ℤ) (theta alpha : ℝ)
    (hphase : (p : ℝ) * theta = 3 * (a : ℝ) + alpha)
    (hend :
      (theta = 1 / 2 ∧ alpha = 3 / 2) ∨
      (theta = 2 / 3 ∧ alpha = 2)) :
    3 ∣ p := by
  rcases hend with ⟨ht, ha⟩ | ⟨ht, ha⟩
  · rw [ht, ha] at hphase
    have hr : (p : ℝ) = 6 * (a : ℝ) + 3 := by
      linarith
    have hi : p = 6 * a + 3 := by
      exact_mod_cast hr
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  · rw [ht, ha] at hphase
    have hr : 2 * (p : ℝ) = 9 * (a : ℝ) + 6 := by
      linarith
    have hi : 2 * p = 9 * a + 6 := by
      exact_mod_cast hr
    rw [Int.dvd_iff_emod_eq_zero]
    omega

end JT96

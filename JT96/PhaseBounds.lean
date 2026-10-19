import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace JT96

theorem phase_endpoint_cases
    (theta alpha beta : ℝ)
    (ht_lo : 1 / 2 ≤ theta)
    (ht_hi : theta ≤ 2 / 3)
    (ha_lo : 1 ≤ alpha)
    (ha_hi : alpha ≤ 2)
    (hb_lo : 1 ≤ beta)
    (hb_hi : beta ≤ 2)
    (hs : 1 ≤ alpha - beta + theta)
    (hr : alpha + beta + 5 * theta ≤ 5 ∨
          7 ≤ alpha + beta + 5 * theta) :
    (theta = 1 / 2 ∧ alpha = 3 / 2 ∧ beta = 1) ∨
    (theta = 2 / 3 ∧ alpha = 2 ∧ beta = 5 / 3) := by
  rcases hr with hr | hr
  · left
    have ht : theta = 1 / 2 := by linarith
    have hb : beta = 1 := by linarith
    have ha : alpha = 3 / 2 := by linarith
    exact ⟨ht, ha, hb⟩
  · right
    have ht : theta = 2 / 3 := by linarith
    have ha : alpha = 2 := by linarith
    have hb : beta = 5 / 3 := by linarith
    exact ⟨ht, ha, hb⟩

end JT96

import JT96.Divisibility
import JT96.PhaseIntervals

namespace JT96

theorem allowedPhase_sub_three_mul
    (x : ℝ) (k : ℤ) (hx : AllowedPhase x) :
    AllowedPhase (x - 3 * (k : ℝ)) := by
  rcases hx with ⟨j, hlo, hhi⟩
  refine ⟨j - k, ?_, ?_⟩ <;> push_cast <;> linarith

theorem six_distance_slope_forces_three_dvd
    (p q : ℤ) (theta : ℝ)
    (ht_lo : 1 / 2 ≤ theta)
    (ht_hi : theta ≤ 2 / 3)
    (hp : AllowedPhase ((p : ℝ) * theta))
    (hq : AllowedPhase ((q : ℝ) * theta))
    (hr : AllowedPhase (((p + q + 5 : ℤ) : ℝ) * theta))
    (hs : AllowedPhase (((p - q + 1 : ℤ) : ℝ) * theta)) :
    3 ∣ p := by
  rcases hp with ⟨a, hpa_lo, hpa_hi⟩
  rcases hq with ⟨b, hqb_lo, hqb_hi⟩

  let alpha : ℝ := (p : ℝ) * theta - 3 * (a : ℝ)
  let beta : ℝ := (q : ℝ) * theta - 3 * (b : ℝ)

  have ha_lo : 1 ≤ alpha := by
    dsimp [alpha]
    linarith
  have ha_hi : alpha ≤ 2 := by
    dsimp [alpha]
    linarith
  have hb_lo : 1 ≤ beta := by
    dsimp [beta]
    linarith
  have hb_hi : beta ≤ 2 := by
    dsimp [beta]
    linarith

  have hs0 := allowedPhase_sub_three_mul _ (a - b) hs
  have hs1 : AllowedPhase (alpha - beta + theta) := by
    convert hs0 using 1 <;>
      dsimp [alpha, beta] <;> push_cast <;> ring

  have hr0 := allowedPhase_sub_three_mul _ (a + b) hr
  have hr1 : AllowedPhase (alpha + beta + 5 * theta) := by
    convert hr0 using 1 <;>
      dsimp [alpha, beta] <;> push_cast <;> ring

  have hs_bound : 1 ≤ alpha - beta + theta :=
    allowedPhase_small _
      (by linarith) (by linarith) hs1

  have hr_cases :
      alpha + beta + 5 * theta ≤ 5 ∨
      7 ≤ alpha + beta + 5 * theta :=
    allowedPhase_large _
      (by linarith) (by linarith) hr1

  have he := phase_endpoint_cases theta alpha beta
    ht_lo ht_hi ha_lo ha_hi hb_lo hb_hi hs_bound hr_cases

  have hp_id :
      (p : ℝ) * theta = 3 * (a : ℝ) + alpha := by
    dsimp [alpha]
    ring

  apply endpoint_forces_three_dvd p a theta alpha hp_id
  rcases he with ⟨ht, ha, _⟩ | ⟨ht, ha, _⟩
  · exact Or.inl ⟨ht, ha⟩
  · exact Or.inr ⟨ht, ha⟩

end JT96

import JT96.PhaseGrid

namespace JT96

theorem phase_box_hit
    (p q alpha lower upper betaLower betaUpper : ℝ)
    (hp : 60000 < p)
    (hwidth : 1 / 1000 ≤ upper - lower)
    (hBwidth : 9 / 50 ≤ betaUpper - betaLower)
    (hclose : |q / p - 5 / 18| < 1 / 20000) :
    ∃ theta : ℝ, ∃ a b : ℤ,
      lower < theta ∧ theta < upper ∧
      p * theta = 3 * (a : ℝ) + alpha ∧
      betaLower < q * theta - 3 * (b : ℝ) ∧
      q * theta - 3 * (b : ℝ) < betaUpper := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  let m : ℤ := Int.floor ((p * lower - alpha) / 3) + 1
  let theta0 : ℝ := (3 * (m : ℝ) + alpha) / p
  let x : ℝ := q * theta0 / 3

  have hflo := Int.floor_le ((p * lower - alpha) / 3)
  have hfhi := Int.lt_floor_add_one ((p * lower - alpha) / 3)
  have hmlo : p * lower < 3 * (m : ℝ) + alpha := by
    dsimp [m]
    push_cast
    linarith
  have hmhi : 3 * (m : ℝ) + alpha ≤ p * lower + 3 := by
    dsimp [m]
    push_cast
    linarith
  have hbase : p * theta0 = 3 * (m : ℝ) + alpha := by
    dsimp [theta0]
    field_simp [hpne] <;> ring

  have hBW :
      (3 : ℝ) / 50 ≤ betaUpper / 3 - betaLower / 3 := by
    linarith
  obtain ⟨j, k, hj0, hj18, hL, hU⟩ :=
    near_grid18_hits_interval x (q / p)
      (betaLower / 3) (betaUpper / 3) hBW hclose

  have hj17 : j ≤ 17 := by omega
  have hjR0 : (0 : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hj0
  have hjR17 : (j : ℝ) ≤ 17 := by
    exact_mod_cast hj17

  let theta : ℝ := theta0 + 3 * (j : ℝ) / p
  have hstep : p * theta = p * theta0 + 3 * (j : ℝ) := by
    dsimp [theta]
    field_simp [hpne] <;> ring
  have hwidthMul :=
    mul_le_mul_of_nonneg_left hwidth (le_of_lt hp0)
  have hscaledLo : p * lower < p * theta := by
    nlinarith only [hmlo, hbase, hstep, hjR0]
  have hscaledHi : p * theta < p * upper := by
    nlinarith only [hmhi, hbase, hstep, hjR17, hwidthMul, hp]

  have hqtheta :
      q * theta - 3 * (k : ℝ) =
        3 * (x + (j : ℝ) * (q / p) - (k : ℝ)) := by
    dsimp [theta, x]
    field_simp [hpne] <;> ring

  refine ⟨theta, m + j, k, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mul_lt_mul_left hp0).mp hscaledLo
  · exact (mul_lt_mul_left hp0).mp hscaledHi
  · push_cast
    nlinarith only [hbase, hstep]
  · rw [hqtheta]
    linarith only [hL]
  · rw [hqtheta]
    linarith only [hU]

end JT96

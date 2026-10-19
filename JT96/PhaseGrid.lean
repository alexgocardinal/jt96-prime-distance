import JT96.DeletionBoxes

namespace JT96

theorem grid18_hits_interval
    (x lower upper : ℝ)
    (hwidth : (1 : ℝ) / 18 < upper - lower) :
    ∃ j k : ℤ,
      0 ≤ j ∧ j < 18 ∧
      lower < x + (j : ℝ) * (5 / 18) - (k : ℝ) ∧
      x + (j : ℝ) * (5 / 18) - (k : ℝ) < upper := by
  let n : ℤ := Int.floor (18 * (lower - x)) + 1
  let j : ℤ := (11 * n) % 18
  let k : ℤ := 3 * n - 5 * ((11 * n) / 18)
  have hj0 : 0 ≤ j := by
    dsimp [j]
    omega
  have hj18 : j < 18 := by
    dsimp [j]
    omega
  have hrepr : 5 * j = n + 18 * k := by
    dsimp [j, k]
    omega
  have hreprR :
      5 * (j : ℝ) = (n : ℝ) + 18 * (k : ℝ) := by
    exact_mod_cast hrepr
  have hflo := Int.floor_le (18 * (lower - x))
  have hfhi := Int.lt_floor_add_one (18 * (lower - x))
  have hnlo : 18 * (lower - x) < (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith
  have hnhi : (n : ℝ) ≤ 18 * (lower - x) + 1 := by
    dsimp [n]
    push_cast
    linarith
  refine ⟨j, k, hj0, hj18, ?_, ?_⟩ <;> linarith

theorem near_grid18_hits_interval
    (x ratio lower upper : ℝ)
    (hwidth : (3 : ℝ) / 50 ≤ upper - lower)
    (hclose : |ratio - 5 / 18| < 1 / 20000) :
    ∃ j k : ℤ,
      0 ≤ j ∧ j < 18 ∧
      lower < x + (j : ℝ) * ratio - (k : ℝ) ∧
      x + (j : ℝ) * ratio - (k : ℝ) < upper := by
  have htrim :
      (1 : ℝ) / 18 <
        (upper - 1 / 900) - (lower + 1 / 900) := by
    linarith
  obtain ⟨j, k, hj0, hj18, hL, hU⟩ :=
    grid18_hits_interval x
      (lower + 1 / 900) (upper - 1 / 900) htrim
  have hj17 : j ≤ 17 := by omega
  have hjR0 : (0 : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hj0
  have hjR17 : (j : ℝ) ≤ 17 := by
    exact_mod_cast hj17
  obtain ⟨hrlo, hrhi⟩ := abs_lt.mp hclose
  have hmlo := mul_nonneg hjR0
    (show (0 : ℝ) ≤ ratio - 5 / 18 + 1 / 20000 by
      linarith)
  have hmhi := mul_nonneg hjR0
    (show (0 : ℝ) ≤ 1 / 20000 - (ratio - 5 / 18) by
      linarith)
  refine ⟨j, k, hj0, hj18, ?_, ?_⟩ <;> nlinarith

end JT96

import JT96.WindowBands
import Mathlib.Data.Real.Basic

namespace JT96

theorem window_blocks_bound
    (F : ℕ → ℤ) (hzero : F 0 = 0)
    (d : ℕ) (lower upper : ℤ)
    (hw : ∀ n, lower ≤ F (n + d) - F n ∧
                  F (n + d) - F n ≤ upper)
    (k : ℕ) :
    (k : ℤ) * lower ≤ F (k * d) ∧
    F (k * d) ≤ (k : ℤ) * upper := by
  induction k with
  | zero =>
      simp [hzero]
  | succ k ih =>
      have hblock := hw (k * d)
      have hidx : (k + 1) * d = k * d + d := by ring
      rw [hidx]
      push_cast
      constructor <;>
        nlinarith [ih.1, ih.2, hblock.1, hblock.2]

theorem window_band_cross_bound
    (F : ℕ → ℤ) (hzero : F 0 = 0)
    (d e : ℕ)
    (lower_d upper_d lower_e upper_e : ℤ)
    (hd : ∀ n, lower_d ≤ F (n + d) - F n ∧
                  F (n + d) - F n ≤ upper_d)
    (he : ∀ n, lower_e ≤ F (n + e) - F n ∧
                  F (n + e) - F n ≤ upper_e) :
    (e : ℤ) * lower_d ≤ (d : ℤ) * upper_e := by
  have hleft :=
    window_blocks_bound F hzero d lower_d upper_d hd e
  have hright :=
    window_blocks_bound F hzero e lower_e upper_e he d
  rw [Nat.mul_comm d e] at hright
  exact hleft.1.trans hright.2

theorem window_band_ratio_bound
    (F : ℕ → ℤ) (hzero : F 0 = 0)
    (d e : ℕ) (hdpos : 0 < d) (hepos : 0 < e)
    (lower_d upper_d lower_e upper_e : ℤ)
    (hd : ∀ n, lower_d ≤ F (n + d) - F n ∧
                  F (n + d) - F n ≤ upper_d)
    (he : ∀ n, lower_e ≤ F (n + e) - F n ∧
                  F (n + e) - F n ≤ upper_e) :
    (lower_d : ℝ) / (d : ℝ) ≤
      (upper_e : ℝ) / (e : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast hepos
  apply (div_le_div_iff₀ hdR heR).2
  have hc := window_band_cross_bound F hzero d e
    lower_d upper_d lower_e upper_e hd he
  have hcR :
      (e : ℝ) * (lower_d : ℝ) ≤
        (d : ℝ) * (upper_e : ℝ) := by
    exact_mod_cast hc
  nlinarith

end JT96

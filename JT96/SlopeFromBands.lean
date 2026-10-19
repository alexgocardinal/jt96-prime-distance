import JT96.BlockBounds
import JT96.FirstExample
import Mathlib.Data.Real.Archimedean

namespace JT96

theorem common_slope_from_bounds
    (D : Set ℕ) (h2 : 2 ∈ D) (h3 : 3 ∈ D)
    (lower upper : ℕ → ℝ)
    (hcross : ∀ d ∈ D, ∀ e ∈ D, lower d ≤ upper e)
    (hl2 : (1 : ℝ) / 2 ≤ lower 2)
    (hu3 : upper 3 ≤ (2 : ℝ) / 3) :
    ∃ theta : ℝ,
      1 / 2 ≤ theta ∧ theta ≤ 2 / 3 ∧
      ∀ d ∈ D, lower d ≤ theta ∧ theta ≤ upper d := by
  let S : Set ℝ := lower '' D
  have hne : S.Nonempty := ⟨lower 2, 2, h2, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨upper 3, ?_⟩
    rintro x ⟨d, hd, rfl⟩
    exact hcross d hd 3 h3
  refine ⟨sSup S, ?_, ?_, ?_⟩
  · exact hl2.trans (le_csSup hbdd ⟨2, h2, rfl⟩)
  · have hu : sSup S ≤ upper 3 := by
      apply csSup_le hne
      rintro x ⟨d, hd, rfl⟩
      exact hcross d hd 3 h3
    exact hu.trans hu3
  · intro d hd
    constructor
    · exact le_csSup hbdd ⟨d, hd, rfl⟩
    · apply csSup_le hne
      rintro x ⟨e, he, rfl⟩
      exact hcross e he d hd

theorem slope_from_window_bands
    (D : Set ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (h2 : 2 ∈ D) (h3 : 3 ∈ D)
    (F : ℕ → ℤ) (hzero : F 0 = 0)
    (k : ℕ → ℤ)
    (hk2 : k 2 = 0) (hk3 : k 3 = 0)
    (hw : ∀ d ∈ D, ∀ n,
      3 * k d + 1 ≤ F (n + d) - F n ∧
      F (n + d) - F n ≤ 3 * k d + 2) :
    SlopeFeasible D := by
  let lower : ℕ → ℝ :=
    fun d => ((3 * k d + 1 : ℤ) : ℝ) / (d : ℝ)
  let upper : ℕ → ℝ :=
    fun d => ((3 * k d + 2 : ℤ) : ℝ) / (d : ℝ)
  have hcross :
      ∀ d ∈ D, ∀ e ∈ D, lower d ≤ upper e := by
    intro d hd e he
    exact window_band_ratio_bound F hzero d e
      (hpos d hd) (hpos e he)
      (3 * k d + 1) (3 * k d + 2)
      (3 * k e + 1) (3 * k e + 2)
      (hw d hd) (hw e he)
  have hl2 : (1 : ℝ) / 2 ≤ lower 2 := by
    norm_num [lower, hk2]
  have hu3 : upper 3 ≤ (2 : ℝ) / 3 := by
    norm_num [upper, hk3]
  obtain ⟨theta, ht_lo, ht_hi, htheta⟩ :=
    common_slope_from_bounds D h2 h3 lower upper hcross hl2 hu3
  refine ⟨theta, ht_lo, ht_hi, ?_⟩
  intro d hd
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast hpos d hd
  have hlo :
      ((3 * k d + 1 : ℤ) : ℝ) ≤ theta * (d : ℝ) :=
    (div_le_iff₀ hdR).mp (htheta d hd).1
  have hhi :
      theta * (d : ℝ) ≤ ((3 * k d + 2 : ℤ) : ℝ) :=
    (le_div_iff₀ hdR).mp (htheta d hd).2
  push_cast at hlo hhi
  refine ⟨k d, ?_, ?_⟩ <;> nlinarith

end JT96

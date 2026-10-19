import JT96.SlopeFromBands
import JT96.FloorColoring
import JT96.FourColoring

namespace JT96

theorem colorable_three_slopeFeasible
    (D : Set ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (h2 : 2 ∈ D) (h3 : 3 ∈ D)
    (hcol : (distanceGraph D).Colorable 3) :
    SlopeFeasible D := by
  rcases hcol with ⟨c⟩
  obtain ⟨sigma, hsign, hbin⟩ :=
    coloring_binary_increments D h2 h3 c
  let k : ℕ → ℤ := fun d => colorWindow c sigma 0 d / 3

  have hw0 (d : ℕ) :
      colorWindow c sigma 0 d = colorLift c sigma d := by
    simp only [colorWindow, Nat.zero_add, colorLift, sub_zero]

  have hk2 : k 2 = 0 := by
    have hb := colorLift_bounds c sigma hbin 2
    have hz :=
      colorWindow_nonzero D c sigma hsign 0 2 h2 (by decide)
    rw [hw0 2] at hz
    change colorWindow c sigma 0 2 / 3 = 0
    rw [hw0 2]
    omega

  have hk3 : k 3 = 0 := by
    have hb := colorLift_bounds c sigma hbin 3
    have hz :=
      colorWindow_nonzero D c sigma hsign 0 3 h3 (by decide)
    rw [hw0 3] at hz
    change colorWindow c sigma 0 3 / 3 = 0
    rw [hw0 3]
    omega

  apply slope_from_window_bands D hpos h2 h3
    (colorLift c sigma) rfl k hk2 hk3
  intro d hd n
  exact colorWindow_fixed_band D c sigma hsign hbin
    d hd (hpos d hd) n

theorem slope_criterion
    (D : Set ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (h2 : 2 ∈ D) (h3 : 3 ∈ D) :
    (distanceGraph D).Colorable 3 ↔ SlopeFeasible D :=
  ⟨colorable_three_slopeFeasible D hpos h2 h3,
    slopeFeasible_colorable_three D⟩

theorem exampleDistances_not_colorable_three :
    ¬ (distanceGraph exampleDistances).Colorable 3 := by
  intro hcol
  apply exampleDistances_no_slope
  apply colorable_three_slopeFeasible exampleDistances
    (fun d hd => (exampleDistances_prime d hd).pos)
    (by simp [exampleDistances])
    (by simp [exampleDistances])
    hcol

theorem example_four_color_certificate :
    (distanceGraph exampleDistances).Colorable 4 ∧
    ¬ (distanceGraph exampleDistances).Colorable 3 :=
  ⟨exampleDistances_colorable_four,
    exampleDistances_not_colorable_three⟩

end JT96

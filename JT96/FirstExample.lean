import JT96.SixDistanceArithmetic

namespace JT96

def exampleDistances : Set ℕ :=
  {2, 3, 61, 131, 191, 257}

def SlopeFeasible (D : Set ℕ) : Prop :=
  ∃ theta : ℝ,
    1 / 2 ≤ theta ∧ theta ≤ 2 / 3 ∧
    ∀ d ∈ D, AllowedPhase ((d : ℝ) * theta)

theorem exampleDistances_prime :
    ∀ d ∈ exampleDistances, Nat.Prime d := by
  intro d hd
  simp only [exampleDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem exampleDistances_no_slope :
    ¬ SlopeFeasible exampleDistances := by
  rintro ⟨theta, ht_lo, ht_hi, hD⟩
  have h61 := hD 61 (by simp [exampleDistances])
  have h131 := hD 131 (by simp [exampleDistances])
  have h191 := hD 191 (by simp [exampleDistances])
  have h257 := hD 257 (by simp [exampleDistances])
  have hdiv : (3 : ℤ) ∣ 191 := by
    apply six_distance_slope_forces_three_dvd
      191 61 theta ht_lo ht_hi
    · convert h191 using 1 <;> norm_num
    · convert h61 using 1 <;> norm_num
    · convert h257 using 1 <;> norm_num
    · convert h131 using 1 <;> norm_num
  norm_num at hdiv

end JT96

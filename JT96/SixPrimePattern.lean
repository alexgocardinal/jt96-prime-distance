import JT96.ColoringCriterion
import Mathlib.Data.Nat.Prime.Basic

namespace JT96

def sixDistances (p q : ℕ) : Set ℕ :=
  {2, 3, p, q, p + q + 5, p - q + 1}

theorem prime_distance_colorable_four
    (D : Set ℕ) (hprime : ∀ d ∈ D, Nat.Prime d) :
    (distanceGraph D).Colorable 4 := by
  refine ⟨modFourColoring D ?_⟩
  intro d hd
  rcases (hprime d hd).eq_two_or_odd with h | h <;> omega

theorem prime_gt_three_not_dvd
    (p : ℕ) (hp : Nat.Prime p) (hgt : 3 < p) :
    ¬ (3 : ℤ) ∣ (p : ℤ) := by
  intro h
  have hnat : 3 ∣ p := by exact_mod_cast h
  rcases hp.eq_one_or_self_of_dvd 3 hnat with h | h <;> omega

theorem sixDistances_prime
    (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime (p + q + 5))
    (hs : Nat.Prime (p - q + 1)) :
    ∀ d ∈ sixDistances p q, Nat.Prime d := by
  intro d hd
  simp only [sixDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact hp
  · exact hq
  · exact hr
  · exact hs

theorem sixDistances_no_slope
    (p q : ℕ) (hpq : q ≤ p)
    (hp3 : ¬ (3 : ℤ) ∣ (p : ℤ)) :
    ¬ SlopeFeasible (sixDistances p q) := by
  rintro ⟨theta, ht_lo, ht_hi, hD⟩
  have hp := hD p (by simp [sixDistances])
  have hq := hD q (by simp [sixDistances])
  have hr := hD (p + q + 5) (by simp [sixDistances])
  have hs := hD (p - q + 1) (by simp [sixDistances])
  apply hp3
  apply six_distance_slope_forces_three_dvd
    (p : ℤ) (q : ℤ) theta ht_lo ht_hi
  · simpa using hp
  · simpa using hq
  · convert hr using 1 <;> push_cast <;> ring
  · convert hs using 1 <;>
      push_cast [Nat.cast_sub hpq] <;> ring

theorem sixDistances_four_color_certificate
    (p q : ℕ) (hpq : q ≤ p) (hgt : 3 < p)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime (p + q + 5))
    (hs : Nat.Prime (p - q + 1)) :
    (distanceGraph (sixDistances p q)).Colorable 4 ∧
    ¬ (distanceGraph (sixDistances p q)).Colorable 3 := by
  have hprime := sixDistances_prime p q hp hq hr hs
  constructor
  · exact prime_distance_colorable_four _ hprime
  · intro hcol
    apply sixDistances_no_slope p q hpq
      (prime_gt_three_not_dvd p hp hgt)
    exact colorable_three_slopeFeasible _
      (fun d hd => (hprime d hd).pos)
      (by simp [sixDistances])
      (by simp [sixDistances])
      hcol

end JT96

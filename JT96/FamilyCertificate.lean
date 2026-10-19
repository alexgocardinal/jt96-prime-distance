import JT96.ConeGeometry

namespace JT96

def MinimalSixPrimeObstruction (D : Set ℕ) : Prop :=
  D.Finite ∧
  D.ncard = 6 ∧
  (∀ d ∈ D, Nat.Prime d) ∧
  (distanceGraph D).Colorable 4 ∧
  ¬ (distanceGraph D).Colorable 3 ∧
  (∀ E : Set ℕ, E ⊂ D → (distanceGraph E).Colorable 3) ∧
  (∀ a ∈ D, ∀ b ∈ D, a + 2 ≠ b)

def PrimeConePair (p q : ℕ) : Prop :=
  60000 < p ∧
  |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000 ∧
  Nat.Prime p ∧
  Nat.Prime q ∧
  Nat.Prime (p + q + 5) ∧
  Nat.Prime (p - q + 1)

theorem primeConePair_obstruction
    (p q : ℕ) (h : PrimeConePair p q) :
    MinimalSixPrimeObstruction (sixDistances p q) := by
  rcases h with ⟨hpbig, hclose, hp, hq, hr, hs⟩
  obtain ⟨hq10, h3q, h4q⟩ := cone_geometry p q hpbig hclose
  have hpq : q ≤ p := by omega
  have hpgt : 3 < p := by omega
  have hfour :=
    sixDistances_four_color_certificate p q hpq hpgt hp hq hr hs
  refine ⟨sixDistances_finite p q,
    sixDistances_ncard p q hq10 h3q,
    sixDistances_prime p q hp hq hr hs,
    hfour.1, hfour.2, ?_,
    sixDistances_no_twins_of_geometry p q hq10 h3q⟩
  intro E hE
  exact sixDistances_proper_subset_colorable
    p q hpq hpbig hclose hp hq hr hs E hE

/-- External prime-pattern input, stated here but not proved. -/
def PrimePatternInput : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ PrimeConePair p q

end JT96

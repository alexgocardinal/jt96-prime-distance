import JT96.FamilyCertificate
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Lattice.Fold

namespace JT96

theorem infinite_minimal_six_prime_obstructions
    (hprime : PrimePatternInput) :
    {D : Set ℕ | MinimalSixPrimeObstruction D}.Infinite := by
  classical
  let family : Set (Set ℕ) :=
    {D : Set ℕ | MinimalSixPrimeObstruction D}
  change family.Infinite
  intro hf

  have hU : (⋃₀ family).Finite :=
    hf.sUnion (fun D hD => hD.1)

  obtain ⟨p, q, hpN, hpair⟩ :=
    hprime (hU.toFinset.sup id)

  have hD : sixDistances p q ∈ family :=
    primeConePair_obstruction p q hpair

  have hpU : p ∈ ⋃₀ family := by
    apply Set.mem_sUnion.mpr
    exact ⟨sixDistances p q, hD, by simp [sixDistances]⟩

  have hpF : p ∈ hU.toFinset :=
    hU.mem_toFinset.mpr hpU

  have hle : p ≤ hU.toFinset.sup id :=
    Finset.le_sup (f := id) hpF

  omega

end JT96

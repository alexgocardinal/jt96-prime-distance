import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace JT96

/-- Vertices are integers. Distinct vertices are adjacent when
their distance belongs to D. -/
def distanceGraph (D : Set ℕ) : SimpleGraph ℤ where
  Adj u v :=
    u ≠ v ∧
      ∃ d ∈ D, v = u + (d : ℤ) ∨ u = v + (d : ℤ)
  symm := by
    intro u v h
    rcases h with ⟨hne, d, hd, hor⟩
    refine ⟨hne.symm, d, hd, ?_⟩
    rcases hor with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    intro u h
    exact h.1 rfl

end JT96

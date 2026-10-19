import JT96.DistanceGraph
import Mathlib.Tactic

namespace JT96

def signedColorStep (a b : Fin 3) : ℤ :=
  if a = b then 0
  else if b.val = (a.val + 1) % 3 then 1
  else -1

def tripleDirection (a b c : Fin 3) : ℤ :=
  if a = b then signedColorStep b c
  else signedColorStep a b

theorem tripleDirection_nonzero :
    ∀ a b c : Fin 3, a ≠ c →
      tripleDirection a b c = 1 ∨
      tripleDirection a b c = -1 := by
  decide

theorem tripleDirection_controls_step :
    ∀ a b c : Fin 3, a ≠ c →
      signedColorStep a b = 0 ∨
      signedColorStep a b = tripleDirection a b c := by
  decide

theorem tripleDirection_consistent :
    ∀ a b c d : Fin 3,
      a ≠ c → b ≠ d → a ≠ d →
      tripleDirection a b c = tripleDirection b c d := by
  decide

theorem coloring_direction_step
    (D : Set ℕ) (h2 : 2 ∈ D) (h3 : 3 ∈ D)
    (c : (distanceGraph D).Coloring (Fin 3))
    (n : ℤ) :
    tripleDirection (c n) (c (n + 1)) (c (n + 2)) =
      tripleDirection (c (n + 1)) (c (n + 2)) (c (n + 3)) := by
  apply tripleDirection_consistent
  · apply c.valid
    exact ⟨by omega, 2, h2, Or.inl (by omega)⟩
  · apply c.valid
    exact ⟨by omega, 2, h2, Or.inl (by omega)⟩
  · apply c.valid
    exact ⟨by omega, 3, h3, Or.inl (by omega)⟩

end JT96

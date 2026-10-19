import JT96.PhaseBoxHit

namespace JT96

theorem allowedPhase_add_three_mul
    (x : ℝ) (k : ℤ) (hx : AllowedPhase x) :
    AllowedPhase (x + 3 * (k : ℝ)) := by
  rcases hx with ⟨j, hlo, hhi⟩
  refine ⟨j + k, ?_, ?_⟩ <;> push_cast <;> linarith

theorem sixDistances_deletion_from_phases
    (p q : ℕ) (hpq : q ≤ p) (deleted : ℕ)
    (theta alpha beta : ℝ) (a b : ℤ)
    (hp_phase : (p : ℝ) * theta = 3 * (a : ℝ) + alpha)
    (hq_phase : (q : ℝ) * theta = 3 * (b : ℝ) + beta)
    (h2 : 2 ≠ deleted → AllowedPhase (2 * theta))
    (h3 : 3 ≠ deleted → AllowedPhase (3 * theta))
    (hp : p ≠ deleted → AllowedPhase alpha)
    (hq : q ≠ deleted → AllowedPhase beta)
    (hr : p + q + 5 ≠ deleted →
      AllowedPhase (alpha + beta + 5 * theta))
    (hs : p - q + 1 ≠ deleted →
      AllowedPhase (alpha - beta + theta)) :
    (distanceGraph (sixDistances p q \ {deleted})).Colorable 3 := by
  refine ⟨floorColoring
    (sixDistances p q \ {deleted}) theta ?_⟩
  intro d hd
  have hmem := hd.1
  have hne : d ≠ deleted := by simpa using hd.2
  simp only [sixDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using h2 hne
  · simpa using h3 hne
  · have h := allowedPhase_add_three_mul alpha a (hp hne)
    convert h using 1 <;> linarith only [hp_phase]
  · have h := allowedPhase_add_three_mul beta b (hq hne)
    convert h using 1 <;> linarith only [hq_phase]
  · have h := allowedPhase_add_three_mul
      (alpha + beta + 5 * theta) (a + b) (hr hne)
    convert h using 1 <;> push_cast <;>
      nlinarith only [hp_phase, hq_phase]
  · have h := allowedPhase_add_three_mul
      (alpha - beta + theta) (a - b) (hs hne)
    convert h using 1 <;>
      push_cast [Nat.cast_sub hpq] <;>
      nlinarith only [hp_phase, hq_phase]

end JT96

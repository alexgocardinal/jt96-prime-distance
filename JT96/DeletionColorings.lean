import JT96.FloorColoring

namespace JT96

def deletionNumerator : ℕ → ℕ
  | 2 => 3
  | 3 => 1
  | 61 => 139
  | 131 => 31
  | 191 => 133
  | 257 => 67
  | _ => 0

def deletionDenominator : ℕ → ℕ
  | 2 => 2
  | 3 => 1
  | 61 => 257
  | 131 => 61
  | 191 => 257
  | 257 => 131
  | _ => 1

noncomputable def deletionSlope (deleted : ℕ) : ℝ :=
  (deletionNumerator deleted : ℝ) /
    (deletionDenominator deleted : ℝ)

theorem deletionSlope_allowed
    (deleted d : ℕ)
    (hdel : deleted ∈ exampleDistances)
    (hd : d ∈ exampleDistances)
    (hne : d ≠ deleted) :
    AllowedPhase ((d : ℝ) * deletionSlope deleted) := by
  refine ⟨
    (((d * deletionNumerator deleted) /
      (3 * deletionDenominator deleted) : ℕ) : ℤ),
    ?_, ?_⟩
  all_goals
    simp only [exampleDistances, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hdel hd
    rcases hdel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [deletionSlope, deletionNumerator,
        deletionDenominator] at hne ⊢

theorem example_single_deletion_colorable
    (deleted : ℕ) (hdel : deleted ∈ exampleDistances) :
    (distanceGraph (exampleDistances \ {deleted})).Colorable 3 := by
  refine ⟨floorColoring
    (exampleDistances \ {deleted}) (deletionSlope deleted) ?_⟩
  intro d hd
  exact deletionSlope_allowed deleted d hdel hd.1
    (by simpa using hd.2)

end JT96

import JT96.DeletionColorings

namespace JT96

theorem distanceGraph_colorable_of_subset
    {D E : Set ℕ} {k : ℕ}
    (hsub : E ⊆ D)
    (hcol : (distanceGraph D).Colorable k) :
    (distanceGraph E).Colorable k := by
  rcases hcol with ⟨c⟩
  refine ⟨SimpleGraph.Coloring.mk (fun v => c v) ?_⟩
  intro u v huv
  apply c.valid
  rcases huv with ⟨hne, d, hd, hstep⟩
  exact ⟨hne, d, hsub hd, hstep⟩

theorem example_proper_subset_colorable
    (E : Set ℕ) (hE : E ⊂ exampleDistances) :
    (distanceGraph E).Colorable 3 := by
  obtain ⟨deleted, hdel, hnot⟩ := Set.exists_of_ssubset hE
  have hsub : E ⊆ exampleDistances \ {deleted} := by
    intro d hd
    refine ⟨hE.le hd, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    exact hnot (he ▸ hd)
  exact distanceGraph_colorable_of_subset hsub
    (example_single_deletion_colorable deleted hdel)

theorem exampleDistances_no_twins :
    ∀ a ∈ exampleDistances,
    ∀ b ∈ exampleDistances, a + 2 ≠ b := by
  intro a ha b hb
  simp only [exampleDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

end JT96

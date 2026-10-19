import JT96.DistanceGraph
import JT96.FirstExample

namespace JT96

def modFourColor (n : ℤ) : Fin 4 :=
  ⟨(n % 4).toNat, by omega⟩

def modFourColoring
    (D : Set ℕ)
    (hD : ∀ d ∈ D, d % 4 ≠ 0) :
    (distanceGraph D).Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk modFourColor (by
    intro u v h heq
    have hval := congrArg Fin.val heq
    change (u % 4).toNat = (v % 4).toNat at hval
    rcases h with ⟨_, d, hd, hstep⟩
    have hd4 := hD d hd
    rcases hstep with hstep | hstep <;> omega)

theorem exampleDistances_colorable_four :
    (distanceGraph exampleDistances).Colorable 4 := by
  refine ⟨modFourColoring exampleDistances ?_⟩
  intro d hd
  simp only [exampleDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end JT96

import JT96.DistanceGraph
import JT96.FirstExample
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring

namespace JT96

theorem floor_phase_different
    (x y : ℝ) (h : AllowedPhase (y - x)) :
    Int.floor x % 3 ≠ Int.floor y % 3 := by
  rcases h with ⟨k, hk_lo, hk_hi⟩
  have hx_lo := Int.floor_le x
  have hx_hi := Int.lt_floor_add_one x
  have hy_lo := Int.floor_le y
  have hy_hi := Int.lt_floor_add_one y
  have hlo :
      3 * (k : ℝ) <
        (Int.floor y : ℝ) - (Int.floor x : ℝ) := by
    linarith
  have hhi :
      (Int.floor y : ℝ) - (Int.floor x : ℝ) <
        3 * (k : ℝ) + 3 := by
    linarith
  have hlo' : 3 * k < Int.floor y - Int.floor x := by
    exact_mod_cast hlo
  have hhi' : Int.floor y - Int.floor x < 3 * k + 3 := by
    exact_mod_cast hhi
  intro heq
  omega

noncomputable def floorColor (theta : ℝ) (n : ℤ) : Fin 3 :=
  ⟨(Int.floor ((n : ℝ) * theta) % 3).toNat, by omega⟩

noncomputable def floorColoring
    (D : Set ℕ) (theta : ℝ)
    (hD : ∀ d ∈ D, AllowedPhase ((d : ℝ) * theta)) :
    (distanceGraph D).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (floorColor theta) (by
    intro u v h heq
    have hval := congrArg Fin.val heq
    change
      (Int.floor ((u : ℝ) * theta) % 3).toNat =
      (Int.floor ((v : ℝ) * theta) % 3).toNat at hval
    have hres :
        Int.floor ((u : ℝ) * theta) % 3 =
        Int.floor ((v : ℝ) * theta) % 3 := by
      omega
    rcases h with ⟨_, d, hd, hstep⟩
    rcases hstep with hstep | hstep
    · have hx :
          AllowedPhase ((v : ℝ) * theta - (u : ℝ) * theta) := by
        convert hD d hd using 1 <;>
          rw [hstep] <;> push_cast <;> ring
      exact (floor_phase_different _ _ hx) hres
    · have hx :
          AllowedPhase ((u : ℝ) * theta - (v : ℝ) * theta) := by
        convert hD d hd using 1 <;>
          rw [hstep] <;> push_cast <;> ring
      exact (floor_phase_different _ _ hx) hres.symm)

theorem slopeFeasible_colorable_three
    (D : Set ℕ) (h : SlopeFeasible D) :
    (distanceGraph D).Colorable 3 := by
  rcases h with ⟨theta, _, _, hD⟩
  exact ⟨floorColoring D theta hD⟩

end JT96

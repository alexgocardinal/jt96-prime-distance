import JT96.ColorSteps

namespace JT96

theorem integer_step_constant
    {A : Type*} (f : ℤ → A)
    (hf : ∀ n, f n = f (n + 1))
    (n : ℤ) :
    f n = f 0 := by
  refine n.inductionOn' 0 rfl ?_ ?_
  · intro k _ ih
    exact (hf k).symm.trans ih
  · intro k _ ih
    calc
      f (k - 1) = f k := by simpa using hf (k - 1)
      _ = f 0 := ih

theorem coloring_uniform_direction
    (D : Set ℕ) (h2 : 2 ∈ D) (h3 : 3 ∈ D)
    (c : (distanceGraph D).Coloring (Fin 3)) :
    ∃ sigma : ℤ,
      (sigma = 1 ∨ sigma = -1) ∧
      ∀ n : ℤ,
        signedColorStep (c n) (c (n + 1)) = 0 ∨
        signedColorStep (c n) (c (n + 1)) = sigma := by
  let sigma := tripleDirection (c 0) (c 1) (c 2)
  have h02 : c 0 ≠ c 2 := by
    apply c.valid
    exact ⟨by omega, 2, h2, Or.inl (by omega)⟩
  refine ⟨sigma, ?_, ?_⟩
  · exact tripleDirection_nonzero (c 0) (c 1) (c 2) h02
  · intro n
    have hn2 : c n ≠ c (n + 2) := by
      apply c.valid
      exact ⟨by omega, 2, h2, Or.inl (by omega)⟩
    have hcontrol :=
      tripleDirection_controls_step
        (c n) (c (n + 1)) (c (n + 2)) hn2
    have hconstant :
        tripleDirection (c n) (c (n + 1)) (c (n + 2)) =
          sigma := by
      exact integer_step_constant
        (fun j => tripleDirection
          (c j) (c (j + 1)) (c (j + 2)))
        (fun j => by
          simpa [add_assoc] using
            coloring_direction_step D h2 h3 c j) n
    rcases hcontrol with hz | hs
    · exact Or.inl hz
    · exact Or.inr (hs.trans hconstant)

theorem coloring_binary_increments
    (D : Set ℕ) (h2 : 2 ∈ D) (h3 : 3 ∈ D)
    (c : (distanceGraph D).Coloring (Fin 3)) :
    ∃ sigma : ℤ,
      (sigma = 1 ∨ sigma = -1) ∧
      ∀ n : ℤ,
        sigma * signedColorStep (c n) (c (n + 1)) = 0 ∨
        sigma * signedColorStep (c n) (c (n + 1)) = 1 := by
  obtain ⟨sigma, hsign, hsteps⟩ :=
    coloring_uniform_direction D h2 h3 c
  refine ⟨sigma, hsign, ?_⟩
  intro n
  rcases hsteps n with hz | hs
  · left
    simp [hz]
  · right
    rw [hs]
    rcases hsign with rfl | rfl <;> norm_num

end JT96

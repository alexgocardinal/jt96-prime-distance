import JT96.LocalSumBounds

namespace JT96

def colorLift (c : ℤ → Fin 3) (sigma : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      colorLift c sigma n +
        sigma * signedColorStep (c (n : ℤ)) (c ((n : ℤ) + 1))

theorem colorLift_mod_three
    (c : ℤ → Fin 3) (sigma : ℤ)
    (hsign : sigma = 1 ∨ sigma = -1)
    (n : ℕ) :
    colorLift c sigma n % 3 =
      (sigma * ((c (n : ℤ)).val : ℤ) -
        sigma * ((c 0).val : ℤ)) % 3 := by
  rcases hsign with rfl | rfl
  · induction n with
    | zero =>
        simp [colorLift]
    | succ n ih =>
        have hs := signedColorStep_mod_three
          (c (n : ℤ)) (c ((n : ℤ) + 1))
        simp only [colorLift, Nat.cast_succ, one_mul] at *
        omega
  · induction n with
    | zero =>
        simp [colorLift]
    | succ n ih =>
        have hs := signedColorStep_mod_three
          (c (n : ℤ)) (c ((n : ℤ) + 1))
        simp only [colorLift, Nat.cast_succ, neg_one_mul] at *
        omega

theorem colorLift_step_bounds
    (c : ℤ → Fin 3) (sigma : ℤ)
    (hbin : ∀ n : ℤ,
      sigma * signedColorStep (c n) (c (n + 1)) = 0 ∨
      sigma * signedColorStep (c n) (c (n + 1)) = 1)
    (n : ℕ) :
    colorLift c sigma n ≤ colorLift c sigma (n + 1) ∧
    colorLift c sigma (n + 1) ≤ colorLift c sigma n + 1 := by
  have h := hbin (n : ℤ)
  simp only [colorLift]
  rcases h with h | h <;> omega

theorem colorLift_bounds
    (c : ℤ → Fin 3) (sigma : ℤ)
    (hbin : ∀ n : ℤ,
      sigma * signedColorStep (c n) (c (n + 1)) = 0 ∨
      sigma * signedColorStep (c n) (c (n + 1)) = 1)
    (n : ℕ) :
    0 ≤ colorLift c sigma n ∧
    colorLift c sigma n ≤ (n : ℤ) := by
  induction n with
  | zero =>
      simp [colorLift]
  | succ n ih =>
      have hh := colorLift_step_bounds c sigma hbin n
      simp only [Nat.cast_succ]
      omega

end JT96

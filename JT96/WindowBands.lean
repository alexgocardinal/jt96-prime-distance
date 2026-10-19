import JT96.ColorLift

namespace JT96

def colorWindow
    (c : ℤ → Fin 3) (sigma : ℤ) (n d : ℕ) : ℤ :=
  colorLift c sigma (n + d) - colorLift c sigma n

theorem colorWindow_nonzero
    (D : Set ℕ)
    (c : (distanceGraph D).Coloring (Fin 3))
    (sigma : ℤ) (hsign : sigma = 1 ∨ sigma = -1)
    (n d : ℕ) (hd : d ∈ D) (hdpos : 0 < d) :
    colorWindow c sigma n d % 3 ≠ 0 := by
  have hneq : c (n : ℤ) ≠ c ((n + d : ℕ) : ℤ) := by
    apply c.valid
    exact ⟨by omega, d, hd, Or.inl (by omega)⟩
  have hn := colorLift_mod_three c sigma hsign n
  have hnd := colorLift_mod_three c sigma hsign (n + d)
  have hbn := (c (n : ℤ)).isLt
  have hbnd := (c ((n + d : ℕ) : ℤ)).isLt
  intro hz
  apply hneq
  apply Fin.ext
  dsimp [colorWindow] at hz
  rcases hsign with rfl | rfl <;>
    simp only [one_mul, neg_one_mul] at hn hnd <;>
    omega

theorem colorWindow_step_bounds
    (c : ℤ → Fin 3) (sigma : ℤ)
    (hbin : ∀ n : ℤ,
      sigma * signedColorStep (c n) (c (n + 1)) = 0 ∨
      sigma * signedColorStep (c n) (c (n + 1)) = 1)
    (n d : ℕ) :
    colorWindow c sigma n d - 1 ≤
      colorWindow c sigma (n + 1) d ∧
    colorWindow c sigma (n + 1) d ≤
      colorWindow c sigma n d + 1 := by
  have h0 := colorLift_step_bounds c sigma hbin n
  have hd := colorLift_step_bounds c sigma hbin (n + d)
  have hidx : n + 1 + d = (n + d) + 1 := by omega
  dsimp [colorWindow]
  rw [hidx]
  omega

theorem adjacent_nonzero_same_band
    (a b : ℤ)
    (ha : a % 3 ≠ 0) (hb : b % 3 ≠ 0)
    (hlo : a - 1 ≤ b) (hhi : b ≤ a + 1) :
    a / 3 = b / 3 := by
  omega

theorem colorWindow_band_constant
    (D : Set ℕ)
    (c : (distanceGraph D).Coloring (Fin 3))
    (sigma : ℤ) (hsign : sigma = 1 ∨ sigma = -1)
    (hbin : ∀ n : ℤ,
      sigma * signedColorStep (c n) (c (n + 1)) = 0 ∨
      sigma * signedColorStep (c n) (c (n + 1)) = 1)
    (d : ℕ) (hd : d ∈ D) (hdpos : 0 < d)
    (n : ℕ) :
    colorWindow c sigma n d / 3 =
      colorWindow c sigma 0 d / 3 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hs := colorWindow_step_bounds c sigma hbin n d
      have ha := colorWindow_nonzero D c sigma hsign n d hd hdpos
      have hb :=
        colorWindow_nonzero D c sigma hsign (n + 1) d hd hdpos
      have he := adjacent_nonzero_same_band
        (colorWindow c sigma n d)
        (colorWindow c sigma (n + 1) d)
        ha hb hs.1 hs.2
      exact he.symm.trans ih

theorem colorWindow_fixed_band
    (D : Set ℕ)
    (c : (distanceGraph D).Coloring (Fin 3))
    (sigma : ℤ) (hsign : sigma = 1 ∨ sigma = -1)
    (hbin : ∀ n : ℤ,
      sigma * signedColorStep (c n) (c (n + 1)) = 0 ∨
      sigma * signedColorStep (c n) (c (n + 1)) = 1)
    (d : ℕ) (hd : d ∈ D) (hdpos : 0 < d)
    (n : ℕ) :
    3 * (colorWindow c sigma 0 d / 3) + 1 ≤
      colorWindow c sigma n d ∧
    colorWindow c sigma n d ≤
      3 * (colorWindow c sigma 0 d / 3) + 2 := by
  have hb :=
    colorWindow_band_constant D c sigma hsign hbin d hd hdpos n
  have hn := colorWindow_nonzero D c sigma hsign n d hd hdpos
  omega

end JT96

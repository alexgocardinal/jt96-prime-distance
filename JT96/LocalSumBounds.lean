import JT96.UniformDirection

namespace JT96

theorem signedColorStep_mod_three :
    ∀ a b : Fin 3,
      signedColorStep a b % 3 =
        ((b.val : ℤ) - (a.val : ℤ)) % 3 := by
  decide

theorem normalized_pair_bounds
    (a b c : Fin 3) (sigma : ℤ)
    (hsign : sigma = 1 ∨ sigma = -1)
    (h1 : sigma * signedColorStep a b = 0 ∨
          sigma * signedColorStep a b = 1)
    (h2 : sigma * signedColorStep b c = 0 ∨
          sigma * signedColorStep b c = 1)
    (hac : a ≠ c) :
    1 ≤ sigma * signedColorStep a b +
          sigma * signedColorStep b c ∧
    sigma * signedColorStep a b +
      sigma * signedColorStep b c ≤ 2 := by
  rcases hsign with rfl | rfl <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [signedColorStep] at *

theorem normalized_triple_bounds
    (a b c d : Fin 3) (sigma : ℤ)
    (hsign : sigma = 1 ∨ sigma = -1)
    (h1 : sigma * signedColorStep a b = 0 ∨
          sigma * signedColorStep a b = 1)
    (h2 : sigma * signedColorStep b c = 0 ∨
          sigma * signedColorStep b c = 1)
    (h3 : sigma * signedColorStep c d = 0 ∨
          sigma * signedColorStep c d = 1)
    (had : a ≠ d) :
    1 ≤ sigma * signedColorStep a b +
          sigma * signedColorStep b c +
          sigma * signedColorStep c d ∧
    sigma * signedColorStep a b +
      sigma * signedColorStep b c +
      sigma * signedColorStep c d ≤ 2 := by
  rcases hsign with rfl | rfl <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> norm_num [signedColorStep] at *

end JT96

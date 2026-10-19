import JT96.SixPrimePattern

namespace JT96

theorem delete_p_phase_box
    (theta beta : ℝ)
    (ht1 : 1199 / 2000 < theta)
    (ht2 : theta < 1201 / 2000)
    (hb1 : 171 / 100 < beta)
    (hb2 : beta < 189 / 100) :
    (1 / 2 ≤ theta ∧ theta ≤ 2 / 3) ∧
    AllowedPhase (2 * theta) ∧
    AllowedPhase (3 * theta) ∧
    AllowedPhase beta ∧
    AllowedPhase (1 / 10 + beta + 5 * theta) ∧
    AllowedPhase (1 / 10 - beta + theta) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩,
    ⟨1, ?_, ?_⟩, ⟨-1, ?_, ?_⟩⟩ <;>
    norm_num <;> linarith

theorem delete_q_phase_box
    (theta beta : ℝ)
    (ht1 : 599 / 1000 < theta)
    (ht2 : theta < 601 / 1000)
    (hb1 : 1 / 4 < beta)
    (hb2 : beta < 3 / 4) :
    (1 / 2 ≤ theta ∧ theta ≤ 2 / 3) ∧
    AllowedPhase (2 * theta) ∧
    AllowedPhase (3 * theta) ∧
    AllowedPhase (6 / 5) ∧
    AllowedPhase (6 / 5 + beta + 5 * theta) ∧
    AllowedPhase (6 / 5 - beta + theta) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩,
    ⟨1, ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩ <;>
    norm_num <;> linarith

theorem delete_r_phase_box
    (theta beta : ℝ)
    (ht1 : 599 / 1000 < theta)
    (ht2 : theta < 601 / 1000)
    (hb1 : 21 / 20 < beta)
    (hb2 : beta < 27 / 20) :
    (1 / 2 ≤ theta ∧ theta ≤ 2 / 3) ∧
    AllowedPhase (2 * theta) ∧
    AllowedPhase (3 * theta) ∧
    AllowedPhase (9 / 5) ∧
    AllowedPhase beta ∧
    AllowedPhase (9 / 5 - beta + theta) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩,
    ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩ <;>
    norm_num <;> linarith

theorem delete_s_phase_box
    (theta beta : ℝ)
    (ht1 : 509 / 1000 < theta)
    (ht2 : theta < 511 / 1000)
    (hb1 : 21 / 20 < beta)
    (hb2 : beta < 13 / 10) :
    (1 / 2 ≤ theta ∧ theta ≤ 2 / 3) ∧
    AllowedPhase (2 * theta) ∧
    AllowedPhase (3 * theta) ∧
    AllowedPhase (11 / 10) ∧
    AllowedPhase beta ∧
    AllowedPhase (11 / 10 + beta + 5 * theta) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩,
    ⟨0, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩ <;>
    norm_num <;> linarith

end JT96

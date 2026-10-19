import JT96.PhaseTransport

namespace JT96

theorem sixDistances_delete_p
    (p q : ℕ) (hpq : q ≤ p) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000) :
    (distanceGraph (sixDistances p q \ {p})).Colorable 3 := by
  have hpR : (60000 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpbig
  obtain ⟨theta, a, b, ht1, ht2, hpa, hb1, hb2⟩ :=
    phase_box_hit (p : ℝ) (q : ℝ) (1 / 10)
      (1199 / 2000) (1201 / 2000) (171 / 100) (189 / 100)
      hpR (by norm_num) (by norm_num) hclose
  let beta : ℝ := (q : ℝ) * theta - 3 * (b : ℝ)
  obtain ⟨_, h2, h3, hq, hr, hs⟩ :=
    delete_p_phase_box theta beta ht1 ht2 hb1 hb2
  refine sixDistances_deletion_from_phases
    p q hpq (p) theta (1 / 10) beta a b hpa
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [beta]
    ring
  · intro _
    exact h2
  · intro _
    exact h3
  · intro hne
    exact (hne rfl).elim
  · intro _
    exact hq
  · intro _
    exact hr
  · intro _
    exact hs

theorem sixDistances_delete_q
    (p q : ℕ) (hpq : q ≤ p) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000) :
    (distanceGraph (sixDistances p q \ {q})).Colorable 3 := by
  have hpR : (60000 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpbig
  obtain ⟨theta, a, b, ht1, ht2, hpa, hb1, hb2⟩ :=
    phase_box_hit (p : ℝ) (q : ℝ) (6 / 5)
      (599 / 1000) (601 / 1000) (1 / 4) (3 / 4)
      hpR (by norm_num) (by norm_num) hclose
  let beta : ℝ := (q : ℝ) * theta - 3 * (b : ℝ)
  obtain ⟨_, h2, h3, hp, hr, hs⟩ :=
    delete_q_phase_box theta beta ht1 ht2 hb1 hb2
  refine sixDistances_deletion_from_phases
    p q hpq (q) theta (6 / 5) beta a b hpa
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [beta]
    ring
  · intro _
    exact h2
  · intro _
    exact h3
  · intro _
    exact hp
  · intro hne
    exact (hne rfl).elim
  · intro _
    exact hr
  · intro _
    exact hs

theorem sixDistances_delete_r
    (p q : ℕ) (hpq : q ≤ p) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000) :
    (distanceGraph (sixDistances p q \ {p + q + 5})).Colorable 3 := by
  have hpR : (60000 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpbig
  obtain ⟨theta, a, b, ht1, ht2, hpa, hb1, hb2⟩ :=
    phase_box_hit (p : ℝ) (q : ℝ) (9 / 5)
      (599 / 1000) (601 / 1000) (21 / 20) (27 / 20)
      hpR (by norm_num) (by norm_num) hclose
  let beta : ℝ := (q : ℝ) * theta - 3 * (b : ℝ)
  obtain ⟨_, h2, h3, hp, hq, hs⟩ :=
    delete_r_phase_box theta beta ht1 ht2 hb1 hb2
  refine sixDistances_deletion_from_phases
    p q hpq (p + q + 5) theta (9 / 5) beta a b hpa
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [beta]
    ring
  · intro _
    exact h2
  · intro _
    exact h3
  · intro _
    exact hp
  · intro _
    exact hq
  · intro hne
    exact (hne rfl).elim
  · intro _
    exact hs

theorem sixDistances_delete_s
    (p q : ℕ) (hpq : q ≤ p) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000) :
    (distanceGraph (sixDistances p q \ {p - q + 1})).Colorable 3 := by
  have hpR : (60000 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpbig
  obtain ⟨theta, a, b, ht1, ht2, hpa, hb1, hb2⟩ :=
    phase_box_hit (p : ℝ) (q : ℝ) (11 / 10)
      (509 / 1000) (511 / 1000) (21 / 20) (13 / 10)
      hpR (by norm_num) (by norm_num) hclose
  let beta : ℝ := (q : ℝ) * theta - 3 * (b : ℝ)
  obtain ⟨_, h2, h3, hp, hq, hr⟩ :=
    delete_s_phase_box theta beta ht1 ht2 hb1 hb2
  refine sixDistances_deletion_from_phases
    p q hpq (p - q + 1) theta (11 / 10) beta a b hpa
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [beta]
    ring
  · intro _
    exact h2
  · intro _
    exact h3
  · intro _
    exact hp
  · intro _
    exact hq
  · intro _
    exact hr
  · intro hne
    exact (hne rfl).elim

end JT96

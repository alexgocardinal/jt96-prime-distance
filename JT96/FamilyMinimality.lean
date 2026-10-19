import JT96.VariableDeletions
import JT96.ProperSubsets

namespace JT96

theorem odd_distance_allowed
    (d : ℕ) (hodd : d % 2 = 1) :
    AllowedPhase ((d : ℝ) * (3 / 2)) := by
  have hoddI : (d : ℤ) % 2 = 1 := by omega
  have heq : (d : ℤ) = 2 * ((d : ℤ) / 2) + 1 := by omega
  have heqR :
      (d : ℝ) = 2 * (((d : ℤ) / 2 : ℤ) : ℝ) + 1 := by
    exact_mod_cast heq
  refine ⟨(d : ℤ) / 2, ?_, ?_⟩ <;>
    nlinarith only [heqR]

theorem integer_allowed_of_mod_three
    (d : ℤ) (hd : d % 3 ≠ 0) :
    AllowedPhase (d : ℝ) := by
  have hb :
      3 * (d / 3) + 1 ≤ d ∧ d ≤ 3 * (d / 3) + 2 := by
    omega
  refine ⟨d / 3, ?_, ?_⟩
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

theorem prime_set_delete_two_colorable
    (D : Set ℕ) (hprime : ∀ d ∈ D, Nat.Prime d) :
    (distanceGraph (D \ {2})).Colorable 3 := by
  refine ⟨floorColoring (D \ {2}) (3 / 2) ?_⟩
  intro d hd
  have hne : d ≠ 2 := by simpa using hd.2
  exact odd_distance_allowed d
    ((hprime d hd.1).eq_two_or_odd.resolve_left hne)

theorem prime_set_delete_three_colorable
    (D : Set ℕ) (hprime : ∀ d ∈ D, Nat.Prime d) :
    (distanceGraph (D \ {3})).Colorable 3 := by
  refine ⟨floorColoring (D \ {3}) 1 ?_⟩
  intro d hd
  have hne : d ≠ 3 := by simpa using hd.2
  have hm : (d : ℤ) % 3 ≠ 0 := by
    intro hz
    have hi : (3 : ℤ) ∣ (d : ℤ) :=
      Int.dvd_iff_emod_eq_zero.mpr hz
    have hn : 3 ∣ d := by exact_mod_cast hi
    rcases (hprime d hd.1).eq_one_or_self_of_dvd 3 hn
      with h | h <;> omega
  simpa using integer_allowed_of_mod_three (d : ℤ) hm

theorem sixDistances_single_deletion_colorable
    (p q : ℕ) (hpq : q ≤ p) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime (p + q + 5))
    (hs : Nat.Prime (p - q + 1))
    (deleted : ℕ) (hdel : deleted ∈ sixDistances p q) :
    (distanceGraph (sixDistances p q \ {deleted})).Colorable 3 := by
  have hprime := sixDistances_prime p q hp hq hr hs
  simp only [sixDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hdel
  rcases hdel with h | h | h | h | h | h
  · subst deleted
    exact prime_set_delete_two_colorable _ hprime
  · subst deleted
    exact prime_set_delete_three_colorable _ hprime
  · subst deleted
    exact sixDistances_delete_p p q hpq hpbig hclose
  · subst deleted
    exact sixDistances_delete_q p q hpq hpbig hclose
  · subst deleted
    exact sixDistances_delete_r p q hpq hpbig hclose
  · subst deleted
    exact sixDistances_delete_s p q hpq hpbig hclose

theorem sixDistances_proper_subset_colorable
    (p q : ℕ) (hpq : q ≤ p) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime (p + q + 5))
    (hs : Nat.Prime (p - q + 1))
    (E : Set ℕ) (hE : E ⊂ sixDistances p q) :
    (distanceGraph E).Colorable 3 := by
  obtain ⟨deleted, hdel, hnot⟩ := Set.exists_of_ssubset hE
  have hsub : E ⊆ sixDistances p q \ {deleted} := by
    intro d hd
    refine ⟨hE.le hd, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    exact hnot (he ▸ hd)
  exact distanceGraph_colorable_of_subset hsub
    (sixDistances_single_deletion_colorable
      p q hpq hpbig hclose hp hq hr hs deleted hdel)

end JT96

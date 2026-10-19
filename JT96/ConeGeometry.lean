import JT96.FamilyMinimality
import Mathlib.Data.Set.Card

namespace JT96

theorem cone_geometry
    (p q : ℕ) (hpbig : 60000 < p)
    (hclose : |(q : ℝ) / (p : ℝ) - 5 / 18| < 1 / 20000) :
    10 < q ∧ 3 * q < p ∧ p < 4 * q := by
  have hpR : (60000 : ℝ) < (p : ℝ) := by
    exact_mod_cast hpbig
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hclose
  have hl :
      (5 / 18 - 1 / 20000 : ℝ) * (p : ℝ) < (q : ℝ) :=
    (lt_div_iff₀ hp0).mp (by linarith)
  have hu :
      (q : ℝ) < (5 / 18 + 1 / 20000 : ℝ) * (p : ℝ) :=
    (div_lt_iff₀ hp0).mp (by linarith)
  have hqR : (10 : ℝ) < (q : ℝ) := by
    linarith only [hl, hpR]
  have h3R : 3 * (q : ℝ) < (p : ℝ) := by
    linarith only [hu, hp0]
  have h4R : (p : ℝ) < 4 * (q : ℝ) := by
    linarith only [hl, hp0]
  exact ⟨by exact_mod_cast hqR,
    by exact_mod_cast h3R, by exact_mod_cast h4R⟩

theorem sixDistances_no_twins_of_geometry
    (p q : ℕ) (hq10 : 10 < q) (h3q : 3 * q < p) :
    ∀ a ∈ sixDistances p q,
    ∀ b ∈ sixDistances p q, a + 2 ≠ b := by
  intro a ha b hb
  simp only [sixDistances, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

theorem sixDistances_finite (p q : ℕ) :
    (sixDistances p q).Finite := by
  unfold sixDistances
  have h0 : ({p - q + 1} : Set ℕ).Finite :=
    Set.finite_singleton _
  have h1 := h0.insert (p + q + 5)
  have h2 := h1.insert q
  have h3 := h2.insert p
  have h4 := h3.insert 3
  exact h4.insert 2

theorem sixDistances_ncard
    (p q : ℕ) (hq10 : 10 < q) (h3q : 3 * q < p) :
    (sixDistances p q).ncard = 6 := by
  have hp :
      p ∉ ({p + q + 5} : Set ℕ) := by
    simp only [Set.mem_singleton_iff]
    omega
  have hs :
      p - q + 1 ∉ ({p, p + q + 5} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hq :
      q ∉ ({p - q + 1, p, p + q + 5} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have h3 :
      3 ∉ ({q, p - q + 1, p, p + q + 5} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have h2 :
      2 ∉ ({3, q, p - q + 1, p, p + q + 5} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hset :
      sixDistances p q =
        ({2, 3, q, p - q + 1, p, p + q + 5} : Set ℕ) := by
    ext d
    simp only [sixDistances, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  rw [hset, Set.ncard_insert_of_not_mem h2,
    Set.ncard_insert_of_not_mem h3,
    Set.ncard_insert_of_not_mem hq,
    Set.ncard_insert_of_not_mem hs,
    Set.ncard_insert_of_not_mem hp,
    Set.ncard_singleton]

end JT96

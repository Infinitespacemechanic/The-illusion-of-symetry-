import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

-- Standalone. No stepS needed.
def stepU (n : ℤ) : ℤ := if Even n then n + 3 else n + 1
def stepU_inv (m : ℤ) : ℤ := if Even m then m - 1 else m - 3

private lemma even_one : ¬ Even (1 : ℤ) := by decide
private lemma even_three : ¬ Even (3 : ℤ) := by decide
private lemma even_neg_one : ¬ Even (-1 : ℤ) := by decide
private lemma even_neg_three : ¬ Even (-3 : ℤ) := by decide

private lemma even_add_one_iff (n : ℤ) : Even (n + 1) ↔ ¬ Even n := by
  rw [Int.even_add]; simp [even_one]

private lemma even_add_three_iff (n : ℤ) : Even (n + 3) ↔ ¬ Even n := by
  rw [Int.even_add]; simp [even_three]

private lemma even_sub_one_iff (n : ℤ) : Even (n - 1) ↔ ¬ Even n := by
  have : n - 1 = n + (-1) := by ring
  rw [this, Int.even_add]; simp [even_neg_one]

private lemma even_sub_three_iff (n : ℤ) : Even (n - 3) ↔ ¬ Even n := by
  have : n - 3 = n + (-3) := by ring
  rw [this, Int.even_add]; simp [even_neg_three]

theorem stepU_two_step (n : ℤ) : stepU (stepU n) = n + 4 := by
  by_cases h : Even n
  · have h1 : ¬ Even (n + 3) := by rwa [even_add_three_iff]
    unfold stepU; simp [h, h1]; ring
  · have h1 : Even (n + 1) := (even_add_one_iff n).mpr h
    unfold stepU; simp [h, h1]; ring

theorem stepU_inv_two_step (m : ℤ) : stepU_inv (stepU_inv m) = m - 4 := by
  by_cases h : Even m
  · have h1 : ¬ Even (m - 1) := by rwa [even_sub_one_iff]
    unfold stepU_inv; simp [h, h1]; ring
  · have h1 : Even (m - 3) := (even_sub_three_iff m).mpr h
    unfold stepU_inv; simp [h, h1]; ring

theorem stepU_inv_leftInv (n : ℤ) : stepU_inv (stepU n) = n := by
  by_cases h : Even n
  · have h1 : ¬ Even (n + 3) := by rwa [even_add_three_iff]
    unfold stepU stepU_inv; simp [h, h1]
  · have h1 : Even (n + 1) := (even_add_one_iff n).mpr h
    unfold stepU stepU_inv; simp [h, h1]

theorem stepU_rightInv (m : ℤ) : stepU (stepU_inv m) = m := by
  by_cases h : Even m
  · have h1 : ¬ Even (m - 1) := by rwa [even_sub_one_iff]
    unfold stepU stepU_inv; simp [h, h1]; ring
  · have h1 : Even (m - 3) := (even_sub_three_iff m).mpr h
    unfold stepU stepU_inv; simp [h, h1]; ring

-- uniqueness you stated
theorem stepU_pred_unique {p m : ℤ} (hm : stepU p = m) : p = stepU_inv m := by
  have : stepU_inv (stepU p) = stepU_inv m := by rw [hm]
  rwa [stepU_inv_leftInv] at this
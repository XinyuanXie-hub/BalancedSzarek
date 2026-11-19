module
public import BalancedSzarek.Definitions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section

open scoped BigOperators

namespace BalancedSzarek

private lemma swap_apply_add {n : ℕ} (b : Fin n → ℝ) (i j k : Fin n) :
    b (Equiv.swap i j k) = b k +
      (if k = i then b j - b i else 0) +
      (if k = j then b i - b j else 0) := by
  by_cases hik : k = i
  · subst k
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  · by_cases hjk : k = j
    · subst k
      simp [hik]
    · rw [Equiv.swap_apply_of_ne_of_ne hik hjk]
      simp [hik, hjk]

private lemma sum_weight_mul_ite {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    (∑ k, a k * (if k = i then r else 0)) = a i * r := by
  simp [mul_ite]

private lemma swap_weighted_sum {n : ℕ} (a b : Fin n → ℝ) (i j : Fin n) :
    (∑ k, a k * b (Equiv.swap i j k)) =
      (∑ k, a k * b k) + a i * (b j - b i) + a j * (b i - b j) := by
  simp_rw [swap_apply_add, mul_add, Finset.sum_add_distrib, sum_weight_mul_ite]

private lemma signed_cross_total {n : ℕ} (a b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, ∑ j, a i * (b j - b i)) = -(n : ℝ) * ∑ i, a i * b i := by
  calc
    (∑ i, ∑ j, a i * (b j - b i)) = ∑ i, (-(n : ℝ)) * (a i * b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hb]
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

private lemma signed_cross_total' {n : ℕ} (a b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, ∑ j, a j * (b i - b j)) = -(n : ℝ) * ∑ i, a i * b i := by
  rw [Finset.sum_comm]
  exact signed_cross_total a b hb

private lemma sum_swap_weighted {n : ℕ} (a b : Fin n → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, ∑ j, ∑ k, a k * b (Equiv.swap i j k)) =
      ((n : ℝ) ^ 2 - 2 * n) * ∑ k, a k * b k := by
  simp_rw [swap_weighted_sum, Finset.sum_add_distrib, signed_cross_total a b hb,
    signed_cross_total' a b hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring


/-- The sign vector represented by a subset of coordinates. -/
def sliceSign {n k : ℕ} (x : Slice (Fin n) k) (i : Fin n) : ℝ :=
  if i ∈ x.val then 1 else -1

/-- The sum of the coefficients weighted by the signs of the slice point. -/
def sliceSignedSum {n k : ℕ} (a : Fin n → ℝ) (x : Slice (Fin n) k) : ℝ :=
  ∑ i, a i * sliceSign x i

lemma sliceSignedSum_eq {n k : ℕ} (a : Fin n → ℝ) (x : Slice (Fin n) k) :
    sliceSignedSum a x = ∑ i, if i ∈ x.val then a i else -a i := by
  simp [sliceSignedSum, sliceSign, mul_ite]

private lemma sum_sliceSign {n : ℕ} (hn : Even n) (x : Slice (Fin n) (n / 2)) :
    (∑ i, sliceSign x i) = 0 := by
  have hfilter : (Finset.univ.filter fun i : Fin n ↦ i ∈ x.val) = x.val := by
    ext i
    simp
  have sign_eq (i : Fin n) :
      sliceSign x i = (if i ∈ x.val then (2 : ℝ) else 0) - 1 := by
    by_cases hi : i ∈ x.val <;> norm_num [sliceSign, hi]
  simp_rw [sign_eq, Finset.sum_sub_distrib, Finset.sum_ite, hfilter, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, x.property, mul_one, mul_zero, add_zero]
  have hn2 : 2 * (n / 2) = n := by
    obtain ⟨m, rfl⟩ := hn
    omega
  exact sub_eq_zero.mpr (by exact_mod_cast (Nat.mul_comm (n / 2) 2).trans hn2)

private lemma sliceSign_swap {n k : ℕ} (x : Slice (Fin n) k) (i j l : Fin n) :
    sliceSign (swap i j x) l = sliceSign x (Equiv.swap i j l) := by
  simp [sliceSign, swap, Finset.mem_map_equiv]

lemma lap_abs_sliceSignedSum_le {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n)
    (a : Fin n → ℝ) (x : Slice (Fin n) (n / 2)) :
    lap (fun y ↦ |sliceSignedSum a y|) x ≤ 2 * (n : ℝ) * |sliceSignedSum a x| := by
  have hswap : (∑ i, ∑ j, sliceSignedSum a (swap i j x)) =
      ((n : ℝ) ^ 2 - 2 * n) * sliceSignedSum a x := by
    simp only [sliceSignedSum, sliceSign_swap]
    exact sum_swap_weighted a (sliceSign x) (sum_sliceSign hn x)
  have htriangle : |∑ i, ∑ j, sliceSignedSum a (swap i j x)| ≤
      ∑ i, ∑ j, |sliceSignedSum a (swap i j x)| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hfactor : 0 ≤ (n : ℝ) ^ 2 - 2 * n := by nlinarith
  rw [hswap, abs_mul, abs_of_nonneg hfactor] at htriangle
  simp only [lap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  linarith only [htriangle]

lemma abs_sliceSignedSum_compl {n k : ℕ} (h : Fintype.card (Fin n) = 2 * k)
    (a : Fin n → ℝ) (x : Slice (Fin n) k) :
    |sliceSignedSum a (compl x h)| = |sliceSignedSum a x| := by
  have hsum : sliceSignedSum a (compl x h) = -sliceSignedSum a x := by
    rw [sliceSignedSum_eq, sliceSignedSum_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if i ∈ x.valᶜ then a i else -a i) = -(if i ∈ x.val then a i else -a i)
    by_cases hi : i ∈ x.val <;> simp [hi]
  rw [hsum, abs_neg]

end BalancedSzarek

module
public import BalancedSzarek.Energy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

open scoped BigOperators

namespace BalancedSzarek

private lemma middleSlice_card {n : ℕ} :
    Fintype.card (Slice (Fin n) (n / 2)) =
      ((Finset.univ : Finset (Fin n)).powersetCard (n / 2)).card := by
  simp

private lemma balancedMean_eq_sum {n : ℕ} (g : Finset (Fin n) → ℝ) :
    balancedMean g =
      (∑ x : Slice (Fin n) (n / 2), g x.val) / Fintype.card (Slice (Fin n) (n / 2)) := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard (n / 2)
  have hΩ (x : Finset (Fin n)) : x ∈ Ω ↔ x.card = n / 2 := by simp [Ω]
  rw [balancedMean, Finset.sum_subtype Ω hΩ, middleSlice_card]

private lemma sum_sq_sub_mean {α : Type*} [Fintype α] (f : α → ℝ)
    (hcard : (Fintype.card α : ℝ) ≠ 0) :
    let μ := (∑ x, f x) / Fintype.card α
    (∑ x, (f x - μ) ^ 2) = (∑ x, f x ^ 2) - (Fintype.card α : ℝ) * μ ^ 2 := by
  let μ := (∑ x, f x) / Fintype.card α
  change (∑ x, (f x - μ) ^ 2) = (∑ x, f x ^ 2) - (Fintype.card α : ℝ) * μ ^ 2
  calc
    _ = (∑ x, f x ^ 2) - (∑ x, f x) * (2 * μ) + ∑ _ : α, μ ^ 2 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, μ]
      field_simp
      ring

lemma balanced_inequality_of_gap {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) (a : Fin n → ℝ)
    (hgap :
      let f : Slice (Fin n) (n / 2) → ℝ := fun x ↦ |sliceSignedSum a x|
      let μ := (∑ x, f x) / Fintype.card (Slice (Fin n) (n / 2))
      (4 * ((n : ℝ) - 1)) * (∑ x, (f x - μ) ^ 2) ≤ ∑ x, f x * lap f x) :
    let S := fun x : Finset (Fin n) ↦ ∑ i, if i ∈ x then a i else -a i
    Real.sqrt ((n - 2 : ℝ) / (2 * (n - 1))) *
        Real.sqrt (balancedMean (fun x ↦ (S x) ^ 2)) ≤
      balancedMean (fun x ↦ |S x|) := by
  let f : Slice (Fin n) (n / 2) → ℝ := fun x ↦ |sliceSignedSum a x|
  let m : ℝ := Fintype.card (Slice (Fin n) (n / 2))
  let μ := (∑ x, f x) / m
  let q := (∑ x, f x ^ 2) / m
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (show 0 < Fintype.card (Slice (Fin n) (n / 2)) by
      rw [middleSlice_card, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_pos (by omega))
  have hμ : 0 ≤ μ :=
    div_nonneg (Finset.sum_nonneg fun x _ ↦ abs_nonneg _) hm.le
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hden : 0 < 2 * ((n : ℝ) - 1) := by linarith
  have hr : 0 ≤ ((n : ℝ) - 2) / (2 * ((n : ℝ) - 1)) := div_nonneg (by linarith) hden.le
  have henergy : ∑ x, f x * lap f x ≤ 2 * (n : ℝ) * ∑ x, f x ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    calc
      f x * lap f x ≤ f x * (2 * (n : ℝ) * f x) :=
        mul_le_mul_of_nonneg_left (lap_abs_sliceSignedSum_le hn hn4 a x) (abs_nonneg _)
      _ = _ := by ring
  have htotal := hgap.trans henergy
  have hvariance := sum_sq_sub_mean f hm.ne'
  change
    (4 * ((n : ℝ) - 1)) * (∑ x, (f x - μ) ^ 2) ≤ 2 * (n : ℝ) * ∑ x, f x ^ 2 at htotal
  change (∑ x, (f x - μ) ^ 2) = (∑ x, f x ^ 2) - m * μ ^ 2 at hvariance
  rw [hvariance] at htotal
  have hq : q * m = ∑ x, f x ^ 2 := div_mul_cancel₀ _ hm.ne'
  rw [← hq] at htotal
  have hnorm : 4 * ((n : ℝ) - 1) * (q - μ ^ 2) ≤ 2 * (n : ℝ) * q := by
    apply le_of_mul_le_mul_right ?_ hm
    calc
      (4 * ((n : ℝ) - 1) * (q - μ ^ 2)) * m =
          4 * ((n : ℝ) - 1) * (q * m - m * μ ^ 2) := by ring
      _ ≤ 2 * (n : ℝ) * (q * m) := htotal
      _ = _ := by ring
  have hsq : (((n : ℝ) - 2) / (2 * ((n : ℝ) - 1))) * q ≤ μ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith only [hnorm]
  let S := fun x : Finset (Fin n) ↦ ∑ i, if i ∈ x then a i else -a i
  have hqmean : balancedMean (fun x ↦ (S x) ^ 2) = q := by
    simp [balancedMean_eq_sum, q, m, f, S, sliceSignedSum_eq, sq_abs]
  have hμmean : balancedMean (fun x ↦ |S x|) = μ := by
    simp [balancedMean_eq_sum, μ, m, f, S, sliceSignedSum_eq]
  change _ * Real.sqrt (balancedMean (fun x ↦ (S x) ^ 2)) ≤ balancedMean (fun x ↦ |S x|)
  rw [hqmean, hμmean]
  rw [← Real.sqrt_mul hr]
  exact (Real.sqrt_le_left hμ).mpr hsq

end BalancedSzarek

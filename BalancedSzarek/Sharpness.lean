module
public import BalancedSzarek.Definitions
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Finset
open scoped BigOperators

private theorem twice_choose_two (m : ℕ) : 2 * m.choose 2 = (m - 1) * m := by
  simpa [Nat.descFactorial_succ m 1] using (Nat.descFactorial_eq_factorial_mul_choose m 2).symm

private theorem same_sign_fraction (n : ℕ) (hn : 4 ≤ n) (he : Even n) :
    2 * ((n - 2).choose (n / 2 - 2) : ℝ) / (n.choose (n / 2) : ℝ) =
      (n - 2 : ℝ) / (2 * (n - 1)) := by
  let k := n / 2
  have hnk : n = k + k := by
    obtain ⟨m, hm⟩ := he
    dsimp [k]
    omega
  have hk : 2 ≤ k := by omega
  have h := Nat.choose_mul (n := n) (k := k) hk
  have h₂ := congrArg (fun x : ℕ ↦ 2 * x) h
  change 2 * (n.choose k * k.choose 2) =
    2 * (n.choose 2 * (n - 2).choose (k - 2)) at h₂
  simp only [Nat.mul_left_comm 2 (n.choose k), ← Nat.mul_assoc 2 (n.choose 2),
    twice_choose_two] at h₂
  have hr : (n.choose k : ℝ) * (((k - 1 : ℕ) : ℝ) * (k : ℝ)) =
      ((n - 1 : ℕ) : ℝ) * (n : ℝ) * ((n - 2).choose (k - 2) : ℝ) := by
    exact_mod_cast h₂
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ n)] at hr
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnkR : (n : ℝ) = (k : ℝ) + k := by exact_mod_cast hnk
  have htotal : 0 < (n.choose k : ℝ) := by exact_mod_cast (Nat.choose_pos (by omega : k ≤ n))
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  change 2 * ((n - 2).choose (k - 2) : ℝ) / (n.choose k : ℝ) = _
  apply (div_eq_div_iff (ne_of_gt htotal) (mul_ne_zero (by norm_num) hn1)).2
  apply mul_left_cancel₀ hn0
  linear_combination -4 * hr - ((n.choose k : ℝ) * ((n : ℝ) + 2 * (k : ℝ) - 2)) * hnkR

/-- The two equal nonzero coefficients give equality in Theorem 3. -/
theorem balancedSzarek_sharp (n : ℕ) (hn_even : Even n) (hn : 4 ≤ n) (c : ℝ)
    (hc : ∀ a : Fin n → ℝ,
      let S := fun x : Finset (Fin n) ↦ ∑ i, if i ∈ x then a i else -a i
      c * Real.sqrt (balancedMean (fun x ↦ (S x) ^ 2)) ≤
        balancedMean (fun x ↦ |S x|)) :
    c ≤ Real.sqrt ((n - 2 : ℝ) / (2 * (n - 1))) := by
  classical
  let k := n / 2
  have hnk : n = k + k := by
    obtain ⟨m, hm⟩ := hn_even
    dsimp [k]
    omega
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let a : Fin n → ℝ := fun t ↦ (if t = i then 1 else 0) + (if t = j then 1 else 0)
  let S : Finset (Fin n) → ℝ := fun x ↦ ∑ t, if t ∈ x then a t else -a t
  have hS (x : Finset (Fin n)) :
      S x = (if i ∈ x then 1 else -1) + (if j ∈ x then 1 else -1) := by
    calc
      S x = ∑ t : Fin n,
          ((if t = i then (if i ∈ x then 1 else -1) else 0) +
           (if t = j then (if j ∈ x then 1 else -1) else 0)) := by
        refine sum_congr rfl fun t _ ↦ ?_
        by_cases hti : t = i <;> by_cases htj : t = j <;>
          by_cases ht : t ∈ x <;> simp_all [a]
      _ = _ := by simp [sum_add_distrib]
  let Ω := (univ : Finset (Fin n)).powersetCard k
  let plus := Ω.filter fun x ↦ i ∈ x ∧ j ∈ x
  let minus := Ω.filter fun x ↦ i ∉ x ∧ j ∉ x
  have hcompl (x : Finset (Fin n)) (hx : x ∈ Ω) : xᶜ ∈ Ω := by
    have hcard : x.card = k := (mem_powersetCard.mp hx).2
    apply mem_powersetCard.mpr
    refine ⟨subset_univ _, ?_⟩
    rw [card_compl, Fintype.card_fin, hcard]
    omega
  have hminus : minus.card = plus.card := by
    apply card_nbij' (fun x ↦ xᶜ) (fun x ↦ xᶜ)
    · intro x hx
      have h := mem_filter.mp hx
      exact mem_filter.mpr ⟨hcompl x h.1, by simpa using h.2⟩
    · intro x hx
      have h := mem_filter.mp hx
      exact mem_filter.mpr ⟨hcompl x h.1, by simpa using h.2⟩
    · intro x _
      exact compl_compl x
    · intro x _
      exact compl_compl x
  have hplus : plus.card = (n - 2).choose (k - 2) := by
    have hpair : ({i, j} : Finset (Fin n)).card = 2 := by simp [hij]
    have h := card_filter_powersetCard_subset ({i, j} : Finset (Fin n))
      (univ : Finset (Fin n)) k (subset_univ _) (by rw [hpair]; omega)
    simpa only [hpair, card_univ, Fintype.card_fin, insert_subset_iff,
      singleton_subset_iff, plus, Ω] using h
  have hΩ : Ω.card = n.choose k := by simp [Ω, card_powersetCard]
  have hsum {r : ℝ} {f : Finset (Fin n) → ℝ}
      (hf : ∀ x, f x = (if i ∈ x ∧ j ∈ x then r else 0) +
        (if i ∉ x ∧ j ∉ x then r else 0)) :
      balancedMean f = r * (2 * ((n - 2).choose (k - 2) : ℝ) /
        (n.choose k : ℝ)) := by
    unfold balancedMean
    change (∑ x ∈ Ω, f x) / Ω.card = _
    simp only [hf, sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const,
      nsmul_eq_mul]
    change ((plus.card : ℝ) * r + (minus.card : ℝ) * r) / Ω.card = _
    rw [hminus, hplus, hΩ]
    ring
  let p := (n - 2 : ℝ) / (2 * (n - 1))
  have hprob : 2 * ((n - 2).choose (k - 2) : ℝ) / (n.choose k : ℝ) = p :=
    same_sign_fraction n hn hn_even
  have hfirst : balancedMean (fun x ↦ |S x|) = 2 * p := by
    rw [hsum, hprob]
    intro x
    rw [hS]
    by_cases hi : i ∈ x <;> by_cases hj : j ∈ x <;> norm_num [hi, hj]
  have hsecond : balancedMean (fun x ↦ (S x) ^ 2) = 4 * p := by
    rw [hsum, hprob]
    intro x
    rw [hS]
    by_cases hi : i ∈ x <;> by_cases hj : j ∈ x <;> norm_num [hi, hj]
  have htest : c * Real.sqrt (balancedMean (fun x ↦ (S x) ^ 2)) ≤
      balancedMean (fun x ↦ |S x|) := hc a
  rw [hfirst, hsecond, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at htest
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hs := Real.sq_sqrt hp.le
  change c ≤ Real.sqrt p
  apply le_of_mul_le_mul_right _ (Real.sqrt_pos.2 hp)
  nlinarith

module
public import BalancedSzarek.Definitions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section

open scoped BigOperators

namespace BalancedSzarek

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def inc (a x : Finset ι) : ℝ := if a ⊆ x then 1 else 0

omit [Fintype ι] in
private theorem inc_eq_prod (a x : Finset ι) :
    inc a x = ∏ i ∈ a, (if i ∈ x then (1 : ℝ) else 0) := by
  by_cases h : a ⊆ x
  · rw [inc, ite_eq_left h]
    symm
    exact Finset.prod_eq_one fun i hi ↦ ite_eq_left (h hi)
  · rw [inc, ite_eq_right h]
    change ¬ ∀ ⦃i⦄, i ∈ a → i ∈ x at h
    push Not at h
    obtain ⟨i, hi, hix⟩ := h
    symm
    exact Finset.prod_eq_zero hi (ite_eq_right hix)

private theorem inc_compl (a x : Finset ι) :
    inc a xᶜ = ∑ b ∈ a.powerset, (-1 : ℝ) ^ b.card * inc b x := by
  simp_rw [inc_eq_prod]
  rw [← show (∏ i ∈ a, (1 - (if i ∈ x then (1 : ℝ) else 0))) =
      ∑ b ∈ a.powerset, (-1 : ℝ) ^ b.card *
        ∏ i ∈ b, (if i ∈ x then (1 : ℝ) else 0) from by
    simpa only [Finset.prod_const_one, mul_one] using
      Finset.prod_sub (fun _ : ι ↦ (1 : ℝ)) (fun i ↦ if i ∈ x then 1 else 0) a]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i ∈ x <;> simp [h]

private def swapSet (i j : ι) (x : Finset ι) : Finset ι :=
  x.map (Equiv.swap i j).toEmbedding

omit [Fintype ι] in
private theorem mem_swapSet (i j t : ι) (x : Finset ι) :
    t ∈ swapSet i j x ↔ Equiv.swap i j t ∈ x := by
  rw [swapSet, Finset.mem_map_equiv, Equiv.symm_swap]

omit [Fintype ι] in
private theorem swapSet_same {a : Finset ι} {i j : ι} (h : i ∈ a ↔ j ∈ a) :
    swapSet i j a = a := by
  ext t
  rw [mem_swapSet]
  by_cases hti : t = i
  · subst t
    simpa using h.symm
  by_cases htj : t = j
  · subst t
    simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hti htj]

omit [Fintype ι] in
private theorem swapSet_move {a : Finset ι} {i j : ι} (hi : i ∈ a) (hj : j ∉ a) :
    swapSet i j a = insert j (a.erase i) := by
  have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
  ext t
  rw [mem_swapSet]
  by_cases hti : t = i
  · subst t
    simp [hij, hj]
  by_cases htj : t = j
  · subst t
    simp [hi]
  simp [Equiv.swap_apply_of_ne_of_ne hti htj, hti, htj]

omit [Fintype ι] in
private theorem inc_swap (a x : Finset ι) (i j : ι) :
    inc a (swapSet i j x) = inc (swapSet i j a) x := by
  unfold inc swapSet
  have h : a ⊆ x.map (Equiv.swap i j).toEmbedding ↔
      a.map (Equiv.swap i j).toEmbedding ⊆ x := by
    simpa only [Equiv.symm_swap] using
      (Finset.subset_map_symm (s := a) (t := x) (f := Equiv.swap i j))
  simp only [h]

private theorem sum_swap_reduce (a x : Finset ι) :
    (∑ i, ∑ j, (inc a x - inc a (swapSet i j x))) =
      2 * ∑ i ∈ a, ∑ j ∈ aᶜ, (inc a x - inc (insert j (a.erase i)) x) := by
  let f := fun i j ↦ inc a x - inc a (swapSet i j x)
  have hsym (i j : ι) : f i j = f j i := by
    dsimp [f, swapSet]
    rw [Equiv.swap_comm]
  have hsame (b : Finset ι) (h : ∀ i ∈ b, ∀ j ∈ b, i ∈ a ↔ j ∈ a) :
      (∑ i ∈ b, ∑ j ∈ b, f i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    dsimp [f]
    rw [inc_swap, swapSet_same (h i hi j hj), sub_self]
  have ha : (∑ i ∈ a, ∑ j ∈ a, f i j) = 0 :=
    hsame a (fun _ hi _ hj ↦ iff_of_true hi hj)
  have hac : (∑ i ∈ aᶜ, ∑ j ∈ aᶜ, f i j) = 0 :=
    hsame aᶜ (fun _ hi _ hj ↦ iff_of_false (Finset.mem_compl.mp hi) (Finset.mem_compl.mp hj))
  have hcross : (∑ i ∈ aᶜ, ∑ j ∈ a, f i j) = ∑ i ∈ a, ∑ j ∈ aᶜ, f i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hsym j i
  change (∑ i, ∑ j, f i j) = _
  rw [← Finset.sum_add_sum_compl a]
  simp_rw [← Finset.sum_add_sum_compl a (f _), Finset.sum_add_distrib]
  rw [ha, hac, hcross, zero_add, add_zero, ← two_mul]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  simp only [f, inc_swap, swapSet_move hi (Finset.mem_compl.mp hj)]


private theorem sum_insert_erase (a x : Finset ι) {i : ι} (hi : i ∈ a) :
    (∑ j ∈ aᶜ, inc (insert j (a.erase i)) x) =
      ((x.card : ℝ) + 1 - a.card) * inc (a.erase i) x - inc a x := by
  by_cases h : a.erase i ⊆ x
  · have hsum : (∑ j ∈ aᶜ, inc (insert j (a.erase i)) x) = ((x \ a).card : ℝ) := by
      simp_rw [inc, Finset.insert_subset_iff, h, and_true]
      rw [← Finset.sum_filter]
      have heq : aᶜ.filter (· ∈ x) = x \ a := by
        ext j
        simp [and_comm]
      rw [heq]
      simp
    rw [hsum, inc, ite_eq_left h, mul_one]
    by_cases hix : i ∈ x
    · have ha : a ⊆ x := by
        rw [← Finset.insert_erase hi, Finset.insert_subset_iff]
        exact ⟨hix, h⟩
      have hcard := Finset.card_sdiff_add_card_eq_card ha
      have hcast : ((x \ a).card : ℝ) + a.card = x.card := by exact_mod_cast hcard
      rw [inc, ite_eq_left ha]
      linarith
    · have ha : ¬ a ⊆ x := fun ha ↦ hix (ha hi)
      have hdiff : x \ a = x \ a.erase i := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [hix]
        · simp [hj]
      have hcard := Finset.card_sdiff_add_card_eq_card h
      have hcast : ((x \ a.erase i).card : ℝ) + (a.erase i).card = x.card := by
        exact_mod_cast hcard
      have hcard' := Finset.card_erase_add_one hi
      have hcast' : ((a.erase i).card : ℝ) + 1 = a.card := by exact_mod_cast hcard'
      rw [hdiff, inc, ite_eq_right ha]
      linarith
  · have ha : ¬ a ⊆ x := fun ha ↦ h (Finset.erase_subset i a |>.trans ha)
    simp [inc, Finset.insert_subset_iff, h, ha]

/-- Indicator that the chosen set contains the index set. -/
def monomial {k : ℕ} (a : Finset ι) (x : Slice ι k) : ℝ := inc a x.1

@[simp] theorem monomial_empty {k : ℕ} (x : Slice ι k) : monomial ∅ x = 1 := by
  simp [monomial, inc]

theorem monomial_self {k : ℕ} (x y : Slice ι k) :
    monomial x.val y = if y = x then 1 else 0 := by
  have h : x.val ⊆ y.val ↔ y = x := by
    constructor
    · intro hxy
      apply Subtype.ext
      exact (Finset.eq_of_subset_of_card_le hxy (by rw [x.property, y.property])).symm
    · rintro rfl
      exact Finset.Subset.rfl
  simp [monomial, inc, h]

theorem lap_monomial {k : ℕ} (a : Finset ι) (x : Slice ι k) :
    lap (monomial a) x =
      2 * (a.card : ℝ) * ((Fintype.card ι : ℝ) + 1 - a.card) * monomial a x -
      2 * ((k : ℝ) + 1 - a.card) * ∑ i ∈ a, monomial (a.erase i) x := by
  change (∑ i, ∑ j, (inc a x.1 - inc a (swapSet i j x.1))) = _
  rw [sum_swap_reduce]
  have hcard : (aᶜ.card : ℝ) = (Fintype.card ι : ℝ) - a.card := by
    have h := Finset.card_add_card_compl a
    have hcast : (a.card : ℝ) + aᶜ.card = Fintype.card ι := by exact_mod_cast h
    linarith
  have h (i : ι) (hi : i ∈ a) :
      (∑ j ∈ aᶜ, (inc a x.1 - inc (insert j (a.erase i)) x.1)) =
        ((Fintype.card ι : ℝ) + 1 - a.card) * inc a x.1 -
          ((k : ℝ) + 1 - a.card) * inc (a.erase i) x.1 := by
    rw [Finset.sum_sub_distrib, sum_insert_erase a x.1 hi, x.2]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib,
    ← Finset.mul_sum a (fun i ↦ inc (a.erase i) x.1) ((k : ℝ) + 1 - a.card)]
  simp only [Finset.sum_const, nsmul_eq_mul, monomial]
  ring

theorem monomial_compl {k : ℕ} (h : Fintype.card ι = 2 * k)
    (a : Finset ι) (x : Slice ι k) :
    monomial a (compl x h) = ∑ b ∈ a.powerset, (-1 : ℝ) ^ b.card * monomial b x :=
  inc_compl a x.1

end BalancedSzarek

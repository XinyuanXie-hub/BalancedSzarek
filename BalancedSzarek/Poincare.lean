module
public import BalancedSzarek.Linear
public import BalancedSzarek.Operator
public import BalancedSzarek.Spectrum

public section

open scoped BigOperators RealInnerProductSpace

namespace BalancedSzarek

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

noncomputable def moment (f : Slice ι k → ℝ) (a : Finset ι) : ℝ :=
  ∑ x, f x * monomial a x

private theorem even_eigenvalue (h : Fintype.card ι = 2 * k)
    (eigenvalue : ℝ) (v : EuclideanSpace ℝ (Slice ι k))
    (hv : v ∈ centeredEven h) (hne : v ≠ 0) (hev : lapLinear v = eigenvalue • v) :
    4 * ((Fintype.card ι : ℝ) - 1) ≤ eigenvalue := by
  classical
  obtain ⟨heven, hcenter⟩ := hv
  let f : Slice ι k → ℝ := fun x ↦ v x
  have hfeven (x : Slice ι k) : f (compl x h) = f x := heven x
  have hNonzero : ∃ x, f x ≠ 0 := by
    by_contra! hs
    apply hne
    ext x
    exact hs x
  obtain ⟨x, hx⟩ := hNonzero
  have hxmoment : moment f x.val ≠ 0 := by
    simpa [moment, monomial_self, mul_ite] using hx
  have hex : ∃ d : ℕ, ∃ a : Finset ι, a.card = d ∧ moment f a ≠ 0 :=
    ⟨k, x.val, x.property, hxmoment⟩
  let d := Nat.find hex
  obtain ⟨a, ha, hma⟩ := Nat.find_spec hex
  change a.card = d at ha
  have hdk : d ≤ k := Nat.find_min' hex ⟨x.val, x.property, hxmoment⟩
  have hlower (b : Finset ι) (hb : b.card < d) : moment f b = 0 := by
    by_contra hne
    exact (Nat.not_lt_of_ge (Nat.find_min' hex ⟨b, rfl, hne⟩)) hb
  have hd0 : d ≠ 0 := by
    intro hd
    have ha0 : a = ∅ := Finset.card_eq_zero.mp (ha.trans hd)
    apply hma
    simpa [moment, ha0, monomial_empty, f] using hcenter
  let C : Slice ι k ≃ Slice ι k :=
    (show Function.Involutive (fun x ↦ compl x h) from fun x ↦ compl_compl x h).toPerm _
  have hparity : moment f a = (-1 : ℝ) ^ d * moment f a := by
    calc
      moment f a = ∑ x, f (compl x h) * monomial a (compl x h) :=
        (C.sum_comp (fun x ↦ f x * monomial a x)).symm
      _ = ∑ b ∈ a.powerset, (-1 : ℝ) ^ b.card * moment f b := by
        simp_rw [hfeven, monomial_compl, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        unfold moment
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by ring
      _ = (-1 : ℝ) ^ d * moment f a := by
        rw [Finset.sum_eq_single a, ha]
        · intro b hb hba
          have hsub := Finset.mem_powerset.mp hb
          rw [hlower b (ha ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hba⟩)),
            mul_zero]
        · exact fun hnot ↦ (hnot (Finset.mem_powerset.mpr (Finset.Subset.refl a))).elim
  have hd2 : 2 ≤ d := by
    by_contra! h
    have hd1 : d = 1 := by omega
    rw [hd1, pow_one] at hparity
    exact hma (by linarith)
  have hev' (x : Slice ι k) : lap f x = eigenvalue * f x := by
    exact congrArg (fun g : EuclideanSpace ℝ (Slice ι k) ↦ g x) hev
  have hfrequency :
      2 * (d : ℝ) * ((Fintype.card ι : ℝ) + 1 - d) * moment f a = eigenvalue * moment f a := by
    calc
      _ = ∑ x, f x * lap (monomial a) x := by
        simp only [lap_monomial, ha]
        simp_rw [mul_sub (f _)]
        rw [Finset.sum_sub_distrib]
        have hmain :
            (∑ x, f x * (2 * (d : ℝ) * ((Fintype.card ι : ℝ) + 1 - d) *
              monomial a x)) = 2 * (d : ℝ) * ((Fintype.card ι : ℝ) + 1 - d) * moment f a := by
          rw [moment, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ by ring
        rw [hmain]
        suffices (∑ x, f x * (2 * ((k : ℝ) + 1 - d) *
            ∑ i ∈ a, monomial (a.erase i) x)) = 0 by rw [this, sub_zero]
        simp_rw [mul_assoc, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro i hi
        have hcard : (a.erase i).card < d := ha ▸ Finset.card_erase_lt_of_mem hi
        calc
          _ = (2 * ((k : ℝ) + 1 - d)) * moment f (a.erase i) := by
            rw [moment, Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ ↦ by ring
          _ = 0 := by rw [hlower _ hcard, mul_zero]
      _ = ∑ x, monomial a x * lap f x := lap_pair f (monomial a)
      _ = _ := by
        rw [moment, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by rw [hev']; ring
  rw [← mul_right_cancel₀ hma hfrequency]
  exact degree_two_bound _ _ _ h hd2 hdk

theorem poincare (h : Fintype.card ι = 2 * k) (f : Slice ι k → ℝ)
    (hf : ∀ x, f (compl x h) = f x) :
    let μ := (∑ x, f x) / Fintype.card (Slice ι k)
    4 * ((Fintype.card ι : ℝ) - 1) * (∑ x, (f x - μ) ^ 2) ≤
      ∑ x, f x * lap f x := by
  classical
  dsimp only
  let μ : ℝ := (∑ x, f x) / Fintype.card (Slice ι k)
  let g : EuclideanSpace ℝ (Slice ι k) := WithLp.toLp _ (fun x ↦ f x - μ)
  have hg : g ∈ centeredEven h := by
    refine ⟨fun x ↦ by change f (compl x h) - μ = f x - μ; rw [hf], ?_⟩
    change (∑ x, (f x - μ)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    by_cases hc : (Fintype.card (Slice ι k) : ℝ) = 0
    · have : IsEmpty (Slice ι k) := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hc)
      simp
    · dsimp [μ]
      field_simp; ring
  have hbound := spectral_lower_bound_on lapLinear lapLinear_symmetric (centeredEven h)
    (fun _ hv ↦ lapLinear_mem_centeredEven h hv) _ (even_eigenvalue h) g hg
  have hshift (x : Slice ι k) : lap (fun y ↦ g y) x = lap f x := by
    unfold lap
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      change (f x - μ) - (f (swap i j x) - μ) = _
      ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, lapLinear_apply, hshift] at hbound
  change 4 * ((Fintype.card ι : ℝ) - 1) * (∑ x, (f x - μ) * (f x - μ)) ≤
    ∑ x, lap f x * (f x - μ) at hbound
  simpa only [pow_two, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_lap, zero_mul, sub_zero, mul_comm (lap f _) (f _)] using hbound

end BalancedSzarek

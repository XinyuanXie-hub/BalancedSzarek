module
public import BalancedSzarek.Definitions
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open scoped BigOperators RealInnerProductSpace

namespace BalancedSzarek

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def swapEquiv (i j : ι) : Slice ι k ≃ Slice ι k :=
  (show Function.Involutive (swap (k := k) i j) from swap_swap i j).toPerm _

theorem sum_lap (f : Slice ι k → ℝ) : ∑ x, lap f x = 0 := by
  unfold lap
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((swapEquiv (k := k) i j).sum_comp f).symm

theorem lap_compl (h : Fintype.card ι = 2 * k) (f : Slice ι k → ℝ)
    (hf : ∀ x, f (compl x h) = f x) (x : Slice ι k) :
    lap f (compl x h) = lap f x := by
  simp only [lap, swap_compl, hf]

theorem lap_const (c : ℝ) (x : Slice ι k) :
    lap (fun _ ↦ c) x = 0 := by
  simp [lap]

@[expose] noncomputable def lapLinear : EuclideanSpace ℝ (Slice ι k) →ₗ[ℝ]
    EuclideanSpace ℝ (Slice ι k) where
  toFun f := WithLp.toLp _ (lap fun x ↦ f x)
  map_add' f g := by
    ext x
    change lap (fun y ↦ f y + g y) x = lap (fun y ↦ f y) x + lap (fun y ↦ g y) x
    unfold lap
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  map_smul' c f := by
    ext x
    change lap (fun y ↦ c * f y) x = c * lap (fun y ↦ f y) x
    unfold lap
    simp_rw [Finset.mul_sum, mul_sub]

@[simp] theorem lapLinear_apply (f : EuclideanSpace ℝ (Slice ι k)) (x : Slice ι k) :
    lapLinear f x = lap (fun y ↦ f y) x := rfl

theorem lap_pair (f g : Slice ι k → ℝ) :
    ∑ x, f x * lap g x = ∑ x, g x * lap f x := by
  unfold lap
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have h := (swapEquiv (k := k) i j).sum_comp (fun x ↦ f x * g (swap i j x))
  change (∑ x, f (swap i j x) * g (swap i j (swap i j x))) =
    ∑ x, f x * g (swap i j x) at h
  simp only [swap_swap] at h
  congr 1
  · exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _
  · rw [← h]
    exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _

theorem lapLinear_symmetric : (lapLinear (ι := ι) (k := k)).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, lapLinear_apply]
  simp_rw [mul_comm (lap _ _) _]
  exact lap_pair (fun x ↦ g x) (fun x ↦ f x)

/-- Functions invariant under complementation with sum zero. -/
@[expose] noncomputable def centeredEven (h : Fintype.card ι = 2 * k) :
    Submodule ℝ (EuclideanSpace ℝ (Slice ι k)) where
  carrier := {f | (∀ x, f (compl x h) = f x) ∧ ∑ x, f x = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf, hsf⟩ ⟨hg, hsg⟩
    exact ⟨fun x ↦ by simp [hf x, hg x], by simp [Finset.sum_add_distrib, hsf, hsg]⟩
  smul_mem' := by
    rintro c f ⟨hf, hsf⟩
    refine ⟨fun x ↦ by simp [hf x], ?_⟩
    change ∑ x, c * f x = 0
    rw [← Finset.mul_sum, hsf, mul_zero]

theorem lapLinear_mem_centeredEven (h : Fintype.card ι = 2 * k)
    {f : EuclideanSpace ℝ (Slice ι k)} (hf : f ∈ centeredEven h) :
    lapLinear f ∈ centeredEven h := by
  obtain ⟨he, _⟩ := hf
  exact ⟨lap_compl h _ he, sum_lap _⟩

end BalancedSzarek

module
public import Mathlib.Analysis.InnerProductSpace.Spectrum

public section
open scoped RealInnerProductSpace

namespace BalancedSzarek

/-- A lower bound on the eigenvalues of a symmetric operator bounds its quadratic form. -/
theorem spectral_lower_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (gap : ℝ)
    (hgap : ∀ (μ : ℝ) (v : E), v ≠ 0 → L v = μ • v → gap ≤ μ) (v : E) :
    gap * ⟪v, v⟫ ≤ ⟪v, L v⟫ := by
  classical
  let b := hL.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have heig (i : Fin (Module.finrank ℝ E)) :
      gap ≤ hL.eigenvalues (n := Module.finrank ℝ E) rfl i :=
    hgap _ _ (b.toBasis.ne_zero i) (hL.apply_eigenvectorBasis rfl i)
  rw [← b.repr.inner_map_map v v, ← b.repr.inner_map_map v (L v)]
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change gap * (b.repr v i * b.repr v i) ≤ b.repr (L v) i * b.repr v i
  rw [hL.eigenvectorBasis_apply_self_apply rfl]
  let c := b.repr v i
  let μ := hL.eigenvalues (n := Module.finrank ℝ E) rfl i
  change gap * (c * c) ≤ (μ * c) * c
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right (heig i) (mul_self_nonneg c)

/-- The same bound on an invariant subspace, expressed in the ambient space. -/
theorem spectral_lower_bound_on {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (V : Submodule ℝ E)
    (hV : ∀ v ∈ V, L v ∈ V) (gap : ℝ)
    (hgap : ∀ (μ : ℝ) (v : E), v ∈ V → v ≠ 0 → L v = μ • v → gap ≤ μ)
    (v : E) (hv : v ∈ V) : gap * ⟪v, v⟫ ≤ ⟪v, L v⟫ := by
  apply spectral_lower_bound (L.restrict hV) (hL.restrict_invariant hV) gap _ (⟨v, hv⟩ : V)
  intro μ w hw heq
  apply hgap μ w w.property
  · exact fun h ↦ hw (Subtype.ext h)
  · exact congrArg Subtype.val heq

/-- The ordered-transposition eigenvalue in degree two is a lower bound
for the eigenvalues in degrees two through the size of the middle slice. -/
theorem degree_two_bound (n k d : ℕ) (hn : n = 2 * k) (hd : 2 ≤ d) (hdk : d ≤ k) :
    4 * ((n : ℝ) - 1) ≤ 2 * (d : ℝ) * ((n : ℝ) + 1 - d) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnd : (d : ℝ) + 1 ≤ n := by
    exact_mod_cast (show d + 1 ≤ n by omega)
  nlinarith [mul_nonneg (sub_nonneg.mpr hd')
    (show 0 ≤ (n : ℝ) - 1 - d by linarith)]

end BalancedSzarek

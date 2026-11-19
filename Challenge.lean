module
public import Mathlib.Analysis.Real.Sqrt

public section

open scoped BigOperators

/-- Uniform expectation over sign vectors whose coordinates sum to zero.
    A subset records the coordinates with sign `+1`. -/
noncomputable def balancedMean {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard (n / 2)
  (∑ x ∈ Ω, f x) / Ω.card

/-- Theorem 3 (Balanced Szarek’s inequality), arXiv:2605.05193v1. -/
theorem theorem3 (n : ℕ) (hn_even : Even n) (hn : 4 ≤ n) :
    IsGreatest
      {c : ℝ | ∀ a : Fin n → ℝ,
        let S := fun x : Finset (Fin n) ↦ ∑ i, if i ∈ x then a i else -a i
        c * Real.sqrt (balancedMean (fun x ↦ (S x) ^ 2)) ≤
          balancedMean (fun x ↦ |S x|)}
      (Real.sqrt ((n - 2 : ℝ) / (2 * (n - 1)))) := by
  sorry

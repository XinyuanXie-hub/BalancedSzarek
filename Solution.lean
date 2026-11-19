module
public import BalancedSzarek.Inequality
public import BalancedSzarek.Poincare
public import BalancedSzarek.Sharpness

public section

open scoped BigOperators

/-- Theorem 3 (Balanced Szarek’s inequality), arXiv:2605.05193v1. -/
theorem theorem3 (n : ℕ) (hn_even : Even n) (hn : 4 ≤ n) :
    IsGreatest
      {c : ℝ | ∀ a : Fin n → ℝ,
        let S := fun x : Finset (Fin n) ↦ ∑ i, if i ∈ x then a i else -a i
        c * Real.sqrt (balancedMean (fun x ↦ (S x) ^ 2)) ≤
          balancedMean (fun x ↦ |S x|)}
      (Real.sqrt ((n - 2 : ℝ) / (2 * (n - 1)))) := by
  constructor
  · intro a
    have hcard : Fintype.card (Fin n) = 2 * (n / 2) := by
      rw [Fintype.card_fin]
      obtain ⟨m, hm⟩ := hn_even
      omega
    apply BalancedSzarek.balanced_inequality_of_gap hn_even hn a
    simpa only [Fintype.card_fin] using
      BalancedSzarek.poincare hcard (fun x ↦ |BalancedSzarek.sliceSignedSum a x|)
        (BalancedSzarek.abs_sliceSignedSum_compl hcard a)
  · intro c hc
    exact balancedSzarek_sharp n hn_even hn c hc

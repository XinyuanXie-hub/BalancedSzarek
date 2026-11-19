module
public import Mathlib.Analysis.Real.Sqrt

public section

open scoped BigOperators

@[expose] noncomputable def balancedMean {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard (n / 2)
  (∑ x ∈ Ω, f x) / Ω.card

namespace BalancedSzarek

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-- The slice of subsets of cardinality `k`. -/
abbrev Slice (ι : Type*) [Fintype ι] (k : ℕ) := {x : Finset ι // x.card = k}

/-- Swap two coordinates of a point in the slice. -/
@[expose] def swap [DecidableEq ι] (i j : ι) (x : Slice ι k) : Slice ι k :=
  ⟨x.val.map (Equiv.swap i j).toEmbedding, by simpa using x.property⟩

theorem swap_swap [DecidableEq ι] (i j : ι) (x : Slice ι k) :
    swap i j (swap i j x) = x := by
  apply Subtype.ext
  ext a
  simp [swap, Finset.mem_map_equiv]

/-- The unnormalized Laplacian obtained by summing over ordered transpositions. -/
@[expose] noncomputable def lap [DecidableEq ι] (f : Slice ι k → ℝ) (x : Slice ι k) : ℝ :=
  ∑ i : ι, ∑ j : ι, (f x - f (swap i j x))

/-- Complementation is a permutation of the middle slice. -/
@[expose] def compl [DecidableEq ι] (x : Slice ι k) (h : Fintype.card ι = 2 * k) : Slice ι k :=
  ⟨x.valᶜ, by rw [Finset.card_compl, h, x.property]; omega⟩

@[simp] theorem compl_compl [DecidableEq ι] (x : Slice ι k)
    (h : Fintype.card ι = 2 * k) : compl (compl x h) h = x := by
  apply Subtype.ext
  exact _root_.compl_compl x.val

theorem swap_compl [DecidableEq ι] (i j : ι) (x : Slice ι k)
    (h : Fintype.card ι = 2 * k) : swap i j (compl x h) = compl (swap i j x) h := by
  apply Subtype.ext
  ext a
  simp [swap, compl, Finset.mem_map_equiv]

end BalancedSzarek

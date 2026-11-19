# Balanced Szarek’s inequality

This project uses Lean to verify Theorem 3 (Balanced Szarek’s inequality).

> Paata Ivanisvili and Xinyuan Xie, *Grokability in five inequalities*, [arXiv:2605.05193v1](https://arxiv.org/abs/2605.05193v1).

## Mathematical statements

The middle slice of the Hamming cube is

```math
\Omega_n:=\Bigl\{x\in\{-1,1\}^{n}:\sum_{i=1}^{n}x_i=0\Bigr\}.
```

<a name="theorem-3"></a>

**Theorem 3 (Balanced Szarek’s inequality).** Let $`n\in\mathbb{N}`$ be even and $`n\geq 4`$. Let $`x`$ be distributed uniformly on $`\Omega_n`$, and let $`a=(a_1,\dots,a_n)\in\mathbb{R}^n`$. Then

```math
c_n\sqrt{\mathbb{E}\Bigl|\sum_{i=1}^n a_i x_i\Bigr|^2}
\leq \mathbb{E}\Bigl|\sum_{i=1}^n a_i x_i\Bigr|,
```

where

```math
c_n=\sqrt{\frac{n-2}{2(n-1)}}
```

is optimal.

## Verification

To verify the correctness of the theorem in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match [Theorem 3 (Balanced Szarek’s inequality)](#theorem-3) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there.
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log (lines 198–203) reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.


Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.

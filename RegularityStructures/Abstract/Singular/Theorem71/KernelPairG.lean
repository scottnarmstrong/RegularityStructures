/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Model

/-!
# The generic kernel pair `(h, r)` of Theorem 7.1

The explicit kernel `K = ∑_n 2^{3n} K₀(S^{2^n} z)` and remainder `R̄ = H − K` of the decomposition
of the heat kernel `H` [Hai14, Lemma 5.5] are abstracted into a pair `(h, r)`: a causal shell
profile `h` and a remainder kernel `r` (`RemKernel r`).
`Model.kGammaRemG M h r P I γ f x = kGammaS M h P I γ f x + remVecG M r P γ f x` is the integration
operator of Theorem 7.1 for this pair; for `(annKernel0C N, annRemainderC N)` it is
`Model.kGammaRem`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A kernel pair for Theorem 7.1: a causal shell profile `h` of order `N` together with a smooth
causal remainder kernel `r` with spatially decaying derivatives. -/
structure KernelPair (h r : ParabolicSpace → ℝ) (N : ℕ) : Prop where
  shell : ShellProfile h N
  causal : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0
  rem : RemKernel r

/-- `annKernel0C N`, `annRemainderC N` is a kernel pair. -/
theorem kernelPair_ann (N : ℕ) : KernelPair (annKernel0C N) (annRemainderC N) N where
  shell := shellProfile_annKernel0C N
  causal := fun _ hz => annKernel0C_eq_zero_of_nonpos N hz
  rem := remKernel_annRemainderC N

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- The integration operator `𝒦_γ f + R_γ f` of Theorem 7.1 for a generic kernel pair `(h, r)`. -/
def kGammaRemG (M : Model 𝒯 parabolicSemigroup) (h r : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) : ι → ℝ :=
  M.kGammaS h P I γ f x + M.remVecG r P γ f x

end Model

end RegularityStructures

end

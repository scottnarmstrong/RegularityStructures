/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovNorm

/-!
# Diagonal characterization of semigroup model norms

Hairer--Steele, Appendix B, Proposition B.2 (arXiv:2301.10081v3), uses
diagonal fixed-kernel tests to estimate classical model norms. The existing semigroup
`Model.piNormOn` already uses those tests. Here its best-constant definition is identified
exactly with their supremum, including for differences. These identities concern the
diagonal semigroup norm, not the classical arbitrary-test-function norm.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace RegularityStructures.Model

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace E] {μ : Measure E}
  {𝒯 : RegularityStructure ι} {Q : RegularisingSemigroup E μ}

/-- The best nonnegative difference constant is admissible, including at its infimum. -/
theorem piDiffNormOn_le_iff (M Mbar : Model 𝒯 Q)
    (γ : ℝ) (S : Set E) (C : ℝ≥0) :
    M.piDiffNormOn Mbar γ S ≤ C ↔ M.PiDiffBoundOn Mbar γ C S := by
  apply iInf_nnreal_le_iff
  · intro a b hab h i hi u hu x hx
    exact (h i hi u hu x hx).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (Real.rpow_nonneg hu.1.le _))
  · intro c hc i hi u hu x hx
    exact le_mul_of_forall_pos_le_add_mul (Real.rpow_nonneg hu.1.le _)
      (fun ε hε => hc ε hε i hi u hu x hx)

/-- The analogous closed best-constant characterization for differences of `Γ`. -/
theorem gammaDiffNormOn_le_iff (M Mbar : Model 𝒯 Q)
    (γ : ℝ) (S : Set E) (C : ℝ≥0) :
    M.gammaDiffNormOn Mbar γ S ≤ C ↔ M.GammaDiffBoundOn Mbar γ C S := by
  apply iInf_nnreal_le_iff
  · intro a b hab h i j hi hj x hx y hy
    exact (h i j hi hj x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hab)
        (Real.rpow_nonneg (Q.scaleDist_nonneg _ _) _))
  · intro c hc i j hi hj x hx y hy
    exact le_mul_of_forall_pos_le_add_mul (Real.rpow_nonneg (Q.scaleDist_nonneg _ _) _)
      (fun ε hε => hc ε hε i j hi hj x hx y hy)

end RegularityStructures.Model

end

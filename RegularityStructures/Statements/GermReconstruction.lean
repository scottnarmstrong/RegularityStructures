/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Reconstruction

/-!
# The reconstruction theorem for coherent germs

The statement `RegularityStructures.Statements.RegularisingSemigroup.exists_reconstruction`.
Its proof is `RegularityStructures.RegularisingSemigroup.exists_reconstruction`,
in the module `RegularityStructures.Analysis.Semigroup.Reconstruction`.
-/

public section

namespace RegularityStructures

/-- **The reconstruction theorem for coherent germs** [Hos25, Theorem 4.1]: for `γ > 0` there is
`c`, depending only on the semigroup, `γ` and the exponent set `A`, such that every coherent
germ `F` of order `γ` with constant `C` has a reconstruction `RF` with `|RF_t(x) − F_x(t, x)| ≤
c C t^{γ/ℓ}` for `0 < t ≤ 1`, and `RF` is the only distribution with a bound of this form. -/
theorem Statements.RegularisingSemigroup.exists_reconstruction.{u_1} :
    ∀ {E : Type u_1} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
      (K : RegularityStructures.RegularisingSemigroup E μ) [MeasureTheory.SFinite μ] (γ : ℝ),
      0 < γ →
        ∀ (A : Finset ℝ),
          (∀ a ∈ A, a < γ) →
            ∃ (c : ℝ),
              0 ≤ c ∧
                ∀ ⦃F : E → ℝ → E → ℝ⦄ ⦃C : ℝ⦄,
                  K.IsGerm F →
                    0 ≤ C →
                      K.IsCoherent F γ A C →
                        K.reconstruct F ∈ K.distributions ∧
                          (∀ t ∈ Set.Ioc 0 1, ∀ (x : E), |K.reconstruct F t x - F x t x| ≤ c * C * t ^ (γ / K.order)) ∧
                            ∀ Λ ∈ K.distributions,
                              (∃ (C' : ℝ), ∀ t ∈ Set.Ioc 0 1, ∀ (x : E), |Λ t x - F x t x| ≤ C' * t ^ (γ / K.order)) →
                                Λ = K.reconstruct F :=
  by exact RegularityStructures.RegularisingSemigroup.exists_reconstruction

end RegularityStructures

end

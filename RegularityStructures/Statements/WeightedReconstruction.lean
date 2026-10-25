/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Weighted.Reconstruction

/-!
# Weighted reconstruction

The statement `RegularityStructures.Statements.RegularisingSemigroup.exists_reconstruction_weighted`.
Its proof is `RegularityStructures.RegularisingSemigroup.exists_reconstruction_weighted`,
in the module `RegularityStructures.Analysis.Semigroup.Weighted.Reconstruction`.
-/

public section

namespace RegularityStructures

/-- **The weighted reconstruction theorem** [Hos25, Theorem 4.1] with a polynomially moderate weight
`ρ`: for every weighted coherent germ `F` of order `γ > 0`, `|RF_t(x) − F_x(t, x)| ≤ c C ρ(x)
t^{γ/ℓ}` for `0 < t ≤ 1`, with `c` chosen before the germ and the weight, and `RF` is the only
distribution with a bound of this form. -/
theorem Statements.RegularisingSemigroup.exists_reconstruction_weighted.{u_1} :
    ∀ {E : Type u_1} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
      (K : RegularityStructures.RegularisingSemigroup E μ) [MeasureTheory.SFinite μ] (p γ : ℝ),
      0 < γ →
        ∀ (A : Finset ℝ),
          (∀ a ∈ A, a < γ) →
            ∃ (c : ℝ),
              0 ≤ c ∧
                ∀ ⦃ρ : E → ℝ⦄,
                  K.IsModerateWeight ρ p →
                    ∀ ⦃F : E → ℝ → E → ℝ⦄ ⦃C : ℝ⦄,
                      K.IsWeightedGerm F ρ →
                        0 ≤ C →
                          K.IsWeightedCoherent F ρ γ A C →
                            K.reconstruct F ∈ K.distributions ∧
                              (∀ t ∈ Set.Ioc 0 1,
                                  ∀ (x : E), |K.reconstruct F t x - F x t x| ≤ c * C * ρ x * t ^ (γ / K.order)) ∧
                                ∀ Λ ∈ K.distributions,
                                  (∃ (C' : ℝ),
                                      ∀ t ∈ Set.Ioc 0 1, ∀ (x : E), |Λ t x - F x t x| ≤ C' * ρ x * t ^ (γ / K.order)) →
                                    Λ = K.reconstruct F :=
  by exact RegularityStructures.RegularisingSemigroup.exists_reconstruction_weighted

end RegularityStructures

end

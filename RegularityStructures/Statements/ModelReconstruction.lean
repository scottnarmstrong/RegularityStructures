/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Reconstruction

/-!
# The reconstruction theorem

The statement `RegularityStructures.Statements.Model.exists_reconstruction`.
Its proof is `RegularityStructures.Model.exists_reconstruction`,
in the module `RegularityStructures.Abstract.Reconstruction`.
-/

public section

namespace RegularityStructures

/-- **The reconstruction theorem** [Hai14, Theorem 3.10], [Hos25, Theorem 4.1]. For `γ > 0` there is
a constant `c`, depending only on the regularity structure, the semigroup and `γ`, such that for
every model `M` with `‖Π‖ ≤ C_Π` and every `f ∈ D^γ` with `|||f||| ≤ C_f`: the reconstruction
`Rf` is a distribution, `|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f t^{γ/ℓ}` for `0 < t ≤ 1`, and
`Rf` is the only distribution with a bound of this form.
The model bound and the bound on `f` are global (on all of space-time), whereas [Hai14, Theorem 3.10]
is local, on compact sets; so the statement does not apply directly to models whose bounds hold only
locally, such as random models. -/
theorem Statements.Model.exists_reconstruction.{u_1, u_2} :
    ∀ {E : Type u_1} [MeasurableSpace E] {μ : MeasureTheory.Measure E} {ι : Type u_2} [Fintype ι]
      [DecidableEq ι] (𝒯 : RegularityStructures.RegularityStructure ι)
      (K : RegularityStructures.RegularisingSemigroup E μ) [MeasureTheory.SFinite μ] {γ : ℝ},
      0 < γ →
        ∃ (c : ℝ),
          0 ≤ c ∧
            ∀ (M : RegularityStructures.Model 𝒯 K) ⦃CPi Cf : ℝ⦄ ⦃f : E → ι → ℝ⦄,
              M.PiBoundOn γ CPi Set.univ →
                0 ≤ CPi →
                  f ∈ M.modelledDistributions γ →
                    M.ModelledBoundOn γ Cf Set.univ f →
                      0 ≤ Cf →
                        M.reconstruct f ∈ K.distributions ∧
                          (∀ t ∈ Set.Ioc 0 1,
                              ∀ (x : E), |M.reconstruct f t x - M.regPi x (f x) t x| ≤ c * CPi * Cf * t ^ (γ / K.order)) ∧
                            ∀ Λ ∈ K.distributions,
                              (∃ (C' : ℝ),
                                  ∀ t ∈ Set.Ioc 0 1, ∀ (x : E), |Λ t x - M.regPi x (f x) t x| ≤ C' * t ^ (γ / K.order)) →
                                Λ = M.reconstruct f :=
  by exact RegularityStructures.Model.exists_reconstruction

end RegularityStructures

end

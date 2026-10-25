/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Reconstruction

/-!
# Continuity of the reconstruction in the model

The statement `RegularityStructures.Statements.Model.abs_reconstruct_sub_reconstruct_le`.
Its proof is `RegularityStructures.Model.abs_reconstruct_sub_reconstruct_le`,
in the module `RegularityStructures.Abstract.Reconstruction`.
-/

public section

namespace RegularityStructures

/-- **Local Lipschitz continuity of the reconstruction in the model** [Hai14, Theorem 3.10, (3.4)],
[Hos25, Theorem 4.1]: `|(Q_t (R¹f¹ − Π¹_x f¹(x) − R²f² + Π²_x f²(x)))(x)| ≤ c (C_{f¹} ‖Π¹ − Π²‖
+ ‖Π²‖ |||f¹; f²|||) t^{γ/ℓ}` for `0 < t ≤ 1`.
The model bounds and the bounds on `f¹`, `f²` are global (on all of space-time), whereas [Hai14, Theorem 3.10]
is local, on compact sets; so the statement does not apply directly to models whose bounds hold only
locally, such as random models. -/
theorem Statements.Model.abs_reconstruct_sub_reconstruct_le.{u_1, u_2} :
    ∀ {E : Type u_1} [MeasurableSpace E] {μ : MeasureTheory.Measure E} {ι : Type u_2} [Fintype ι]
      [DecidableEq ι] {𝒯 : RegularityStructures.RegularityStructure ι}
      {K : RegularityStructures.RegularisingSemigroup E μ} [MeasureTheory.SFinite μ]
      (M₁ M₂ : RegularityStructures.Model 𝒯 K) {γ : ℝ},
      0 < γ →
        ∀ {CPi₁ CPi₂ CdPi Cf₁ Cf₂ Cdf : ℝ},
          M₁.PiBoundOn γ CPi₁ Set.univ →
            M₂.PiBoundOn γ CPi₂ Set.univ →
              M₁.PiDiffBoundOn M₂ γ CdPi Set.univ →
                0 ≤ CPi₁ →
                  0 ≤ CPi₂ →
                    0 ≤ CdPi →
                      ∀ {f₁ f₂ : E → ι → ℝ},
                        f₁ ∈ M₁.modelledDistributions γ →
                          f₂ ∈ M₂.modelledDistributions γ →
                            M₁.ModelledBoundOn γ Cf₁ Set.univ f₁ →
                              M₂.ModelledBoundOn γ Cf₂ Set.univ f₂ →
                                M₁.ModelledDiffBoundOn M₂ γ Cdf Set.univ f₁ f₂ →
                                  0 ≤ Cf₁ →
                                    0 ≤ Cf₂ →
                                      0 ≤ Cdf →
                                        ∀ {t : ℝ},
                                          t ∈ Set.Ioc 0 1 →
                                            ∀ (x : E),
                                              |M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x -
                                                    (M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x)| ≤
                                                RegularityStructures.modelReconstructionConst 𝒯 K γ *
                                                    (Cf₁ * CdPi + Cdf * CPi₂) *
                                                  t ^ (γ / K.order) :=
  by exact RegularityStructures.Model.abs_reconstruct_sub_reconstruct_le

end RegularityStructures

end

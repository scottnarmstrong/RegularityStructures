/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.QFamilyModelBound
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The difference cell-block bound

`exists_piHalfCell_block_bound_diff`: for two models, `x, x₀ ∈ S`, `d(x, x₀) ≤ s^{1/4}`,
`‖(Q_u (Π - Π') e_i)(x)‖ ≤ C₀ ∑_{deg k ≤ deg i} s^{(deg i - deg k)/4}
  ((1 + G) W^Δ_{s,k}(x₀) + G_Δ W'_{s,k}(x₀))`,
where `G` bounds `Γ` and `G_Δ` bounds `Γ - Γ'`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem lintegral_mul_add_mul_of_aemeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (c d : ℝ≥0∞) {A B : α → ℝ≥0∞} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) :
    ∫⁻ a, (c * A a + d * B a) ∂μ = c * ∫⁻ a, A a ∂μ + d * ∫⁻ a, B a ∂μ := by
  rw [lintegral_add_left' (hA.const_mul c), lintegral_const_mul'' _ hA,
    lintegral_const_mul'' _ hB]

namespace Model

/-- The coefficient bound for the `Γ`-difference. -/
theorem enorm_gammaMap_sub_coeff_le (M M' : Model 𝒯 parabolicSemigroup) {γ Gd : ℝ}
    (hGd : 0 ≤ Gd) {S : Set ParabolicSpace} (hΓ : GammaDiffBoundOn M M' γ Gd S) {i k : ι}
    (hi : 𝒯.deg i < γ) (hk : 𝒯.deg k ≤ 𝒯.deg i) {s : ℝ} (hs : 0 < s)
    {x x₀ : ParabolicSpace} (hx : x ∈ S) (hx₀ : x₀ ∈ S)
    (hd : parabolicNorm (x - x₀) ≤ s ^ (1 / 4 : ℝ)) :
    ‖M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k‖ₑ ≤
      ENNReal.ofReal Gd * ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4)) := by
  by_cases hki : k = i
  · subst hki
    rw [M.gammaMap_single_apply_self, M'.gammaMap_single_apply_self, sub_self, enorm_zero]
    exact bot_le
  rcases hk.lt_or_eq with hlt | heq
  · have hb := hΓ i k hi hlt x hx x₀ hx₀
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hGd]
    refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
    have h0 : parabolicSemigroup.scaleDist x₀ x ≤ s ^ (1 / 4 : ℝ) := by
      change parabolicNorm (x₀ - x) ≤ _
      rwa [parabolicNorm_sub_comm]
    have hscale : parabolicSemigroup.scaleDist x₀ x ^ (𝒯.deg i - 𝒯.deg k) ≤
        s ^ ((𝒯.deg i - 𝒯.deg k) / 4) := by
      calc _ ≤ (s ^ (1 / 4 : ℝ)) ^ (𝒯.deg i - 𝒯.deg k) :=
            Real.rpow_le_rpow (parabolicSemigroup.scaleDist_nonneg _ _) h0 (by linarith)
        _ = _ := by
            rw [← Real.rpow_mul hs.le]
            congr 1
            ring
    exact mul_le_mul_of_nonneg_left hscale hGd
  · have h1 : M.gammaMap x₀ x (Pi.single i 1) k = 0 :=
      (M.isGradedUnipotent_gammaMap x₀ x).apply_single_of_le hki heq.ge
    have h2 : M'.gammaMap x₀ x (Pi.single i 1) k = 0 :=
      (M'.isGradedUnipotent_gammaMap x₀ x).apply_single_of_le hki heq.ge
    rw [h1, h2, sub_zero, enorm_zero]
    exact bot_le

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceDouble5

/-!
# The chaos-`3` double integral of the difference for `I(Ψ³)Ψ²`

For the second difference `χ₃(…)` of the chaos-`3` kernel,
`∫∫ δK(z, w) δK(z', v) χ₃^Δ` is integrable on the product and bounded by `C μ² T(z, z')`, where
`T = i3Psi2DiffTarget δ θ`.  The integrand is dominated by the sum over the two monomials of `χ₃`
(`i3Psi2DiffT4`, `T5`), i.e. by weights of the chain (with `u = z`, `u' = z'`) and `N₂` diagrams with
one exponent raised by `2θ`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The chaos-`3` double integral of the difference** (integrability and bound). -/
theorem i3Psi2DiffDouble3_bound {B A δ θ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} {μ : ℝ}, 0 ≤ μ → Measurable K →
      Measurable Q₁₁ → Measurable Q₁₂ → Measurable Q₂₁ → Measurable Q₂₂ →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂ →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        Integrable (Function.uncurry fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi3 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - z) (v - z') (w - v) (w - z') (z - v) (z - z'))
          (volume.prod volume) ∧
        |∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi3 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - z) (v - z') (w - v) (w - z') (z - v) (z - z')| ≤
          C * μ ^ 2 * i3Psi2DiffTarget δ θ z z' := by
  obtain ⟨Cc1, hCc1, hC1⟩ := i3Psi2ChainWeighted_twoLevelLe (B := B) (δ := δ) (α := 2 * θ)
    (β₀ := 0) (γ := 0) (η := δ + 2 * θ) hB hδ (by linarith) (by linarith) le_rfl (by norm_num)
    le_rfl (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc2, hCc2, hC2⟩ := i3Psi2ChainWeighted_twoLevelLe (B := B) (δ := δ) (α := 0)
    (β₀ := 2 * θ) (γ := 0) (η := δ + 2 * θ) hB hδ le_rfl (by norm_num) le_rfl (by norm_num)
    (by linarith) (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc3, hCc3, hC3⟩ := i3Psi2ChainWeighted_twoLevelLe (B := B) (δ := δ) (α := 0)
    (β₀ := 0) (γ := 2 * θ) (η := δ + 2 * θ) hB hδ le_rfl (by norm_num) (by linarith)
    (by linarith) le_rfl (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc4, hCc4, hC4⟩ := i3Psi2ChainWeighted_twoLevelLe (B := B) (δ := δ) (α := 0)
    (β₀ := 0) (γ := 0) (η := δ) hB hδ le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cm1, hCm1, hM1⟩ := i3Psi2N2Weighted_twoLevelLe (B := B) (δ := δ) (y₁ := 2 * θ)
    (y₂ := 0) (y₃ := 0) (y₄ := 0) (y₅ := 0) hB hδ (by linarith) le_rfl le_rfl le_rfl le_rfl
    (by linarith)
  obtain ⟨Cm2, hCm2, hM2⟩ := i3Psi2N2Weighted_twoLevelLe (B := B) (δ := δ) (y₁ := 0)
    (y₂ := 2 * θ) (y₃ := 0) (y₄ := 0) (y₅ := 0) hB hδ le_rfl (by linarith) le_rfl le_rfl le_rfl
    (by linarith)
  obtain ⟨Cm3, hCm3, hM3⟩ := i3Psi2N2Weighted_twoLevelLe (B := B) (δ := δ) (y₁ := 0)
    (y₂ := 0) (y₃ := 2 * θ) (y₄ := 0) (y₅ := 0) hB hδ le_rfl le_rfl (by linarith) le_rfl le_rfl
    (by linarith)
  obtain ⟨Cm4, hCm4, hM4⟩ := i3Psi2N2Weighted_twoLevelLe (B := B) (δ := δ) (y₁ := 0)
    (y₂ := 0) (y₃ := 0) (y₄ := 2 * θ) (y₅ := 0) hB hδ le_rfl le_rfl le_rfl (by linarith) le_rfl
    (by linarith)
  obtain ⟨Cm5, hCm5, hM5⟩ := i3Psi2N2Weighted_twoLevelLe (B := B) (δ := δ) (y₁ := 0)
    (y₂ := 0) (y₃ := 0) (y₄ := 0) (y₅ := 2 * θ) hB hδ le_rfl le_rfl le_rfl le_rfl (by linarith)
    (by linarith)
  refine ⟨737280 * A ^ 5 * (Cc1 + Cc2 + Cc3 + Cc4 + Cm1 + Cm2 + Cm3 + Cm4 + Cm5),
    by positivity, ?_⟩
  intro K Q₁₁ Q₁₂ Q₂₁ Q₂₂ μ hμ hKm hQ11 hQ12 hQ21 hQ22 hK hKs hT z z' hzz hz hz' hz1 hz1'
  set K0 : ℝ := 737280 * A ^ 5 with hK0
  have hK0n : 0 ≤ K0 := by positivity
  have hΛ : 0 ≤ K0 * μ ^ 2 := by positivity
  have rn : ∀ e : ℝ, 0 ≤ torusParabolicSize (z - z') ^ e :=
    fun e => Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have e1 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := mul_nonneg hΛ (rn _)
  have e12 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) := mul_nonneg hΛ (rn _)
  have t41 := hC1 e1 hKm hK hKs z z' z z' hzz hz hz' hz1 hz1' (Or.inl ⟨rfl, rfl⟩)
  have t42 := hC2 e1 hKm hK hKs z z' z z' hzz hz hz' hz1 hz1' (Or.inl ⟨rfl, rfl⟩)
  have t43 := hC3 e1 hKm hK hKs z z' z z' hzz hz hz' hz1 hz1' (Or.inl ⟨rfl, rfl⟩)
  have t44 := hC4 e12 hKm hK hKs z z' z z' hzz hz hz' hz1 hz1' (Or.inl ⟨rfl, rfl⟩)
  have t51 := hM1 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have t52 := hM2 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have t53 := hM3 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have t54 := hM4 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have t55 := hM5 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  simp only [add_zero] at t41 t42 t43 t44 t51 t52 t53 t54 t55
  set F : SpaceTime → SpaceTime → ℝ := fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
    i3Psi2DiffChi3 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - z) (v - z') (w - v) (w - z') (z - v) (z - z') with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun p : SpaceTime × SpaceTime => i3Psi2dK K z p.1 * i3Psi2dK K z' p.2 *
      i3Psi2DiffChi3 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (p.1 - z) (p.2 - z') (p.1 - p.2) (p.1 - z') (z - p.2)
        (z - z'))
    unfold i3Psi2dK i3Psi2DiffChi3 i3Psi2Kernel3
    fun_prop
  have hsum := (((((((t41.add t42).add t43).add t44).add t51).add t52).add t53).add t54).add t55
  obtain ⟨hint, hbd⟩ := TwoLevelLe.integrable_bound (F := F) hFm.aestronglyMeasurable hsum (by
    filter_upwards [ae_ae_diffDouble_pos z z'] with w hw
    obtain ⟨⟨hzw, -, hz'w⟩, hw'⟩ := hw
    filter_upwards [hw'] with v hv
    obtain ⟨⟨hz'v, -, hzv⟩, hwv⟩ := hv
    have hch := i3Psi2DiffChi3_abs_le hμ hA hT (torusParabolicSize_sub_pos_symm hzw)
      (torusParabolicSize_sub_pos_symm hz'v) hwv (torusParabolicSize_sub_pos_symm hz'w) hzv hzz
    have hnn : 0 ≤ |i3Psi2dK K z w| * |i3Psi2dK K z' v| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hch hnn
    refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
    · simp only [hFdef, abs_mul]
    · unfold i3Psi2DiffT4 i3Psi2DiffT5
      ring)
  refine ⟨hint, hbd.trans ?_⟩
  have c2 := chain_raised_le_diffTarget (δ := δ) (θ := θ) hzz
  have c24 := chain_far_le_diffTarget (δ := δ) (θ := θ) hzz
  have c3 := S_one_add_le_diffTarget (θ := θ) hδ hz hz' hz1 hz1'
  have b2 : ∀ Cc : ℝ, 0 ≤ Cc → K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 : ℝ)) * Cc *
      i3Psi2S (δ + 2 * θ) z z' ≤ K0 * μ ^ 2 * Cc * i3Psi2DiffTarget δ θ z z' := by
    intro Cc hCc
    calc _ = K0 * μ ^ 2 * Cc * (torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
          i3Psi2S (δ + 2 * θ) z z') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left c2 (by positivity)
  have b24 : K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) * Cc4 *
      i3Psi2S δ z z' ≤ K0 * μ ^ 2 * Cc4 * i3Psi2DiffTarget δ θ z z' := by
    calc _ = K0 * μ ^ 2 * Cc4 * (torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) *
          i3Psi2S δ z z') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left c24 (by positivity)
  have b3 : ∀ Cn : ℝ, 0 ≤ Cn → K0 * μ ^ 2 * Cn * i3Psi2S (1 + δ + 2 * θ) z z' ≤
      K0 * μ ^ 2 * Cn * i3Psi2DiffTarget δ θ z z' := fun Cn hCn =>
    mul_le_mul_of_nonneg_left c3 (by positivity)
  have b41 := b2 Cc1 hCc1
  have b42 := b2 Cc2 hCc2
  have b43 := b2 Cc3 hCc3
  have b51 := b3 Cm1 hCm1
  have b52 := b3 Cm2 hCm2
  have b53 := b3 Cm3 hCm3
  have b54 := b3 Cm4 hCm4
  have b55 := b3 Cm5 hCm5
  linarith [b41, b42, b43, b24, b51, b52, b53, b54, b55]

end RegularityStructures.Phi43

end

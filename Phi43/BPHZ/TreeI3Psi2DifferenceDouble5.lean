/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceKernels
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN1Bound
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN2Bound
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiWeighted
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiTarget

/-!
# The chaos-`5` double integral of the difference for `I(Ψ³)Ψ²`

For the second difference `χ₅(Q₁₁) - χ₅(Q₁₂) - χ₅(Q₂₁) + χ₅(Q₂₂)` of the chaos-`5` kernel,
`∫∫ δK(z, w) δK(z', v) χ₅^Δ` is integrable on the product and bounded by `C μ² T(z, z')`, where
`T = i3Psi2DiffTarget δ θ`.  The integrand is dominated by the sum over the three monomials of `χ₅`
(`i3Psi2DiffT1`, `T2`, `T3`), i.e. by weights of the principal, chain (with `u = z'`, `u' = z`) and
`N₁` diagrams with one exponent raised by `2θ`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Almost everywhere positivity of the distances occurring in the chaos-`5` and chaos-`3`
integrands. -/
theorem ae_ae_diffDouble_pos (z z' : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, (0 < torusParabolicSize (z - w) ∧ 0 < torusParabolicSize (0 - w) ∧
        0 < torusParabolicSize (z' - w)) ∧ ∀ᵐ v : SpaceTime ∂volume,
      (0 < torusParabolicSize (z' - v) ∧ 0 < torusParabolicSize (0 - v) ∧
        0 < torusParabolicSize (z - v)) ∧ 0 < torusParabolicSize (w - v) := by
  filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
    ae_torusParabolicSize_sub_pos z'] with w a b c
  refine ⟨⟨a, b, c⟩, ?_⟩
  filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
    ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
  exact ⟨⟨a', b', c'⟩, d'⟩

/-- **The chaos-`5` double integral of the difference** (integrability and bound). -/
theorem i3Psi2DiffDouble5_bound {B A δ θ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} {μ : ℝ}, 0 ≤ μ → Measurable K →
      Measurable Q₁₁ → Measurable Q₁₂ → Measurable Q₂₁ → Measurable Q₂₂ →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂ →
      ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        Integrable (Function.uncurry fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - v) (w - z') (z - v) (z - z'))
          (volume.prod volume) ∧
        |∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - v) (w - z') (z - v) (z - z')| ≤
          C * μ ^ 2 * i3Psi2DiffTarget δ θ z z' := by
  obtain ⟨Cp1, hCp1, hP1⟩ := i3Psi2PrincipalWeighted_twoLevelLe (B := B) (θ := 1 - δ - 2 * θ)
    (τ := 2 * θ) hB (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cp2, hCp2, hP2⟩ := i3Psi2PrincipalWeighted_twoLevelLe (B := B) (θ := 1 - δ) (τ := 0)
    hB (by linarith) (by linarith) le_rfl (by linarith)
  obtain ⟨Cc1, hCc1, hC1⟩ := i3Psi2ChainLeftWeighted_twoLevelLe (B := B) (δ := δ) (α := 0)
    (β₀ := 2 * θ) (γ := 0) (η := δ + 2 * θ) hB hδ le_rfl (by norm_num) le_rfl (by norm_num)
    (by linarith) (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc2, hCc2, hC2⟩ := i3Psi2ChainLeftWeighted_twoLevelLe (B := B) (δ := δ) (α := 2 * θ)
    (β₀ := 0) (γ := 0) (η := δ + 2 * θ) hB hδ (by linarith) (by linarith) le_rfl (by norm_num)
    le_rfl (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc3, hCc3, hC3⟩ := i3Psi2ChainLeftWeighted_twoLevelLe (B := B) (δ := δ) (α := 0)
    (β₀ := 0) (γ := 2 * θ) (η := δ + 2 * θ) hB hδ le_rfl (by norm_num) (by linarith)
    (by linarith) le_rfl (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc4, hCc4, hC4⟩ := i3Psi2ChainLeftWeighted_twoLevelLe (B := B) (δ := δ) (α := 0)
    (β₀ := 0) (γ := 0) (η := δ) hB hδ le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cn1, hCn1, hN1⟩ := i3Psi2N1Weighted_twoLevelLe (B := B) (δ := δ) (x₁ := 0)
    (x₂ := 2 * θ) (x₃ := 0) hB hδ le_rfl (by linarith) le_rfl (by linarith)
  obtain ⟨Cn2, hCn2, hN2⟩ := i3Psi2N1Weighted_twoLevelLe (B := B) (δ := δ) (x₁ := 2 * θ)
    (x₂ := 0) (x₃ := 0) hB hδ (by linarith) le_rfl le_rfl (by linarith)
  obtain ⟨Cn3, hCn3, hN3⟩ := i3Psi2N1Weighted_twoLevelLe (B := B) (δ := δ) (x₁ := 0)
    (x₂ := 0) (x₃ := 2 * θ) hB hδ le_rfl le_rfl (by linarith) (by linarith)
  refine ⟨737280 * A ^ 5 * (Cp1 + Cp2 + Cc1 + Cc2 + Cc3 + Cc4 + Cn1 + Cn2 + Cn3),
    by positivity, ?_⟩
  intro K Q₁₁ Q₁₂ Q₂₁ Q₂₂ μ hμ hKm hQ11 hQ12 hQ21 hQ22 hK hinc hKs hT z z' hzz hz hz' hz1 hz1'
  set K0 : ℝ := 737280 * A ^ 5 with hK0
  have hK0n : 0 ≤ K0 := by positivity
  have hΛ : 0 ≤ K0 * μ ^ 2 := by positivity
  have rn : ∀ e : ℝ, 0 ≤ torusParabolicSize (z - z') ^ e :=
    fun e => Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have e2 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(2 : ℝ)) := mul_nonneg hΛ (rn _)
  have e22 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) := mul_nonneg hΛ (rn _)
  have e1 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := mul_nonneg hΛ (rn _)
  have e12 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) := mul_nonneg hΛ (rn _)
  have t11 := hP1 e2 hKm hK hinc hKs z z' hz1 hz1'
  have t12 := hP2 e22 hKm hK hinc hKs z z' hz1 hz1'
  have t21 := hC1 e1 hKm hK hKs z z' z' z hzz hz hz' hz1 hz1' (Or.inr ⟨rfl, rfl⟩)
  have t22 := hC2 e1 hKm hK hKs z z' z' z hzz hz hz' hz1 hz1' (Or.inr ⟨rfl, rfl⟩)
  have t23 := hC3 e1 hKm hK hKs z z' z' z hzz hz hz' hz1 hz1' (Or.inr ⟨rfl, rfl⟩)
  have t24 := hC4 e12 hKm hK hKs z z' z' z hzz hz hz' hz1 hz1' (Or.inr ⟨rfl, rfl⟩)
  have t31 := hN1 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have t32 := hN2 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  have t33 := hN3 hΛ hKm hK hKs z z' hzz hz hz' hz1 hz1'
  simp only [add_zero] at t12 t21 t22 t23 t24 t31 t32 t33
  set F : SpaceTime → SpaceTime → ℝ := fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
    i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - v) (w - z') (z - v) (z - z') with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun p : SpaceTime × SpaceTime => i3Psi2dK K z p.1 * i3Psi2dK K z' p.2 *
      i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (p.1 - p.2) (p.1 - z') (z - p.2) (z - z'))
    unfold i3Psi2dK i3Psi2DiffChi5 i3Psi2Kernel5
    fun_prop
  have hsum := (((((((t11.add t12).add t21).add t22).add t23).add t24).add t31).add t32).add t33
  obtain ⟨hint, hbd⟩ := TwoLevelLe.integrable_bound (F := F) hFm.aestronglyMeasurable hsum (by
    filter_upwards [ae_ae_diffDouble_pos z z'] with w hw
    obtain ⟨⟨-, -, hz'w⟩, hw'⟩ := hw
    filter_upwards [hw'] with v hv
    obtain ⟨⟨-, -, hzv⟩, hwv⟩ := hv
    have hch := i3Psi2DiffChi5_abs_le hμ hA hT hwv (torusParabolicSize_sub_pos_symm hz'w) hzv hzz
    have hnn : 0 ≤ |i3Psi2dK K z w| * |i3Psi2dK K z' v| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hch hnn
    refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
    · simp only [hFdef, abs_mul]
    · unfold i3Psi2DiffT1 i3Psi2DiffT2 i3Psi2DiffT3
      ring)
  refine ⟨hint, hbd.trans ?_⟩
  have c11 := principal_raised_le_diffTarget δ θ z z'
  have c12 := principal_far_le_diffTarget δ θ z z'
  have c2 := chain_raised_le_diffTarget (δ := δ) (θ := θ) hzz
  have c24 := chain_far_le_diffTarget (δ := δ) (θ := θ) hzz
  have c3 := S_one_add_le_diffTarget (θ := θ) hδ hz hz' hz1 hz1'
  have Tn := i3Psi2DiffTarget_nonneg δ θ z z'
  have b11 : K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(2 : ℝ)) * Cp1 *
      torusParabolicSize z' ^ (1 - δ - 2 * θ) ≤ K0 * μ ^ 2 * Cp1 * i3Psi2DiffTarget δ θ z z' := by
    calc _ = K0 * μ ^ 2 * Cp1 * (torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
          torusParabolicSize z' ^ (1 - δ - 2 * θ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left c11 (by positivity)
  have b12 : K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) * Cp2 *
      torusParabolicSize z' ^ (1 - δ) ≤ K0 * μ ^ 2 * Cp2 * i3Psi2DiffTarget δ θ z z' := by
    calc _ = K0 * μ ^ 2 * Cp2 * (torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) *
          torusParabolicSize z' ^ (1 - δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left c12 (by positivity)
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
  have b21 := b2 Cc1 hCc1
  have b22 := b2 Cc2 hCc2
  have b23 := b2 Cc3 hCc3
  have b31 := b3 Cn1 hCn1
  have b32 := b3 Cn2 hCn2
  have b33 := b3 Cn3 hCn3
  linarith [b11, b12, b21, b22, b23, b24, b31, b32, b33]

end RegularityStructures.Phi43

end

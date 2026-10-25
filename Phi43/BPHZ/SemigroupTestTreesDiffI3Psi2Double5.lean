/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceDouble5
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Alg
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Principal
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Chain
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2N1
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2N2

/-!
# The chaos-`5` double integral of the difference of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

`i3Psi2DiffDouble5_bound_global`: for arbitrary `z, z'` (with `z, z', z - z'` away from the origin)
and `D` bounding `s(a - b)` on the time window `|a.1|, |b.1| ≤ |z.1| + |z'.1| + 2`,
`|∫∫ δK δK χ₅^Δ| ≤ C μ² (1 + |z.1| + D^δ) treeTheta z z'`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem diff_term_le {L C d X W k T : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hd : 0 ≤ d) (hdX : d ≤ X)
    (hW : 0 ≤ W) (hWk : W ≤ k * T) : L * C * d * W ≤ L * C * k * (X * T) := by
  have hX : 0 ≤ X := hd.trans hdX
  calc L * C * d * W = L * C * (d * W) := by ring
    _ ≤ L * C * (X * (k * T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hdX hWk hW hX) (mul_nonneg hL hC)
    _ = _ := by ring

theorem diff_prin_le {L σ Cp t d T : ℝ} (hL : 0 ≤ L) (hCp : 0 ≤ Cp) (ht : 0 ≤ t) (hσ : 0 ≤ σ)
    (hσT : σ ≤ T) (hd : 0 ≤ d) :
    L * σ * Cp * (1 + (t + 1)) ≤ 2 * L * Cp * ((1 + t + d) * T) := by
  have hT : 0 ≤ T := hσ.trans hσT
  have h1 : 1 + (t + 1) ≤ 2 * (1 + t + d) := by linarith
  calc L * σ * Cp * (1 + (t + 1)) = L * Cp * (σ * (1 + (t + 1))) := by ring
    _ ≤ L * Cp * (T * (2 * (1 + t + d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hσT h1 (by linarith) hT) (mul_nonneg hL hCp)
    _ = _ := by ring

/-- **The chaos-`5` double integral of the difference, for arbitrary `z, z'`.** -/
theorem i3Psi2DiffDouble5_bound_global {B A δ θ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} {μ D : ℝ}, 0 ≤ μ → 0 ≤ D →
      Measurable K → Measurable Q₁₁ → Measurable Q₁₂ → Measurable Q₂₁ → Measurable Q₂₂ →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂ →
      ∀ z z' : SpaceTime,
        (∀ a b : SpaceTime, |a.1| ≤ |z.1| + |z'.1| + 2 → |b.1| ≤ |z.1| + |z'.1| + 2 →
          torusParabolicSize (a - b) ≤ D) →
        0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        Integrable (Function.uncurry fun w v => i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - v) (w - z') (z - v) (z - z'))
          (volume.prod volume) ∧
        |∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ (w - v) (w - z') (z - v) (z - z')| ≤
          C * μ ^ 2 * (1 + |z.1| + D ^ δ) * treeTheta z z' := by
  obtain ⟨Cp1, hCp1, hP1⟩ := i3Psi2PrincipalWeighted_twoLevelLe_global (B := B) (τ := 2 * θ) hB
    (by linarith) (by linarith)
  obtain ⟨Cp2, hCp2, hP2⟩ := i3Psi2PrincipalWeighted_twoLevelLe_global (B := B) (τ := 0) hB
    le_rfl (by norm_num)
  obtain ⟨Cc1, hCc1, hC1⟩ := i3Psi2ChainLeftWeighted_twoLevelLe_global (B := B) (δ := δ) (α := 0)
    (β₀ := 2 * θ) (γ := 0) (η := δ + 2 * θ) hB hδ le_rfl (by norm_num) le_rfl (by norm_num)
    (by linarith) (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc2, hCc2, hC2⟩ := i3Psi2ChainLeftWeighted_twoLevelLe_global (B := B) (δ := δ)
    (α := 2 * θ) (β₀ := 0) (γ := 0) (η := δ + 2 * θ) hB hδ (by linarith) (by linarith) le_rfl
    (by norm_num) le_rfl (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc3, hCc3, hC3⟩ := i3Psi2ChainLeftWeighted_twoLevelLe_global (B := B) (δ := δ) (α := 0)
    (β₀ := 0) (γ := 2 * θ) (η := δ + 2 * θ) hB hδ le_rfl (by norm_num) (by linarith)
    (by linarith) le_rfl (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cc4, hCc4, hC4⟩ := i3Psi2ChainLeftWeighted_twoLevelLe_global (B := B) (δ := δ) (α := 0)
    (β₀ := 0) (γ := 0) (η := δ) hB hδ le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    (by linarith) (by ring) (by linarith) (by linarith)
  obtain ⟨Cn1, hCn1, hN1⟩ := i3Psi2N1Weighted_twoLevelLe_global (B := B) (δ := δ) (x₁ := 0)
    (x₂ := 2 * θ) (x₃ := 0) hB hδ le_rfl (by linarith) le_rfl (by linarith)
  obtain ⟨Cn2, hCn2, hN2⟩ := i3Psi2N1Weighted_twoLevelLe_global (B := B) (δ := δ) (x₁ := 2 * θ)
    (x₂ := 0) (x₃ := 0) hB hδ (by linarith) le_rfl le_rfl (by linarith)
  obtain ⟨Cn3, hCn3, hN3⟩ := i3Psi2N1Weighted_twoLevelLe_global (B := B) (δ := δ) (x₁ := 0)
    (x₂ := 0) (x₃ := 2 * θ) hB hδ le_rfl le_rfl (by linarith) (by linarith)
  refine ⟨737280 * A ^ 5 * (2 * Cp1 + 2 * Cp2 + 6 * (Cc1 + Cc2 + Cc3 + Cc4) +
    3 * (Cn1 + Cn2 + Cn3)), by positivity, ?_⟩
  intro K Q₁₁ Q₁₂ Q₂₁ Q₂₂ μ D hμ hD0 hKm hQ11 hQ12 hQ21 hQ22 hK hKs hT z z' hD hzz hz hz'
  set K0 : ℝ := 737280 * A ^ 5 with hK0
  have hK0n : 0 ≤ K0 := by positivity
  have hΛ : 0 ≤ K0 * μ ^ 2 := by positivity
  have hDslab : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D := fun w v hw hv =>
    hD w v (by linarith [abs_nonneg z'.1]) (by linarith [abs_nonneg z.1])
  have hDn1 : ∀ w : SpaceTime, |w.1| ≤ |z.1| + 1 → torusParabolicSize (z' - w) ≤ D :=
    fun w hw => hD z' w (by linarith [abs_nonneg z.1]) (by linarith [abs_nonneg z'.1])
  have rn : ∀ e : ℝ, 0 ≤ torusParabolicSize (z - z') ^ e :=
    fun e => Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have e2 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(2 : ℝ)) := mul_nonneg hΛ (rn _)
  have e22 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) := mul_nonneg hΛ (rn _)
  have e1 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 : ℝ)) := mul_nonneg hΛ (rn _)
  have e12 : 0 ≤ K0 * μ ^ 2 * torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) := mul_nonneg hΛ (rn _)
  have t11 := hP1 e2 hKm hK hKs z z'
  have t12 := hP2 e22 hKm hK hKs z z'
  have t21 := hC1 e1 hD0 hKm hK hKs z z' z' z hDslab hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have t22 := hC2 e1 hD0 hKm hK hKs z z' z' z hDslab hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have t23 := hC3 e1 hD0 hKm hK hKs z z' z' z hDslab hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have t24 := hC4 e12 hD0 hKm hK hKs z z' z' z hDslab hzz hz hz' (Or.inr ⟨rfl, rfl⟩)
  have t31 := hN1 hΛ hD0 hKm hK hKs z z' hDn1 hzz hz hz'
  have t32 := hN2 hΛ hD0 hKm hK hKs z z' hDn1 hzz hz hz'
  have t33 := hN3 hΛ hD0 hKm hK hKs z z' hDn1 hzz hz hz'
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
  -- numerics
  set Θ := treeTheta z z' with hΘ
  set t : ℝ := |z.1| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hd0 : 0 ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hΘ0 : 0 ≤ Θ := treeTheta_nonneg z z'
  have hdX : D ^ δ ≤ 1 + t + D ^ δ := by linarith
  have s2 : torusParabolicSize (z - z') ^ (-(2 : ℝ)) ≤ Θ :=
    rpow_zz_le_treeTheta hzz (by norm_num) (by norm_num)
  have s22 : torusParabolicSize (z - z') ^ (-(2 + 2 * θ)) ≤ Θ :=
    rpow_zz_le_treeTheta hzz (by linarith) (by linarith)
  have q1 : ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 → torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      i3Psi2S η z z' ≤ 6 * Θ := fun η h0 h1 =>
    rpow_zz_mul_S_le_treeTheta hzz hz hz' (by norm_num) (by norm_num) h0 (by linarith)
  have q12 : ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 → torusParabolicSize (z - z') ^ (-(1 + 2 * θ)) *
      i3Psi2S η z z' ≤ 6 * Θ := fun η h0 h1 =>
    rpow_zz_mul_S_le_treeTheta hzz hz hz' (by linarith) (by linarith) h0 (by linarith)
  have s3 : i3Psi2S (1 + δ + 2 * θ) z z' ≤ 3 * Θ :=
    i3Psi2S_le_treeTheta hzz hz hz' (by linarith) (by linarith)
  have w11 := diff_prin_le (L := K0 * μ ^ 2) (σ := torusParabolicSize (z - z') ^ (-(2 : ℝ)))
    (Cp := Cp1) (t := t) (d := D ^ δ) (T := Θ) hΛ hCp1 ht0 (rn _) s2 hd0
  have w12 := diff_prin_le (L := K0 * μ ^ 2) (σ := torusParabolicSize (z - z') ^ (-(2 + 2 * θ)))
    (Cp := Cp2) (t := t) (d := D ^ δ) (T := Θ) hΛ hCp2 ht0 (rn _) s22 hd0
  have S0 := fun η : ℝ => i3Psi2S_nonneg η z z'
  have c := fun (σ Cc η : ℝ) (hCc : 0 ≤ Cc) (hW : 0 ≤ σ * i3Psi2S η z z')
      (hWk : σ * i3Psi2S η z z' ≤ 6 * Θ) =>
    diff_term_le (L := K0 * μ ^ 2) (C := Cc) (d := D ^ δ) (X := 1 + t + D ^ δ)
      (W := σ * i3Psi2S η z z') (k := 6) (T := Θ) hΛ hCc hd0 hdX hW hWk
  have w21 := c _ Cc1 (δ + 2 * θ) hCc1 (mul_nonneg (rn _) (S0 _))
    (q1 _ (by linarith) (by linarith))
  have w22 := c _ Cc2 (δ + 2 * θ) hCc2 (mul_nonneg (rn _) (S0 _))
    (q1 _ (by linarith) (by linarith))
  have w23 := c _ Cc3 (δ + 2 * θ) hCc3 (mul_nonneg (rn _) (S0 _))
    (q1 _ (by linarith) (by linarith))
  have w24 := c _ Cc4 δ hCc4 (mul_nonneg (rn _) (S0 _)) (q12 _ (by linarith) (by linarith))
  have n := fun (Cn : ℝ) (hCn : 0 ≤ Cn) =>
    diff_term_le (L := K0 * μ ^ 2) (C := Cn) (d := D ^ δ) (X := 1 + t + D ^ δ)
      (W := i3Psi2S (1 + δ + 2 * θ) z z') (k := 3) (T := Θ) hΛ hCn hd0 hdX (S0 _) s3
  have w31 := n Cn1 hCn1
  have w32 := n Cn2 hCn2
  have w33 := n Cn3 hCn3
  rw [ht] at w11 w12 w21 w22 w23 w24 w31 w32 w33 ⊢
  linarith [w11, w12, w21, w22, w23, w24, w31, w32, w33]

end RegularityStructures.Phi43

end

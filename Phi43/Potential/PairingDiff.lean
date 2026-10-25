/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.DerivHyp
public import RegularityStructures.Abstract.Singular.TwoModel.Bounds
public import RegularityStructures.Abstract.Singular.TwoModel.Realising
public import RegularityStructures.Abstract.Singular.TwoModel.Sector
public import Phi43.Potential.Convolution
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Two-model derivative bounds of `Q ∗ ξ`

For two polynomial-compatible models `M₁, M₂` realising continuous functions `ξ₁, ξ₂` of polynomial
growth in a non-polynomial symbol `o` (`Q_t Π^i_x e_o = Q_t ξ_i`), the difference model
`M⊕ = modelSum M₁ M₂` (parameter `λ > 0`) realises `λ⁻¹ (ξ₁ - ξ₂)` in the symbol `inl o`.  Applying
`abs_ddA_potConv_le` to `M⊕` bounds `∂^l (Q ∗ ξ₁ - Q ∗ ξ₂)(z)` by `λ` times the constants of `M⊕`
(`abs_ddA_potConv_sub_le`); with `λ` the size `d` of the model difference this is `d · K` with `K`
depending only on the constants of `M₁, M₂` (`abs_ddA_potConv_sub_le_of_diff`).
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

theorem hasCompactSupport_ddA_potQ_sub (N : ℕ) (l : List (Fin 4)) (z : ParabolicSpace) :
    HasCompactSupport (fun y => ddA l (potQ N) (z - y)) :=
  HasCompactSupport.intro (isCompact_closedBall z 1) fun y hy => by
    have hy' : z - y ∉ Metric.closedBall (0 : ParabolicSpace) 1 := by
      intro h
      apply hy
      rw [mem_closedBall_zero_iff, norm_sub_rev] at h
      rwa [mem_closedBall_iff_norm]
    exact ddA_potQ_eq_zero_of_one_lt N l (one_lt_parabolicNorm_of_not_mem_closedBall hy')

theorem potConv_const_mul_sub {ξ₁ ξ₂ : ParabolicSpace → ℝ} (h₁ : Continuous ξ₁)
    (h₂ : Continuous ξ₂) (c : ℝ) (N : ℕ) (l : List (Fin 4)) (z : ParabolicSpace) :
    potConv (fun w => c * (ξ₁ w - ξ₂ w)) (ddA l (potQ N)) z =
      c * (potConv ξ₁ (ddA l (potQ N)) z - potConv ξ₂ (ddA l (potQ N)) z) := by
  have hg : Continuous (fun y => ddA l (potQ N) (z - y)) :=
    (contDiff_ddA (contDiff_potQ N) l).continuous.comp (continuous_const.sub continuous_id)
  have hcs := hasCompactSupport_ddA_potQ_sub N l z
  have i₁ : Integrable (fun y => ξ₁ y * ddA l (potQ N) (z - y)) :=
    (h₁.mul hg).integrable_of_hasCompactSupport hcs.mul_left
  have i₂ : Integrable (fun y => ξ₂ y * ddA l (potQ N) (z - y)) :=
    (h₂.mul hg).integrable_of_hasCompactSupport hcs.mul_left
  unfold potConv
  rw [← integral_sub i₁ i₂, ← integral_const_mul]
  congr 1
  funext y
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

/-- Qualitative growth of the difference model at a point, from that of the two models. -/
theorem hasQualitativeGrowthAt_modelSum {lam : ℝ} (hlam : 0 < lam)
    (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) {γ : ℝ} {z : ParabolicSpace}
    (g₁ : M₁.HasQualitativeGrowthAt γ z) (g₂ : M₂.HasQualitativeGrowthAt γ z) :
    (TwoModel.modelSum (lam := lam) h₁ h₂).HasQualitativeGrowthAt γ z := by
  obtain ⟨C₁, β₁, q₁, hC₁, hq₁, e₁⟩ := g₁.exists_crude
  obtain ⟨C₂, β₂, q₂, hC₂, hq₂, e₂⟩ := g₂.exists_crude
  have hli : 0 ≤ lam⁻¹ := (inv_pos.2 hlam).le
  refine ⟨lam⁻¹ * (C₁ + C₂) + C₂, min β₁ β₂, max q₁ q₂, fun s hs t ht y => ?_⟩
  have hd : 0 ≤ parabolicNorm (y - z) := parabolicNorm_nonneg _
  have hb : (1 : ℝ) ≤ 1 + parabolicNorm (y - z) := by linarith
  have hT₁ : t ^ (β₁ / 4) ≤ t ^ (min β₁ β₂ / 4) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by gcongr; exact min_le_left _ _)
  have hT₂ : t ^ (β₂ / 4) ≤ t ^ (min β₁ β₂ / 4) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by gcongr; exact min_le_right _ _)
  have hQ₁ : (1 + parabolicNorm (y - z)) ^ q₁ ≤ (1 + parabolicNorm (y - z)) ^ (max q₁ q₂) :=
    Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
  have hQ₂ : (1 + parabolicNorm (y - z)) ^ q₂ ≤ (1 + parabolicNorm (y - z)) ^ (max q₁ q₂) :=
    Real.rpow_le_rpow_of_exponent_le hb (le_max_right _ _)
  have hT0 : 0 ≤ t ^ (min β₁ β₂ / 4) := Real.rpow_nonneg ht.1.le _
  have hQ0 : 0 ≤ (1 + parabolicNorm (y - z)) ^ (max q₁ q₂) := Real.rpow_nonneg (by linarith) _
  have k₁ : ∀ x : ℝ, |x| ≤ C₁ * t ^ (β₁ / 4) * (1 + parabolicNorm (y - z)) ^ q₁ →
      |x| ≤ C₁ * (t ^ (min β₁ β₂ / 4) * (1 + parabolicNorm (y - z)) ^ (max q₁ q₂)) :=
    fun x hx => hx.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hT₁ hQ₁ (Real.rpow_nonneg (by linarith) _) hT0) hC₁)
  have k₂ : ∀ x : ℝ, |x| ≤ C₂ * t ^ (β₂ / 4) * (1 + parabolicNorm (y - z)) ^ q₂ →
      |x| ≤ C₂ * (t ^ (min β₁ β₂ / 4) * (1 + parabolicNorm (y - z)) ^ (max q₁ q₂)) :=
    fun x hx => hx.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hT₂ hQ₂ (Real.rpow_nonneg (by linarith) _) hT0) hC₂)
  have hTQ : 0 ≤ t ^ (min β₁ β₂ / 4) * (1 + parabolicNorm (y - z)) ^ (max q₁ q₂) :=
    mul_nonneg hT0 hQ0
  set TQ := t ^ (min β₁ β₂ / 4) * (1 + parabolicNorm (y - z)) ^ (max q₁ q₂) with hTQdef
  rcases s with j | j
  · have hj : 𝒯.deg j.1 < γ := hs
    rw [TwoModel.regPi_modelSum, TwoModel.coe_piSum_single_inl, abs_mul,
      abs_of_nonneg hli]
    have a := k₁ _ (e₁ j.1 hj t ht y)
    have b := k₂ _ (e₂ j.1 hj t ht y)
    calc lam⁻¹ * |M₁.regPi z (Pi.single j.1 1) t y - M₂.regPi z (Pi.single j.1 1) t y|
        ≤ lam⁻¹ * (|M₁.regPi z (Pi.single j.1 1) t y| + |M₂.regPi z (Pi.single j.1 1) t y|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) hli
      _ ≤ lam⁻¹ * (C₁ * TQ + C₂ * TQ) := mul_le_mul_of_nonneg_left (add_le_add a b) hli
      _ = (lam⁻¹ * (C₁ + C₂)) * TQ := by ring
      _ ≤ (lam⁻¹ * (C₁ + C₂) + C₂) * TQ :=
          mul_le_mul_of_nonneg_right (by linarith) hTQ
      _ = _ := by rw [hTQdef]; ring
  · have hj : 𝒯.deg j < γ := hs
    rw [TwoModel.regPi_modelSum, TwoModel.coe_piSum_single_inr]
    have b := k₂ _ (e₂ j hj t ht y)
    calc |M₂.regPi z (Pi.single j 1) t y| ≤ C₂ * TQ := b
      _ ≤ (lam⁻¹ * (C₁ + C₂) + C₂) * TQ :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hli (add_nonneg hC₁ hC₂)]) hTQ
      _ = _ := by rw [hTQdef]; ring

theorem potInvMul_le_one {lam c : ℝ} (hl : 0 < lam) (hc : c ≤ lam) : lam⁻¹ * c ≤ 1 := by
  rw [inv_mul_le_iff₀ hl]; linarith

theorem hdeg_structSumU (P : PolynomialSector 𝒯 N') {γ : ℝ} (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∀ j, (TwoModel.structSumU P).deg j < γ → -4 < (TwoModel.structSumU P).deg j := by
  intro j hj
  rcases j with j | j
  · exact hdeg j.1 hj
  · exact hdeg j hj

end RegularityStructures.Potential

end

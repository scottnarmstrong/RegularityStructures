/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.NoiseModelHyp
public import Phi43.Potential.NearPairingDiff
public import RegularityStructures.Abstract.Integration.Commute.Reg

/-!
# The hypotheses `NoiseModelHyp` for the difference model

If `M₁, M₂` satisfy `NoiseModelHyp` for the noise coordinate `o ∉ range P.emb` realised by `ξ₁, ξ₂`,
and the differences of `Π` and `Γ` are bounded (`PiDiffBoundOn`, `GammaDiffNearOn`), then
`modelSum M₁ M₂` (parameter `λ`) satisfies `NoiseModelHyp` for the symbol `inl o`, realised by
`λ⁻¹ (ξ₁ - ξ₂)` (`NoiseModelHyp.modelSum`).
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem NoiseModelHyp.modelSum {lam : ℝ} (hlam : 0 < lam) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) {γ CPi₁ CPi₂ CG₁ CG₂ CdPi CdGam : ℝ} {o : ι}
    {ξ₁ ξ₂ : ParabolicSpace → ℝ} (H₁ : NoiseModelHyp M₁ γ CPi₁ CG₁ o ξ₁)
    (H₂ : NoiseModelHyp M₂ γ CPi₂ CG₂ o ξ₂)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow)
    (h0 : 0 ≤ max (max CG₁ CG₂) (lam⁻¹ * CdGam)) (hnp : o ∉ Set.range P.emb) :
    NoiseModelHyp (TwoModel.modelSum (lam := lam) h₁ h₂) γ (max CPi₂ (lam⁻¹ * CdPi))
      (max (max CG₁ CG₂) (lam⁻¹ * CdGam)) (Sum.inl ⟨o, hnp⟩ : TwoModel.NonPoly P ⊕ ι)
      (fun y => lam⁻¹ * (ξ₁ y - ξ₂ y)) where
  pi := TwoModel.piBoundOn_modelSum h₁ h₂ hlam H₂.pi hdPi
  cpi := H₂.cpi.trans (le_max_left _ _)
  gam := TwoModel.gammaBoundOn_modelSum_near h₁ h₂ hlam h0 H₁.gam H₂.gam hdGam
  deg := hdeg_structSumU P H₁.deg
  ho := H₁.ho
  cont := continuous_const.mul (H₁.cont.sub H₂.cont)
  poly := by
    have hp₁ : PolyBounded ξ₁ := ⟨H₁.cont.measurable, H₁.poly⟩
    have hp₂ : PolyBounded ξ₂ := ⟨H₂.cont.measurable, H₂.poly⟩
    exact ((hp₁.sub hp₂).const_mul lam⁻¹).2
  reg x t ht y := by
    have hp₁ : PolyBounded ξ₁ := ⟨H₁.cont.measurable, H₁.poly⟩
    have hp₂ : PolyBounded ξ₂ := ⟨H₂.cont.measurable, H₂.poly⟩
    rw [TwoModel.regPi_modelSum, TwoModel.coe_piSum_single_inl, H₁.reg x t ht,
      H₂.reg x t ht, TwoModel.apply_const_mul_sub hp₁ hp₂ _ ht]
  growth z a b := hasQualitativeGrowthAt_modelSum hlam h₁ h₂ (H₁.growth z a b) (H₂.growth z a b)
  bdd := by
    obtain ⟨B₁, h1⟩ := H₁.bdd
    obtain ⟨B₂, h2⟩ := H₂.bdd
    refine ⟨lam⁻¹ * (B₁ + B₂), fun y hy1 hy2 => ?_⟩
    rw [abs_mul, abs_of_pos (inv_pos.2 hlam)]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (h1 y hy1 hy2)
      (h2 y hy1 hy2))) (inv_pos.2 hlam).le

end RegularityStructures.Potential

end

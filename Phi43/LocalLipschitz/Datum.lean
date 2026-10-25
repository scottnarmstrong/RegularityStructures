/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.Forcing
public import Phi43.Potential.HolderBesovConvBound
public import Phi43.Potential.HolderBesovConvBoundDiff
public import Phi43.Reconstruction.PsiSmooth
public import Phi43.Reconstruction.Path
public import RegularityStructures.PDE.TorusLift

/-!
# The potential bound at a restart, from the enlarged model

`psiSlice N κ noise C s` is the time slice `Ψ(s, ·) = (K ∗ ξ)(s, ·)` as a continuous function on
`T³`.  Its `η`-norm is bounded by the window bounds of the enlarged model at the restart and the
massive potential near `s` (`holderBesovENorm_psiSlice_le`), and the same for the difference of two
noises (`holderBesovENorm_psiSlice_sub_le`, linear in the window differences of the two enlarged
models, obtained from `holderBesovENorm_conv_sub_le` by letting its parameter `λ ↓ d`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Inhomogeneity

theorem phi43PsiAt_periodic (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (s : ℝ) (a b : Fin 3 → ℝ) (h : torusProj a = torusProj b) :
    phi43PsiAt N κ noise C (s, a) = phi43PsiAt N κ noise C (s, b) := by
  have hc : torusProj (a - b) = 0 := by
    rw [PDE.torusProj_sub, h, sub_self]
  have := (perSmooth_phi43PsiAt N κ noise C).periodic (s, b) (a - b) hc
  simpa using this

/-- The time slice `Ψ(s, ·)` on `T³`. -/
def psiSlice (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants)
    (s : ℝ) : C(Torus3, ℝ) :=
  ((descend2 (phi43PsiAt N κ noise C) (perSmooth_phi43PsiAt N κ noise C).smooth.continuous
    (phi43PsiAt_periodic N κ noise C)).curry s)

end RegularityStructures.Phi43.LocalLipschitz

end

public section

open Set

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential RegularityStructures.Phi43.Potential
  RegularityStructures.Phi43.LiftBounds RegularityStructures.Inhomogeneity

theorem psiSlice_apply (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants)
    (s : ℝ) (x : Fin 3 → ℝ) : psiSlice N κ noise C s (torusProj x) = phi43PsiAt N κ noise C (s, x) :=
  descend2_apply (phi43PsiAt N κ noise C) (perSmooth_phi43PsiAt N κ noise C).smooth.continuous
    (phi43PsiAt_periodic N κ noise C) s x

theorem psiSlice_apply_conv (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (s : ℝ) (x : Fin 3 → ℝ) :
    psiSlice N κ noise C s (torusProj x) = hairerConvolution N noise.zeta (s, x) := by
  rw [psiSlice_apply, phi43PsiAt_eq]

variable {κ : Kappa} {M M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {noise noise₁ noise₂ : CanonicalNoise} {s : ℝ}

/-- The constant of the potential bound at the restart. -/
@[expose] noncomputable def l8Const (N : ℕ) (κ : Kappa) : ℝ :=
  max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
      (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1) *
    (potKernelConst (potTail N) + potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise)))

/-- **The potential bound at a restart.** -/
theorem holderBesovENorm_psiSlice_le (N : ℕ) {CPi CGam : ℝ}
    (H : NoiseModelHyp M κ.1 CPi CGam (.old .noise) (potShift s noise.zeta))
    {f : SpaceTime → ℝ} (hfz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    (hgf : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : RegularityStructures.IsMassivePotential f ψ) (C : RenormalisationConstants) (η : ℝ) (hη : η ≤ 0)
    {N' : ℝ} (hN' : 0 ≤ N') (hψN : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ r) ≤ ENNReal.ofReal N') :
    holderBesovENorm η (psiSlice N κ noise C s) ≤ ENNReal.ofReal
      (r4ModelConst (phi43RegularityStructureF κ) κ.1 * (max 1 CGam * CPi) *
        (potKernelConst (potTail N) + potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise))) + 2 * N') :=
  holderBesovENorm_conv_le H N (potForcing_of_growth hfz hgf) hfz noise.smooth.continuous hψ η hη
    hN' hψN _ (psiSlice_apply_conv N κ noise C s)

private theorem le_of_forall_pos_ofReal_le {x : ENNReal} {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ ENNReal.ofReal (a + ε * b)) : x ≤ ENNReal.ofReal a := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := hε
  refine (h (ε / (b + 1)) (div_pos hε' (by linarith))).trans
    (ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_))
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- **The potential bound for two noises at a restart**, linear in the window differences `d` of the
two enlarged models. -/
theorem holderBesovENorm_psiSlice_sub_le (N : ℕ) {CPi CG CdPi CdGam d : ℝ}
    (H₁ : NoiseModelHyp M₁ κ.1 CPi CG (.old .noise) (potShift s noise₁.zeta))
    (H₂ : NoiseModelHyp M₂ κ.1 CPi CG (.old .noise) (potShift s noise₂.zeta))
    (h₁ : M₁.IsPolyCompatible (phi43PolynomialSectorF κ))
    (h₂ : M₂.IsPolyCompatible (phi43PolynomialSectorF κ))
    (hdPi : M₁.PiDiffBoundOn M₂ κ.1 CdPi hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ κ.1 CdGam hairerTimeWindow)
    (hCG : 0 ≤ CG) (hCdPi : CdPi ≤ d) (hCdGam : CdGam ≤ d) (hd : 0 ≤ d)
    {f₁ f₂ : SpaceTime → ℝ} (hfz₁ : ∀ z : ParabolicSpace, noise₁.zeta z = f₁ (z.1, torusProj z.2))
    (hfz₂ : ∀ z : ParabolicSpace, noise₂.zeta z = f₂ (z.1, torusProj z.2))
    (hg₁ : Statements.HasPhi43NoiseGrowth f₁) (hg₂ : Statements.HasPhi43NoiseGrowth f₂)
    {ψ₁ ψ₂ : ℝ → C(Torus3, ℝ)} (hψ₁ : RegularityStructures.IsMassivePotential f₁ ψ₁)
    (hψ₂ : RegularityStructures.IsMassivePotential f₂ ψ₂) (C C' : RenormalisationConstants) (η : ℝ) (hη : η ≤ 0)
    {δψ : ℝ} (hδψ : 0 ≤ δψ)
    (hψN : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ₁ r - ψ₂ r) ≤ ENNReal.ofReal δψ) :
    holderBesovENorm η (psiSlice N κ noise₁ C s - psiSlice N κ noise₂ C' s) ≤ ENNReal.ofReal
      (d * (max 1 CG * max CPi 1 * l8Const N κ) + 2 * δψ) := by
  have hK : 0 ≤ potKernelConst (potTail N) + potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise)) := by
    exact add_nonneg (potKernelConst_pos (isUnitKernel_potTail N)).le (potK1Const_nonneg N _)
  have hX : 0 ≤ max 1 CG * max CPi 1 * l8Const N κ := by
    unfold l8Const
    exact mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (zero_le_one.trans (le_max_right _ _)))
      (mul_nonneg ((r4ModelConst_F_nonneg κ).trans (le_max_left _ _)) hK)
  refine le_of_forall_pos_ofReal_le hX fun ε hε => ?_
  set lam : ℝ := d + ε with hlam
  have hlam0 : 0 < lam := by linarith
  have h0 : 0 ≤ max (max CG CG) (lam⁻¹ * CdGam) := hCG.trans ((le_max_left _ _).trans (le_max_left _ _))
  have key := holderBesovENorm_conv_sub_le hlam0 h₁ h₂ H₁ H₂ hdPi hdGam h0
    (old_noise_notMem_range_emb κ) N (potForcing_of_growth hfz₁ hg₁)
    (potForcing_of_growth hfz₂ hg₂) hfz₁ hfz₂ noise₁.smooth.continuous noise₂.smooth.continuous
    hψ₁ hψ₂ η hη hδψ hψN _ _ (psiSlice_apply_conv N κ noise₁ C s)
    (psiSlice_apply_conv N κ noise₂ C' s)
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hq1 : lam⁻¹ * CdGam ≤ 1 := by
    rw [inv_mul_le_iff₀ hlam0]; linarith
  have hq2 : lam⁻¹ * CdPi ≤ 1 := by
    rw [inv_mul_le_iff₀ hlam0]; linarith
  have hm1 : max 1 (max (max CG CG) (lam⁻¹ * CdGam)) ≤ max 1 CG := by
    rw [max_self]
    exact max_le (le_max_left _ _) (max_le (le_max_right _ _) (hq1.trans (le_max_left _ _)))
  have hm2 : max CPi (lam⁻¹ * CdPi) ≤ max CPi 1 := max_le_max le_rfl hq2
  have hr := r4ModelConst_sum_nonneg κ
  have hrm : r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1 ≤
      max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
        (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1) := le_max_right _ _
  have hA : 0 ≤ max 1 (max (max CG CG) (lam⁻¹ * CdGam)) := zero_le_one.trans (le_max_left _ _)
  have hB : 0 ≤ max CPi (lam⁻¹ * CdPi) := by
    rcases le_or_gt 0 CPi with h | h
    · exact h.trans (le_max_left _ _)
    · exact (mul_nonneg (inv_nonneg.2 hlam0.le) (le_trans (by
        have := H₁.cpi; linarith) (le_refl CdPi))).trans (le_max_right _ _)
  have hstep : r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1 *
      (max 1 (max (max CG CG) (lam⁻¹ * CdGam)) * max CPi (lam⁻¹ * CdPi)) *
      (potKernelConst (potTail N) + potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise))) ≤
      max 1 CG * max CPi 1 * l8Const N κ := by
    unfold l8Const
    have := mul_le_mul hm1 hm2 hB (zero_le_one.trans (le_max_left _ _))
    calc _ ≤ max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
            (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1) *
          (max 1 CG * max CPi 1) *
          (potKernelConst (potTail N) + potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise))) := by
          gcongr
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_left hstep hlam0.le
  have e : lam * (max 1 CG * max CPi 1 * l8Const N κ) =
      d * (max 1 CG * max CPi 1 * l8Const N κ) + ε * (max 1 CG * max CPi 1 * l8Const N κ) := by
    rw [hlam]; ring
  linarith

end RegularityStructures.Phi43.LocalLipschitz

end

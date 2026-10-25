/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.NoiseHyp
public import Phi43.Potential.NearPairing
public import Phi43.Potential.NearPairingDiff
public import Phi43.Potential.ZetaDiff
public import Phi43.Inhomogeneity.DuhamelBounds
public import Phi43.Potential.TestFunction

/-!
# Derivative bounds of the restarted forcing, from the enlarged model

The forcing bound at a restart, in the `DerivHyp` form consumed by the inhomogeneity
`phi43InhomTheta`, with one derivative-constant sequence `forcingGc N κ` for the single forcing and
for the difference of two forcings:

* `derivHyp_zeta_enlarged`: `ζ_s = Q ∗ ξ(s + ·)` has derivative bounds `forcingGc N κ L · B` with
  `B = max 1 C_Γ · C_Π`, from `NoiseModelHyp` of the enlarged model at level `κ`;
* `derivHyp_zeta_sub_enlarged`: the difference of two such forcings has derivative bounds
  `forcingGc N κ L · d · max 1 (max C_{Γ₁} C_{Γ₂}) · max C_{Π₂} 1` when the window differences of the
  two enlarged models are bounded by `d`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential

/-- The derivative-constant sequence of the restarted forcings (single and difference). -/
def forcingGc (N : ℕ) (κ : Kappa) (L : ℕ) : ℝ :=
  potWordConst N L * max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
    (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1)

end RegularityStructures.Phi43.LocalLipschitz

end

public section

open Set
open scoped ContDiff

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential RegularityStructures.Phi43.Potential
  RegularityStructures.Phi43.LiftBounds RegularityStructures.Inhomogeneity

theorem r4ModelConst_F_nonneg (κ : Kappa) :
    0 ≤ r4ModelConst (phi43RegularityStructureF κ) κ.1 :=
  r4ModelConst_nonneg _ (fun j _ => phi43DegreeF_gt_neg_four κ j)

theorem r4ModelConst_sum_nonneg (κ : Kappa) :
    0 ≤ r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1 :=
  r4ModelConst_nonneg _ (hdeg_structSumU _ (fun j _ => phi43DegreeF_gt_neg_four κ j))

theorem forcingGc_nonneg (N : ℕ) (κ : Kappa) (L : ℕ) : 0 ≤ forcingGc N κ L :=
  mul_nonneg (potWordConst_nonneg N L) ((r4ModelConst_F_nonneg κ).trans (le_max_left _ _))

theorem derivHyp_mono {g : ParabolicSpace → ℝ} {B B' : ℝ} {L : ℕ} (h : DerivHyp g B L)
    (hB : B ≤ B') : DerivHyp g B' L := fun l hl s hs y => (h l hl s hs y).trans hB

/-- The old noise symbol is not polynomial. -/
theorem old_noise_notMem_range_emb (κ : Kappa) :
    SymbolF.old .noise ∉ Set.range (phi43PolynomialSectorF κ).emb := by
  rintro ⟨k, hk⟩
  have h1 := (phi43PolynomialSectorF κ).deg_emb k
  rw [hk] at h1
  have h2 : (0 : ℝ) ≤ polyDeg 3 k := Nat.cast_nonneg _
  have h3 := phi43DegreeF_old_noise_lt κ
  have h4 : phi43DegreeF κ (.old .noise) < 0 := by
    change homogeneity κ .noise < 0
    simp only [homogeneity]
    linarith [κ.2.1]
  change phi43DegreeF κ (.old .noise) = _ at h1
  linarith

variable {κ : Kappa} {M M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {noise noise₁ noise₂ : CanonicalNoise} {s : ℝ}

/-- **The forcing bound for the enlarged model at a restart.** -/
theorem derivHyp_zeta_enlarged (N : ℕ) {CPi CGam : ℝ}
    (H : NoiseModelHyp M κ.1 CPi CGam (.old .noise) (potShift s noise.zeta)) (L : ℕ) :
    DerivHyp (potZeta noise.zeta N s) (forcingGc N κ L * (max 1 CGam * CPi)) L := by
  obtain ⟨B, n, hB⟩ := H.poly
  have key := derivHyp_potConv_near M H.pi H.cpi H.gam H.deg H.ho H.cont hB H.reg H.growth N L
  refine derivHyp_mono key ?_
  have hX : 0 ≤ max 1 CGam * CPi := mul_nonneg (zero_le_one.trans (le_max_left _ _)) H.cpi
  unfold potGc forcingGc
  have h1 := potWordConst_nonneg N L
  have h2 : r4ModelConst (phi43RegularityStructureF κ) κ.1 * potWordConst N L ≤
      potWordConst N L * max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
        (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) h1
  exact mul_le_mul_of_nonneg_right h2 hX

/-- **The forcing bound for two enlarged models at a restart.** -/
theorem derivHyp_zeta_sub_enlarged (N : ℕ) {CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam d : ℝ}
    (H₁ : NoiseModelHyp M₁ κ.1 CPi₁ CGam₁ (.old .noise) (potShift s noise₁.zeta))
    (H₂ : NoiseModelHyp M₂ κ.1 CPi₂ CGam₂ (.old .noise) (potShift s noise₂.zeta))
    (h₁ : M₁.IsPolyCompatible (phi43PolynomialSectorF κ))
    (h₂ : M₂.IsPolyCompatible (phi43PolynomialSectorF κ))
    (hdPi : M₁.PiDiffBoundOn M₂ κ.1 CdPi hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ κ.1 CdGam hairerTimeWindow)
    (hCGam₁ : 0 ≤ CGam₁) (hCdPi : CdPi ≤ d) (hCdGam : CdGam ≤ d) (hd : 0 ≤ d) (L : ℕ) :
    DerivHyp (potZeta noise₁.zeta N s - potZeta noise₂.zeta N s)
      (forcingGc N κ L * (d * (max 1 (max CGam₁ CGam₂) * max CPi₂ 1))) L := by
  obtain ⟨B₁, n₁, hB₁⟩ := H₁.poly
  obtain ⟨B₂, n₂, hB₂⟩ := H₂.poly
  have hp₁ : PolyBounded (potShift s noise₁.zeta) := ⟨H₁.cont.measurable, B₁, n₁, hB₁⟩
  have hp₂ : PolyBounded (potShift s noise₂.zeta) := ⟨H₂.cont.measurable, B₂, n₂, hB₂⟩
  intro l hl s' hs y
  have key := abs_ddA_potConv_sub_le_of_diff_near h₁ h₂ H₂.pi H₂.cpi hdPi H₁.gam H₂.gam hdGam
    hCGam₁ hCdPi hCdGam hd H₁.deg H₁.ho (old_noise_notMem_range_emb κ) hp₁ hp₂ H₁.cont H₂.cont
    H₁.reg H₂.reg H₁.growth H₂.growth N l (z := (s', y)) hs.1 hs.2
  have hsm₁ : ContDiff ℝ ∞ (potZeta noise₁.zeta N s) :=
    contDiff_potConv H₁.cont (contDiff_potQ N) (by simpa [ddA] using hasCompactSupport_ddA_potQ N [])
  have hsm₂ : ContDiff ℝ ∞ (potZeta noise₂.zeta N s) :=
    contDiff_potConv H₂.cont (contDiff_potQ N) (by simpa [ddA] using hasCompactSupport_ddA_potQ N [])
  rw [ddA_sub hsm₁ hsm₂ l]
  refine key.trans ?_
  have hr := r4ModelConst_sum_nonneg κ
  have hq := potTestConst_le_potWordConst N hl
  have hX : 0 ≤ max 1 (max CGam₁ CGam₂) * max CPi₂ 1 :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_right _ _))
  have hw := potWordConst_nonneg N L
  have hq0 := (potTestConst_pos N l).le
  have hm : r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1 ≤
      max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
        (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1) := le_max_right _ _
  unfold forcingGc
  calc d * (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1 *
        (max 1 (max CGam₁ CGam₂) * max CPi₂ 1) * potTestConst N l)
      ≤ d * (max (r4ModelConst (phi43RegularityStructureF κ) κ.1)
        (r4ModelConst (TwoModel.structSumU (phi43PolynomialSectorF κ)) κ.1) *
        (max 1 (max CGam₁ CGam₂) * max CPi₂ 1) * potWordConst N L) := by gcongr
    _ = _ := by ring

end RegularityStructures.Phi43.LocalLipschitz

end

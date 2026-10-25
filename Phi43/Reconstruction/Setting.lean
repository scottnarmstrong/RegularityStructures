/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.WindowNear
public import Phi43.Reconstruction.Cube
public import Phi43.Restart.Compat
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlockWNear
public import RegularityStructures.Abstract.FixedPointPhi4Near
import Mathlib.Tactic.Linarith
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma

/-!
# The setting of the identification at a restart

`Phi43NearHyp` collects the per-model hypotheses of `phi43FixedPointF_window_nearOne` (model bounds
of the enlarged model on the window and on the slab, qualitative growth, joint measurability,
realising the kernel on the `Ξ`-free block).  From them:

* `Phi43NearHyp.val_cube`: the cube of an element of the slab space is the truncated cube;
* `Phi43NearHyp.layerSetting`: the `Ξ`-free block of the cube satisfies `LayerSettingWNear` at
  level `κ = γ + α + α` (window `Γ`-bounds with near pairs, radius `4`).
-/

public section

namespace RegularityStructures.Phi43

variable {κ : Kappa}

/-- The per-model hypotheses of `phi43FixedPointF_window_nearOne`. -/
structure Phi43NearHyp (κ : Kappa) (N : ℕ) (M : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (CPi CGam CΓ CGam₁ CΓ₁ T : ℝ) : Prop where
  pi : M.PiBoundOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CPi hairerTimeWindow
  gam : M.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CGam₁ 1 hairerTimeWindow
  chain : gammaChainConst (Fintype.card SymbolF) CGam₁ 16 ≤ CGam
  growth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
    M.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q
  cPi : 0 ≤ CPi
  joint : M.IsJointMeasurable
  real : M.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
    (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF)
  gamBase : M.GammaBoundNearOn (gamma κ) CΓ₁ 1 (timeSlab T)
  gamShift : M.GammaBoundNearOn (gamma κ + phi43Alpha κ) CΓ₁ 1 (timeSlab T)
  gK : M.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ + 2) CΓ₁ 1 (timeSlab T)
  chainΓ : gammaChainConst (Fintype.card SymbolF) CΓ₁ 16 ≤ CΓ
  cΓ : 0 ≤ CΓ
  hT0 : 0 < T
  hT1 : T ≤ 1

variable {N : ℕ} {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

theorem Phi43NearHyp.gamNear (h : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) :
    M.GammaNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CGam hairerTimeWindow :=
  ((h.gam.toGammaNearOn M segmentClosed_hairerTimeWindow)).mono M h.chain

theorem Phi43NearHyp.gamBaseNear (h : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) :
    M.GammaNearOn (gamma κ) CΓ (timeSlab T) :=
  ((h.gamBase.toGammaNearOn M (segmentClosed_timeSlab T))).mono M h.chainΓ

theorem Phi43NearHyp.gamShiftNear (h : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) :
    M.GammaNearOn (gamma κ + phi43Alpha κ) CΓ (timeSlab T) :=
  ((h.gamShift.toGammaNearOn M (segmentClosed_timeSlab T))).mono M h.chainΓ

theorem phi43_hAG (κ : Kappa) (M : Model (phi43RegularityStructureF κ) parabolicSemigroup) :
    ∀ x y τ, M.gammaMap x y (blockProj phi43XiFreeF τ) = blockProj phi43XiFreeF (M.gammaMap x y τ) :=
  Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M

/-- The cube of an element of the slab space is the truncated cube. -/
theorem Phi43NearHyp.val_cube (h : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) {η : ℝ}
    (hκη : κ.1 < -1 / 2 - η)
    (U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)) :
    (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U).val =
      (phi43ProductF κ).truncCube (gamma κ + phi43Alpha κ + phi43Alpha κ) U.val := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  exact Model.SlabSpace.val_cube_near (phi43ProductF κ) (α := phi43Alpha κ) (γ₀ := gamma κ)
    (η₀ := η) (η' := 2 * η) (η'' := 3 * η) (CΓ := CΓ) (phi43SectorV_isSector κ)
    (phi43SectorW_isSector κ) (phi43SectorV_ofRegularity κ) (phi43SectorW_ofRegularity κ)
    (phi43ProductF_mul_mem κ) (phi43ProductF_isRegularPair_VV κ) (phi43ProductF_isRegularPair_VW κ)
    (by simp only [phi43Alpha]; linarith) (by linarith) (by simp only [gamma, phi43Alpha]; linarith)
    (by simp only [phi43Alpha]; linarith) (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith) U h.gamBaseNear h.gamShiftNear h.cΓ

/-- The `Ξ`-free block of the cube satisfies the near window layer setting at level `κ`. -/
theorem Phi43NearHyp.layerSetting (h : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) {η : ℝ}
    (hη₁ : -2 / 3 < η)
    (g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) (timeSlab T)) :
    LayerSettingWNear M (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) g).val
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) (phi43Zeta κ)
      ‖Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) g‖ CPi CGam T := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  exact Model.layerSettingW_blockProj_near phi43XiFreeF (phi43_hAG κ M) g
    (by simp only [gamma, phi43Alpha]; linarith) h.pi h.cPi h.gamNear h.growth h.hT1
    (fun j _ => phi43DegreeF_gt_neg_four κ j) (fun i hi => phi43DegreeF_xiFree_ge κ hi)
    (by simp only [gamma, phi43Alpha, phi43Zeta]; linarith)
    (lt_min_iff.2 ⟨by simp only [phi43Zeta]; linarith, by linarith⟩)

end RegularityStructures.Phi43

end

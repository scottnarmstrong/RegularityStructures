/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Compat
public import Phi43.Structure.CanonicalModelExistence
public import Phi43.Potential.NoiseModelHyp
public import Phi43.Potential.NoiseBounds
public import Phi43.Potential.NoiseBridge
public import Phi43.Potential.ZetaBound
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import Phi43.Potential.Convolution
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The forcing hypotheses at a restart, from the enlarged model

At a restart time `s`, the noise coordinate of an enlarged model `M'` compatible with the
translate by `(s, 0)` of the renormalised canonical model is `Q_t` of the time-shifted noise.
Hence the window bounds of `M'` at level `κ` (those of `Restart.restart_quantitative`) give the
hypotheses `Potential.NoiseModelHyp` of the potential and forcing bounds for `M'` itself, with
the old noise symbol `Ξ` (`noiseModelHyp_enlarged`).  No periodicity of the old model is used.
-/

public section

open Set

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential RegularityStructures.Phi43.Potential
  RegularityStructures.Phi43.LiftBounds

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {Cg : ℝ} {q : ℕ}
  {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
  {C : RenormalisationConstants} {M' : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {s : ℝ}

/-- The noise symbol has degree `< κ`. -/
theorem phi43DegreeF_old_noise_lt (κ : Kappa) : phi43DegreeF κ (.old .noise) < κ.1 := by
  have h0 := κ.2.1
  change homogeneity κ .noise < κ.1
  simp only [homogeneity]
  linarith

/-- The noise coordinate of a compatible enlarged model is `Q_t` of the shifted noise. -/
theorem regPi_old_noise_eq_apply
    (hC : Restart.EnlargedCompat κ
      ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)) M')
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    M'.regPi x (Pi.single (SymbolF.old .noise) 1) t y =
      parabolicSemigroup.apply t (potShift s noise.zeta) y := by
  rw [hC.regPi_single]
  exact regPi_translate_noise_eq_apply
    (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C) s x ht y

/-- **The potential hypotheses for the enlarged model at a restart**, level `κ`. -/
theorem noiseModelHyp_enlarged
    (hC : Restart.EnlargedCompat κ
      ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)) M')
    {f : SpaceTime → ℝ} (hfz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    (hgf : Statements.HasPhi43NoiseGrowth f)
    (hgr : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q' : ℝ),
      M'.GrowthModel κ.1 C' C'' ρP ρG p q')
    {CPi CG : ℝ} (hPi : M'.PiBoundOn κ.1 CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M'.GammaBoundNearOn κ.1 CG 1 hairerTimeWindow) :
    NoiseModelHyp M' κ.1 CPi (gammaChainConst (Fintype.card SymbolF) CG 16) (.old .noise)
      (potShift s noise.zeta) where
  pi := hPi
  cpi := hCPi
  gam := Model.GammaBoundNearOn.toGammaNearOn _ segmentClosed_hairerTimeWindow hGam
  deg j _ := phi43DegreeF_gt_neg_four κ j
  ho := phi43DegreeF_old_noise_lt κ
  cont := noise.smooth.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  poly := by
    obtain ⟨-, B, n, hB⟩ := polyBounded_zeta hfz hgf
    exact ⟨_, n, fun u => abs_potShift_le hB s u⟩
  reg x t ht y := regPi_old_noise_eq_apply hC x ht y
  growth z _ _ := Model.hasQualitativeGrowthAt_of_exists M' hgr z
  bdd := by
    obtain ⟨B, hB⟩ := exists_bound_strip (perSmooth_noise_zeta noise) (s - 1) (s + 2)
    exact ⟨B, fun y h1 h2 => hB (y.1 + s, y.2) (by simp; linarith) (by simp; linarith)⟩

end RegularityStructures.Phi43.LocalLipschitz

end

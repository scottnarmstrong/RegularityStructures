/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Persistence.PotentialOffset
public import Phi43.Restart.Package
public import Phi43.Structure.RenormalisedEnlargedModel
public import Phi43.Inhomogeneity.DuhamelBounds
public import Phi43.Potential.NoiseBounds
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# The forcing interface and the potential bound of the restart, from the size of the lift

For a lift `Z` of the renormalised canonical model of `noise` with `phi43Size κ η T Z ψ ≤ B`, and a
restart time `s ∈ [0, T]`, the model hypotheses of the potential estimates hold for the *canonical*
model `M₀ = canonicalRenormalisedModel N κ noise Cg q hg C` (same noise and constants) translated
by `(s, 0)`, at the level `κ` (the window `Π`-bound at level `κ` involves only pinned symbols; the
noise coordinate has degree `-5/2 - κ < κ`):

* `persist_derivHyp`: the restarted forcing `ζ_s = Q ∗ ζ(· + (s, 0))` satisfies
  `DerivHyp ζ_s (persistGc L * persistBg B) L` for all `L`;
* `persist_conv_bound`: `‖(K_N ∗ ζ)(s')‖_η ≤ persistC8 B` for `s ≤ s' ≤ s + 1`, `s' ≤ T + 1`.

The constants depend only on `(κ, N, B)`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43.Persistence

open RegularityStructures RegularityStructures.Potential RegularityStructures.Phi43.Potential
  RegularityStructures.Phi43.LiftBounds RegularityStructures.Inhomogeneity

/-- `B_g(B) = max(1, C_Γ') B` with `C_Γ' = gammaChainConst (card Symbol) B 16`: the model constant
of the forcing bound. -/
@[expose] noncomputable def persistBg (B : ℝ) : ℝ :=
  max 1 (gammaChainConst (Fintype.card Symbol) B 16) * B

/-- The derivative constants `G_c(L)` of the restarted forcing. -/
@[expose] noncomputable def persistGc (N : ℕ) (κ : Kappa) (L : ℕ) : ℝ :=
  potGc N (phi43RegularityStructure κ) κ.1 L

/-- The `𝒞^η` bound of the singular part `(K_N ∗ ζ)(s')` of the solution. -/
@[expose] noncomputable def persistC8 (N : ℕ) (κ : Kappa) (B : ℝ) : ℝ :=
  r4ModelConst (phi43RegularityStructure κ) κ.1 * persistBg B *
    (potKernelConst (potTail N) + potK1Const N (homogeneity κ Symbol.noise)) + 2 * B

theorem persistBg_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ persistBg B :=
  mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB

theorem persistGc_nonneg (N : ℕ) (κ : Kappa) (L : ℕ) : 0 ≤ persistGc N κ L :=
  potGc_nonneg N (fun j _ => neg_four_lt_homogeneity κ j) L

theorem persistC8_nonneg (N : ℕ) (κ : Kappa) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ persistC8 N κ B := by
  unfold persistC8
  have h1 := r4ModelConst_nonneg (phi43RegularityStructure κ)
    (γ := κ.1) (fun j _ => neg_four_lt_homogeneity κ j)
  have h2 : 0 ≤ potKernelConst (potTail N) :=
    (potKernelConst_pos (isUnitKernel_potTail N)).le
  have h3 := potK1Const_nonneg N (homogeneity κ Symbol.noise)
  have h4 := persistBg_nonneg hB
  positivity

/-- The noise model hypothesis of the restart, at an arbitrary level `γ` above the degree of the
noise. -/
theorem noiseModelHyp_restart_level {N : ℕ} {κ : Kappa} {noise : CanonicalNoise}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (hpoly : PolyBounded noise.zeta)
    (s : ℝ) {γ CPi CG CGam : ℝ} (hγ : homogeneity κ Symbol.noise < γ)
    (hPi : (Z.translate (restartPoint s)).PiBoundOn γ CPi hairerTimeWindow)
    (hCPi : 0 ≤ CPi)
    (hGam : (Z.translate (restartPoint s)).GammaBoundNearOn γ CG 1 hairerTimeWindow)
    (hCG : gammaChainConst (Fintype.card Symbol) CG 16 ≤ CGam)
    (hgrowth : ∀ z : ParabolicSpace, s ≤ z.1 → z.1 ≤ s + 1 → Z.HasQualitativeGrowthAt γ z) :
    NoiseModelHyp (Z.translate (restartPoint s)) γ CPi CGam Symbol.noise
      (potShift s noise.zeta) where
  pi := hPi
  cpi := hCPi
  gam := (Model.GammaBoundNearOn.toGammaNearOn _ segmentClosed_hairerTimeWindow hGam).mono _ hCG
  deg j _ := neg_four_lt_homogeneity κ j
  ho := hγ
  cont := noise.smooth.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  poly := by
    obtain ⟨-, B, n, hB⟩ := hpoly
    exact ⟨_, n, fun u => abs_potShift_le hB s u⟩
  reg x t ht y := regPi_translate_noise_eq_apply hZ s x ht y
  growth z h0 h1 := hasQualitativeGrowthAt_translate (hgrowth _ (by simp [restartPoint]; linarith)
    (by simp [restartPoint]; linarith))
  bdd := by
    obtain ⟨B, hB⟩ := exists_bound_strip (perSmooth_noise_zeta noise) (s - 1) (s + 2)
    exact ⟨B, fun y h1 h2 => hB (y.1 + s, y.2) (by simp; linarith) (by simp; linarith)⟩

/-- The forcing bound at an arbitrary level `γ` above the degree of the noise. -/
theorem derivHyp_zeta_restart_level {N : ℕ} {κ : Kappa} {noise : CanonicalNoise}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (hpoly : PolyBounded noise.zeta)
    (s : ℝ) {γ CPi CGam : ℝ} (hγ : homogeneity κ Symbol.noise < γ)
    (hPi : (Z.translate (restartPoint s)).PiBoundOn γ CPi hairerTimeWindow)
    (hCPi : 0 ≤ CPi)
    (hGam : (Z.translate (restartPoint s)).GammaBoundNearOn γ CGam 1 hairerTimeWindow)
    (hgrowth : ∀ z : ParabolicSpace, s ≤ z.1 → z.1 ≤ s + 1 → Z.HasQualitativeGrowthAt γ z)
    (L : ℕ) :
    DerivHyp (potZeta noise.zeta N s)
      (potGc N (phi43RegularityStructure κ) γ L *
        (max 1 (gammaChainConst (Fintype.card Symbol) CGam 16) * CPi)) L := by
  obtain ⟨_, B, n, hB⟩ := hpoly
  have hξ : Continuous (potShift s noise.zeta) :=
    noise.smooth.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have hB' : ∀ u, |potShift s noise.zeta u| ≤
      (B * (1 + parabolicNorm (restartPoint s)) ^ n) * (1 + parabolicNorm u) ^ n :=
    fun u => abs_potShift_le hB s u
  have hgS : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 →
      (Z.translate (restartPoint s)).HasQualitativeGrowthAt γ z := by
    intro z hz0 hz1
    refine hasQualitativeGrowthAt_translate (hgrowth _ ?_ ?_)
    · simp [restartPoint]; linarith
    · simp [restartPoint]; linarith
  exact derivHyp_potConv_near (Z.translate (restartPoint s)) hPi hCPi
    (Model.GammaBoundNearOn.toGammaNearOn _ segmentClosed_hairerTimeWindow hGam)
    (fun j _ => neg_four_lt_homogeneity κ j) (o := Symbol.noise) hγ hξ
    hB' (fun x t ht y => regPi_translate_noise_eq_apply hZ s x ht y) hgS N L

theorem homogeneity_noise_lt_kappa (κ : Kappa) : homogeneity κ Symbol.noise < κ.1 := by
  have hk : 0 < κ.1 := κ.2.1
  simp only [homogeneity]
  linarith

/-- The canonical model has qualitative growth at the level `κ` at every base point. -/
theorem canonical_hasQualitativeGrowthAt_level (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (z : ParabolicSpace) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).HasQualitativeGrowthAt κ.1 z := by
  obtain ⟨C', C'', r, t, ρP, ρG, G⟩ := phi43RenormalisedSourceSector_growth N κ noise Cg q hg C
  obtain ⟨c, β, p, h⟩ := G.hasQualitativeGrowthAt z
  have hk : 0 < κ.1 := κ.2.1
  refine ⟨c, β, p, fun i hi t ht y => h i (lt_trans hi ?_) t ht y⟩
  simp only [gamma]
  linarith

section Restart

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} (Cg : ℝ) (q : ℕ)
  (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
  {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup} {η T B s : ℝ}
  {ψ : ℝ → C(Torus3, ℝ)}

include hg

/-- The window bounds of the restarted canonical model at the level `κ`, with the bound `B` on the
size `phi43Size` as constant. -/
theorem persist_window (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hB : 0 ≤ B) (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) :
    ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)).PiBoundOn
        κ.1 B hairerTimeWindow ∧
      ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)).GammaBoundNearOn
        κ.1 B 1 hairerTimeWindow := by
  have hk : 0 < κ.1 := κ.2.1
  refine ⟨Restart.restart_canonical_piBoundOn_window hZ hB hs h, ?_⟩
  exact Model.GammaBoundNearOn.mono_degree
    (Restart.restart_canonical_gammaBoundNearOn_window hZ hB hs h) (by simp only [gamma]; linarith)

/-- **The forcing interface.**  The restarted forcing `ζ_s` satisfies the derivative
hypothesis of `phi43InhomTheta` with the constants `persistGc L * persistBg B`. -/
theorem persist_derivHyp (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hpoly : PolyBounded noise.zeta) (hB : 0 ≤ B) (hs : s ∈ Icc (0 : ℝ) T)
    (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) (L : ℕ) :
    DerivHyp (potZeta noise.zeta N s) (persistGc N κ L * persistBg B) L := by
  obtain ⟨hPi, hGam⟩ := persist_window Cg q hg hZ hB hs h
  exact derivHyp_zeta_restart_level
    (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C) hpoly s
    (homogeneity_noise_lt_kappa κ) hPi hB hGam
    (fun z _ _ => canonical_hasQualitativeGrowthAt_level N κ noise Cg q hg C z) L

/-- **The potential bound at a time offset.**  For `s ≤ s' ≤ s + 1`, `s' ≤ T + 1`, the singular part
`(K_N ∗ ζ)(s')` of the solution has `𝒞^η` norm at most `persistC8 N κ B`. -/
theorem persist_conv_bound (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    {f : SpaceTime → ℝ} (hfz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    (hgr : Statements.HasPhi43NoiseGrowth f) (hψ : RegularityStructures.IsMassivePotential f ψ) (hB : 0 ≤ B)
    (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) (hη : η ≤ 0)
    {s' : ℝ} (hs0 : s ≤ s') (hs1 : s' ≤ s + 1) (hsT : s' ≤ T + 1) (V : C(Torus3, ℝ))
    (hV : ∀ xt : Fin 3 → ℝ, V (torusProj xt) = hairerConvolution N noise.zeta (s', xt)) :
    holderBesovENorm η V ≤ ENNReal.ofReal (persistC8 N κ B) := by
  obtain ⟨hPi, hGam⟩ := persist_window Cg q hg hZ hB hs h
  have hZ₀ := canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C
  have hN := phi43NoiseSize_le_of_phi43Size_le h
  have hψN : ∀ r ∈ Icc (s' - 1 / 4) s', holderBesovENorm η (ψ r) ≤ ENNReal.ofReal B := by
    intro r hr
    refine le_trans ?_ hN
    unfold Statements.phi43NoiseSize
    exact le_iSup₂ (f := fun t (_ : t ∈ Icc (-1 : ℝ) (T + 1)) => holderBesovENorm η (ψ t)) r
      ⟨by linarith [hr.1, hs.1], by linarith [hr.2]⟩
  have H := noiseModelHyp_restart_level hZ₀ (polyBounded_zeta hfz hgr) s
    (homogeneity_noise_lt_kappa κ) hPi hB hGam le_rfl
    (fun z _ _ => canonical_hasQualitativeGrowthAt_level N κ noise Cg q hg C z)
  have := holderBesovENorm_conv_le_offset H hs0 hs1 N (potForcing_of_growth hfz hgr) hfz
    noise.smooth.continuous hψ η hη hB hψN V hV
  refine this.trans (le_of_eq ?_)
  unfold persistC8 persistBg
  rfl

end Restart

end RegularityStructures.Phi43.Persistence

end

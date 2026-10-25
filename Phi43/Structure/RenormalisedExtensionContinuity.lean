/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionData
public import Phi43.Structure.CanonicalSmoothCharacters

/-!
# Continuity of the corrected smooth character

The integrated-cubic character is corrected by the actual potential K*Psi.
Its continuity is derived from the causal convolution, not assumed as part
of arbitrary model data [Hai14, (8.34), Theorem 8.44].
-/

public noncomputable section

namespace RegularityStructures.Phi43

theorem continuous_renormalisedExtensionStructureGroup_coeff (N : ℕ) {κ : Kappa}
    (noise : CanonicalNoise) (c : RenormalisationConstants) (τ σ : Symbol) :
    Continuous (fun z => structureGroupMap
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter c z)
        (basis τ) σ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hcoord (i : Fin 4) : Continuous (fun z : ParabolicSpace => parabolicCoords z i) := by
    fin_cases i
    · exact continuous_fst
    · change Continuous (fun z : ParabolicSpace => z.2 0)
      fun_prop
    · change Continuous (fun z : ParabolicSpace => z.2 1)
      fun_prop
    · change Continuous (fun z : ParabolicSpace => z.2 2)
      fun_prop
  have hps : ContDiff ℝ (↑(⊤ : ℕ∞)) (CanonicalData.localPsi D) := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hx (i : Fin 4) : Continuous (fun z => (D.canonicalCharacter z).shift i) :=
    (hcoord i).neg
  have hg (i : Fin 3) : Continuous (fun z => (D.canonicalCharacter z).cPsiGrad i) :=
    (continuous_hairerSpatialGradient N hps i).neg
  have hp : Continuous (fun z => (D.canonicalCharacter z).cPsi) := by
    change Continuous (fun z => -hairerConvolution N (CanonicalData.localPsi D) z +
      ∑ i, (D.canonicalCharacter z).shift i.succ * (D.canonicalCharacter z).cPsiGrad i)
    exact (contDiff_hairerConvolution N hps).continuous.neg.add
      (continuous_finsetSum _ fun i _ => (hx i.succ).mul (hg i))
  have hs : Continuous (fun z => (D.canonicalCharacter z).cPsiSq) :=
    (contDiff_hairerConvolution N (hps.mul hps)).continuous.neg
  have hc : Continuous (fun z => (D.canonicalCharacter z).cPsiCube) :=
    (contDiff_hairerConvolution N ((hps.mul hps).mul hps)).continuous.neg
  have hi : Continuous D.globalIPsi :=
    (canonicalGlobalPiBasis_smooth N noise .iPsi).continuous
  exact continuous_structureGroupMap_basis (D.renormalisedExtensionCharacter c)
    hx hp hg hs (hc.add (continuous_const.mul hi)) τ σ

end RegularityStructures.Phi43

end

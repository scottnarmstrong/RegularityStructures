/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LocalizedUniformAllowances
public import GlobalPhi43.Local.AbsorbedAugmentedSchauder
public import GlobalPhi43.Local.AugmentedExpansionAverage
public import GlobalPhi43.Local.RadiusNormAgreement

/-! The actual corrected Schauder collection from original augmented
local data, using landed LOCAL P-plus positive inputs. The allowance
is for the original u-J at its original natural radius. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 theorem exists_augmented_local_schauder_bound {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 14) :
    ∃ c₀ > 0, c₀ ≤ 1 ∧ ∃ Aout > 0,
    ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
      (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
      IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ →
    ∀ (r c E₁ E₂ E₃ : ℝ), 0 ≤ r → r < 1 / 2 → 0 ≤ c → c ≤ c₀ →
      0 < sourceSup (fun z => u z - J z) r →
      0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ →
      DefectSmall c (sourceSup (fun z => u z - J z) r) E₁ E₂ E₃ →
      (∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₁ z| ≤ E₁) →
      (∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₂ z| ≤ E₂) →
      (∀ z ∈ parabolicClosedNbhd mwCylinder 1, |e₃ z| ≤ E₃) →
    ∀
    (_hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (1 - 2 * ε)))
    (_hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (1 + (1 / 2 - 3 * ε))))
    (_hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (1 / 2 - ε)))
    (_hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (2 - 4 * ε)))
    (_hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y (fun z => J z ^ 2 - C₁) C₂ ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (2 - 4 * ε)))
    (_hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) (fun z => J z ^ 2 - C₁) ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (1 - 2 * ε)))
    (_hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε (fun z => J z ^ 2 - C₁) ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (1 - 2 * ε)))
    (_hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z (fun z => J z ^ 2 - C₁) J C₂ ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (5 / 2 - 5 * ε))),
    weightedRadiusAffineSeminorm (sourceExpansion (fun z => u z - J z) Y Z) r
      ((sourceSup (fun z => u z - J z) r)⁻¹) ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (Aout * sourceSup (fun z => u z - J z) r) := by
  let γ := (3 / 2 : ℝ) - 5 * ε
  have hγ : 1 < γ := by dsimp [γ]; linarith
  have hγ₂ : γ < 2 := by dsimp [γ]; linarith
  obtain ⟨C, hC, hinput⟩ := exists_local_positive_uniform_allowances hε hsmall
  obtain ⟨c₀, hc₀, hc₀1, Aout, hAout, happly⟩ := exists_absorbed_augmented_schauder_application
    (sourceSchauderExponents ε) id (sourceSchauderExponents ε) id
    ⟨1 / 2 - 3 * ε, sourceSchauderExponents_three_point ε⟩ hγ hγ₂
    (fun a ha => (sourceSchauderExponents_admissible hsmall a ha).2)
    (fun a ha => (sourceSchauderExponents_admissible hsmall a ha).1)
    (fun a ha => (sourceSchauderExponents_admissible hsmall a ha).2) C hC.le
  refine ⟨c₀, hc₀, hc₀1, Aout, hAout, ?_⟩
  intro Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hdata r c E₁ E₂ E₃ hr hr1 hc hcc hM
    hE₁ hE₂ hE₃ hsmallDefect he₁ he₂ he₃ hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD
  obtain ⟨v, W, hv, hW, hKW, heq, herror⟩ :=
    localData_augmented_expansion_average hdata hE₂ he₁ he₂ he₃
  let M := sourceSup (fun z => u z - J z) r
  have hmass : sourceSup v r = M := sourceSup_remainder_representative hKW heq hr
  have hMv : 0 < sourceSup v r := by rwa [hmass]
  have hscale : M⁻¹ * sourceSup v r ≤ 1 := by rw [hmass, inv_mul_cancel₀ hM.ne']
  have hJ := hdata.2.2.1
  have hY := hdata.2.2.2.1
  have hZ := hdata.2.2.2.2.1
  have hV : ContDiff ℝ ∞ (fun z => J z ^ 2 - C₁) := (hJ.pow 2).sub contDiff_const
  obtain ⟨P₁, P₃, hP₁, hP₃, hbase, hthree, hprice⟩ :=
    hinput Φ hΦ v J Y Z (fun z => J z ^ 2 - C₁) C₂ hv hJ hY hZ hV
      r M⁻¹ c hr hr1 hc (hcc.trans hc₀1) hMv hscale
      (by simpa only [hmass] using hbudgetY) (by simpa only [hmass] using hbudgetZ)
      (by simpa only [hmass] using hbudgetJ) (by simpa only [hmass] using hbudgetB)
      (by simpa only [hmass] using hbudgetA) (by simpa only [hmass] using hbudgetV)
      (by simpa only [hmass] using hbudgetX) (by simpa only [hmass] using hbudgetD)
  have hsource : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧
        ContDiffOn ℝ ∞ (sourceExpansion v Y Z) O :=
    ⟨univ, isOpen_univ, subset_univ _, (sourceExpansion_contDiff v Y Z hv hY hZ).contDiffOn⟩
  have hn := happly Φ hΦ (sourceExpansion v Y Z)
    (fun T hT => sourceFormalForcingAverage Φ hΦ v J (fun z => J z ^ 2 - C₁) C₂ T hT)
    r M c P₁ P₃ E₁ E₂ E₃ hr hM hc hcc hP₁ hP₃ hE₁ hE₂ hE₃ hsmallDefect
    hsource (fun x _ => expansion_diag v Y Z x) hthree ?_ hbase ?_
  · rw [weightedRadiusAffineSeminorm_remainder_representative hr hKW heq] at hn
    exact hn
  · intro d hd x hx L hL hLd T hT hTL y hy
    have hd1 : d < 1 := by nlinarith [hd.1, hx.1, hx.2.1, sq_nonneg r]
    have hT1 : T ≤ 1 := by linarith
    have hLT : L + T ≤ d := by linarith
    have he := herror Φ hΦ r d L T hT hr hL.le hT1 hLT x hx y hy
    simpa only [sourceExpansion, sourceFormalForcingAverage_eq_integral] using! he
  · simpa only [hmass] using hprice

end GlobalPhi43.Local

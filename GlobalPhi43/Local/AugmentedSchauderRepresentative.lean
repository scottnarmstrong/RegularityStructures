/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedLocalSchauder

/-! One original-data representative carries the exact augmented PDE,
unchanged parent mass and the actual absorbed radius allowance together. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff ENNReal

 theorem exists_augmented_schauder_representative {ε : ℝ}
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
    ∃ (v : ParabolicSpace → ℝ) (W : Set ParabolicSpace),
      ContDiff ℝ ∞ v ∧ IsOpen W ∧ closure mwCylinder ⊆ W ∧
      EqOn v (fun z => u z - J z) W ∧
      sourceSup v r = sourceSup (fun z => u z - J z) r ∧
      (∀ z ∈ sourceCylinder 0,
        sourceHeat v z = -v z ^ 3 - 3 * v z ^ 2 * J z -
          3 * v z * (J z ^ 2 - C₁) - (J z ^ 3 - 3 * C₁ * J z) -
          9 * C₂ * (v z + J z) - e₁ z ∧
        sourceHeat Y z = (J z ^ 2 - C₁) + e₂ z ∧
        sourceHeat Z z = (J z ^ 3 - 3 * C₁ * J z) + e₃ z) ∧
      weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r ((sourceSup v r)⁻¹)
        ((3 / 2 : ℝ) - 5 * ε) ≤ ENNReal.ofReal (Aout * sourceSup v r) := by
  obtain ⟨c₀, hc₀, hc₀1, Aout, hAout, hbound⟩ := exists_augmented_local_schauder_bound hε hsmall
  refine ⟨c₀, hc₀, hc₀1, Aout, hAout, ?_⟩
  intro Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hdata r c E₁ E₂ E₃ hr hr1 hc hcc hM
    hE₁ hE₂ hE₃ hsmallDefect he₁ he₂ he₃ hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD
  have hn := hbound Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hdata r c E₁ E₂ E₃ hr hr1 hc hcc hM
    hE₁ hE₂ hE₃ hsmallDefect he₁ he₂ he₃ hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD
  obtain ⟨v, W, hv, hW, hKW, heq, hpde⟩ := localData_augmented_sourceHeat hdata
  have hmass := sourceSup_remainder_representative hKW heq hr
  refine ⟨v, W, hv, hW, hKW, heq, hmass, ?_, ?_⟩
  · intro z hz
    apply hpde z
    rwa [mwCylinder_eq_sourceCylinder]
  · rw [hmass, weightedRadiusAffineSeminorm_remainder_representative hr hKW heq]
    exact hn

end GlobalPhi43.Local

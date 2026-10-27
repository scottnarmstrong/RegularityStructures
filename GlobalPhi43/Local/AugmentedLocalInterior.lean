/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedSchauderRepresentative
public import GlobalPhi43.MW20.AugmentedClosingRadiusRow

/-! Interior estimates from the original data: the actual absorbed Schauder allowance
feeds the independently proved augmented local-positive closing row. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff ENNReal

 theorem exists_augmented_local_interior {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 14) :
    ∃ c₀ > 0, c₀ ≤ 1 ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
      (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
      IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ →
    ∀ (r R c E₁ E₂ E₃ : ℝ), 0 ≤ r → r < 1 / 2 → 0 ≤ c → c ≤ c₀ →
      0 < sourceSup (fun z => u z - J z) r →
      r + 1 / sourceSup (fun z => u z - J z) r < R → R ≤ 1 / 2 →
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
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (5 / 2 - 5 * ε)))
    (_hbudgetW : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(3 / 2) - 3 * ε) (fun z => J z ^ 3 - 3 * C₁ * J z) ≤
      ENNReal.ofReal (c * sourceSup (fun z => u z - J z) r ^ (3 / 2 - 3 * ε))),
    sourceSup (fun z => u z - J z) R ≤
      max (C / (R - (r + 1 / sourceSup (fun z => u z - J z) r)))
        (sourceSup (fun z => u z - J z) r / 2) := by
  obtain ⟨cSch, hcSch, _, Aout, hAout, hSch⟩ := exists_augmented_schauder_representative hε hsmall
  obtain ⟨k, hk, c₀, hc₀, hcPrior, hc₀1, hclose⟩ :=
    exists_source_augmented_closing_row_from_radius_bound hε hsmall hAout.le hcSch
  let Cclose := (92 / 62 : ℝ) * sourceLargeScaleConstant ε Aout
  refine ⟨c₀, hc₀, hc₀1, max 1 Cclose, le_max_left _ _, ?_⟩
  intro Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hdata r R c E₁ E₂ E₃ hr hr1 hc hcc hM hGap hR1
    hE₁ hE₂ hE₃ hsmallDefect he₁ he₂ he₃ hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD hbudgetW
  obtain ⟨v, W, hv, hW, hKW, heq, hmass, hpde, hnorm⟩ :=
    hSch Φ hΦ u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hdata r c E₁ E₂ E₃ hr hr1 hc (hcc.trans hcPrior) hM
      hE₁ hE₂ hE₃ hsmallDefect he₁ he₂ he₃ hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD
  have hJ := hdata.2.2.1
  have hY := hdata.2.2.2.1
  have hZ := hdata.2.2.2.2.1
  have hV : ContDiff ℝ ∞ (fun z => J z ^ 2 - C₁) := (hJ.pow 2).sub contDiff_const
  have hWtree : ContDiff ℝ ∞ (fun z => J z ^ 3 - 3 * C₁ * J z) :=
    (hJ.pow 3).sub (contDiff_const.mul hJ)
  have hPDE : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) -
        3 * (v z * (J z ^ 2 - C₁)) - (J z ^ 3 - 3 * C₁ * J z) -
        9 * C₂ * (v z + J z) - e₁ z := by
    intro z hz
    simpa only [mul_assoc] using (hpde z hz).1
  have hEbound : ∀ z ∈ sourceCylinder 0, |e₁ z| ≤ E₁ := by
    intro z hz
    have hzP : z ∈ mwCylinder := by rwa [mwCylinder_eq_sourceCylinder]
    exact he₁ z ⟨z, hzP, by simp [parabolicDist]⟩
  have hn := hclose Φ hΦ v J Y Z (fun z => J z ^ 2 - C₁)
    (fun z => J z ^ 3 - 3 * C₁ * J z) e₁ C₂ hv hJ hY hZ hV hWtree hdata.2.2.2.2.2.1 hPDE
    r R c E₁ E₂ E₃ hr hE₁ hE₃ hEbound (by simpa only [hmass] using hsmallDefect)
    hc (by simpa only [hmass] using hM) (by simpa only [hmass] using hGap) hR1
    (by simpa only [one_div] using hnorm)
    (by simpa only [hmass] using hbudgetY) (by simpa only [hmass] using hbudgetZ) hcc
    (by simpa only [hmass] using hbudgetA) (by simpa only [hmass] using hbudgetV)
    (by simpa only [hmass] using hbudgetX) (by simpa only [hmass] using hbudgetD)
    (by simpa only [hmass] using hbudgetJ) (by simpa only [hmass] using hbudgetB)
    (by simpa only [hmass] using hbudgetW)
  have hInv : 0 < 1 / sourceSup (fun z => u z - J z) r := by positivity
  have hRpos : 0 ≤ R := by linarith
  rw [sourceSup_remainder_representative hKW heq hRpos, hmass] at hn
  apply hn.trans
  apply max_le_max _ le_rfl
  exact div_le_div_of_nonneg_right (le_max_right 1 Cclose) (by linarith)

end GlobalPhi43.Local

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedMomentDefs
public import Phi43.BPHZ.ShiftedGammaParamsSub
import Mathlib.Tactic

/-!
# The `Γ`-entry bounds for models with shifted constants

`shiftedBphzInputs_gamma` is the `gamma` field of `ShiftedBphzInputs`: for
`‖c‖, ‖c'‖ ≤ B`, the random `Γ`-entries of `canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)`
have the moment bound `C₀ d^(deg i - deg j + κ̄)`, and the differences of two such models have the
moment bound `C₀ ((ε ∨ ε')^θ + ‖c - c'‖) d^(deg i - deg j + κ̄)`.

The `Γ`-parameter of the model depends on the constants only through the `cPsiCube` component,
which changes by `3 s (T₀(x) - T₀(y))` with `s = c.1` (`gammaFullParam_cPsiCube_shift`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem sg_abs_fst_le (c : RenormalisationConstants) : |c.1| ≤ ‖c‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_fst_le c

private theorem sg_C₁_shiftConst (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (c : RenormalisationConstants) : C₁ (shiftConst N ρ ε c) = hairerWickConstant N ρ ε + c.1 :=
  rfl

/-- **The `gamma` field of `ShiftedBphzInputs`.** -/
theorem shiftedBphzInputs_gamma.{u} (N : ℕ) (κ : Kappa) :
    ∀ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}, IsMollifier ρ → IsMollifier ρ' → ∀ {κbar θ : ℝ},
    0 ≤ κbar → κbar ≤ κ.1 / 2 → 0 < θ → θ < κ.1 - κbar → ∀ {q : ℕ}, 1 ≤ q → ∀ {B : ℝ}, 0 ≤ B →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ GammaShiftBounds.{u} N ρ ρ' κ κbar θ q B C₀ := by
  intro ρ ρ' hρ hρ' κbar θ h0 h1 hθ hθκ q hq B hB
  obtain ⟨Cs, hCs, hs⟩ := gammaFull_entryShift_lintegral_le.{u} N hρ h0 h1 hq hB (κ := κ)
  obtain ⟨Cs', hCs', hs'⟩ := gammaFull_entryShift_lintegral_le.{u} N hρ' h0 h1 hq hB (κ := κ)
  obtain ⟨Cd, hCd, hd⟩ := gammaFull_entryShift_sub_lintegral_le.{u} N hρ hρ' h0 h1 hθ hθκ hq hB
    (κ := κ)
  refine ⟨max Cs (max Cs' Cd), le_max_of_le_left hCs, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr'
  have hcB : |c.1| ≤ B := (sg_abs_fst_le c).trans hc
  have hcB' : |c'.1| ≤ B := (sg_abs_fst_le c').trans hc'
  have hCs_le : Cs ≤ max Cs (max Cs' Cd) := le_max_left _ _
  have hCs'_le : Cs' ≤ max Cs (max Cs' Cd) := (le_max_left _ _).trans (le_max_right _ _)
  have hCd_le : Cd ≤ max Cs (max Cs' Cd) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hi hj x y
    have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
    have hr := eq_random_of_not_mem_gammaFullDeterministic κ hi hij
    simp only [canonicalModelOfLift_gammaMap_single_apply (hξ.1 _) (hgr _)]
    refine le_ofReal_pow_mono (hs hcB hW hε hξ (sg_C₁_shiftConst N ρ ε c) hgr i j hr hne x y) ?_
    exact mul_le_mul_of_nonneg_right hCs_le
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _)
  · intro i j hij hi hj x y
    have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
    have hr := eq_random_of_not_mem_gammaFullDeterministic κ hi hij
    simp only [canonicalModelOfLift_gammaMap_single_apply (hξ'.1 _) (hgr' _)]
    refine le_ofReal_pow_mono (hs' hcB' hW hε' hξ' (sg_C₁_shiftConst N ρ' ε' c') hgr' i j hr hne
      x y) ?_
    exact mul_le_mul_of_nonneg_right hCs'_le
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _)
  · intro i j hij hi hj x y
    have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
    have hr := eq_random_of_not_mem_gammaFullDeterministic κ hi hij
    simp only [canonicalModelOfLift_gammaMap_single_apply (hξ.1 _) (hgr _),
      canonicalModelOfLift_gammaMap_single_apply (hξ'.1 _) (hgr' _)]
    refine le_ofReal_pow_mono (hd hcB hcB' hW hε hε' hξ hξ' (sg_C₁_shiftConst N ρ ε c)
      (sg_C₁_shiftConst N ρ' ε' c') hgr hgr' i j hr hne x y) ?_
    have hM : (max ε ε') ^ θ + |c.1 - c'.1| ≤ (max ε ε') ^ θ + ‖c - c'‖ := by
      have := sg_abs_fst_le (c - c')
      simp only [Prod.fst_sub] at this
      linarith
    have hM0 : 0 ≤ (max ε ε') ^ θ + |c.1 - c'.1| :=
      add_nonneg (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul hCd_le hM hM0 ((hCd.trans hCd_le)))
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _)

end RegularityStructures.Phi43

end

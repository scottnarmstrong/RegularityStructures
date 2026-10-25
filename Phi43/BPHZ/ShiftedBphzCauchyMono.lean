/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedMomentDefs
public import Phi43.BPHZ.GammaFullKolmogorovInputs
public import Phi43.BPHZ.ShiftedPiSingleAll
public import Phi43.BPHZ.ShiftedPiSubAll
import Mathlib.Tactic

/-!
# Shifted BPHZ models: monotonicity in the constant and the deterministic `Γ`-entries

* `PiShiftSingleBound.mono`, `PiShiftSubBound.mono`, `GammaShiftBounds.mono`: the shifted
  moment bounds are monotone in the constant `C`.
* `gammaDeterministic_hypotheses`: the two deterministic `Γ`-hypotheses of the Kolmogorov bound
  (single, difference)
  for canonical models with ARBITRARY renormalisation constants (they do not depend on them).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ} {i : Symbol}
  {B C C' : ℝ}

theorem GammaShiftBounds.mono (h : GammaShiftBounds.{u} N ρ ρ' κ κbar θ q B C) (hC : C ≤ C') :
    GammaShiftBounds.{u} N ρ ρ' κ κbar θ q B C' := by
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hgr hgr'
  obtain ⟨h1, h2, h3⟩ := h c c' hc hc' hW hε hε' hξ hξ' hgr hgr'
  have hd : ∀ y x : ParabolicSpace, ∀ r : ℝ,
      0 ≤ parabolicSemigroup.scaleDist y x ^ r := fun y x r =>
    Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _
  have h0 : 0 ≤ (max ε ε') ^ θ + ‖c - c'‖ :=
    add_nonneg (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _) (norm_nonneg _)
  refine ⟨fun i j hp hi hj x y => ?_, fun i j hp hi hj x y => ?_, fun i j hp hi hj x y => ?_⟩
  · exact le_ofReal_pow_mono (h1 i j hp hi hj x y)
      (mul_le_mul_of_nonneg_right hC (hd y x _))
  · exact le_ofReal_pow_mono (h2 i j hp hi hj x y)
      (mul_le_mul_of_nonneg_right hC (hd y x _))
  · exact le_ofReal_pow_mono (h3 i j hp hi hj x y)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC h0) (hd y x _))

/-- The deterministic `Γ`-hypotheses of the Kolmogorov bound for canonical models with arbitrary
constants. -/
theorem gammaDeterministic_hypotheses {Ω : Type u} {ξ ξ' : Ω → SpaceTime → ℝ}
    {C₁' C₂' : RenormalisationConstants} (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (hξ' : ∀ ω, IsSmoothOnSpaceTime (ξ' ω)) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) {C E : ℝ} (hC : 1 ≤ C) (hE : 0 ≤ E) :
    (∀ Z ∈ ({fun ω => canonicalModelOfLift N κ C₁' (ξ ω),
          fun ω => canonicalModelOfLift N κ C₂' (ξ' ω)} :
          Set (Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)),
      ∀ i j, (i, j) ∈ gammaFullDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
        (phi43RegularityStructure κ).deg j < (phi43RegularityStructure κ).deg i → ∀ ω,
        ∀ x y : ParabolicSpace,
        |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
          C * parabolicSemigroup.scaleDist y x ^
            ((phi43RegularityStructure κ).deg i - (phi43RegularityStructure κ).deg j)) ∧
    (∀ i j, (i, j) ∈ gammaFullDeterministic → (phi43RegularityStructure κ).deg i < gamma κ →
        (phi43RegularityStructure κ).deg j < (phi43RegularityStructure κ).deg i → ∀ ω,
        ∀ x y : ParabolicSpace,
        |(canonicalModelOfLift N κ C₁' (ξ ω)).gammaMap y x (Pi.single i 1) j -
            (canonicalModelOfLift N κ C₂' (ξ' ω)).gammaMap y x (Pi.single i 1) j| ≤
          C * E * parabolicSemigroup.scaleDist y x ^
            ((phi43RegularityStructure κ).deg i - (phi43RegularityStructure κ).deg j)) := by
  constructor
  · rintro Z (rfl | rfl) i j hp hi hj ω x y
    · have h := abs_gammaMap_entry_le_of_mem_gammaFullDeterministic (N := N) (C := C₁')
        (hξ ω) (hgr ω) hp hj y x
      exact h.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg
        (parabolicSemigroup.scaleDist_nonneg y x) _))
    · have h := abs_gammaMap_entry_le_of_mem_gammaFullDeterministic (N := N) (C := C₂')
        (hξ' ω) (hgr' ω) hp hj y x
      exact h.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg
        (parabolicSemigroup.scaleDist_nonneg y x) _))
  · intro i j hp hi hj ω x y
    rw [gammaMap_entry_eq_of_mem_gammaFullDeterministic (N := N) (C := C₁') (C' := C₂')
      (hξ ω) (hgr ω) (hξ' ω) (hgr' ω) hp hj y x, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) hE)
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _)

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubShiftedB
import Mathlib.Tactic

/-!
# Moments of the terms with random gradient coefficients

The terms `gₖ Mₖ` (deterministic moment `Mₖ`) and `gₖ R_σ` (row `R_σ`) and their differences, used
by the shifted rows containing `I(Ψ³)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

/-- `gₖ Mₖ`: the gradient times the first moment of the kernel. -/
theorem ShiftedPiAtoms.momGradMoment (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (x : ParabolicSpace) (k : Fin 3) {e : ℝ} (he : e ≤ 1 / 4) :
    ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
      (Cg * parabolicSemigroup.momentConst 1 * t ^ e) := by
  have h0 := ShiftMom.mul_const (P := P) (shiftedPiMoment t x k) (A.grad1 hW hε hξ x k)
    (abs_shiftedPiMoment_le ht.1 x k) A.nonneg.2.2.2
  have h1 : ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
      (Cg * parabolicSemigroup.momentConst 1 * t ^ (1 / 4 : ℝ)) :=
    h0.mono (le_of_eq (by ring))
  have := parabolicSemigroup.momentConst_nonneg 1
  have := A.nonneg.2.2.2
  exact h1.tpow (by positivity) ht he

/-- `gₖ R_σ` through Hölder. -/
theorem ShiftedPiAtoms.momGradReg (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) {σ : Symbol}
    (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) (hlt : homogeneity κ σ < gamma κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (k : Fin 3) {e : ℝ}
    (he : e ≤ (homogeneity κ σ + κbar) / 4) :
    ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ) (Cg * C2 * t ^ e) := by
  have hp := (A.mom2 h1 hx hlt hW hε hξ hgr ht x).tpow A.nonneg.2.1 ht he
  have h0 := ShiftMom.mul (measurable_shiftedPiGrad hξ x k)
    (measurable_shiftedPiReg hξ hgr _ x ht.1 _) (A.grad hW hε hξ x k) hp A.nonneg.2.2.2
  exact h0.mono (le_of_eq (by ring))

/-- The difference `(gₖ - gₖ') Mₖ`. -/
theorem ShiftedPiSubAtoms.momGradMomentSub
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (k : Fin 3) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) {e : ℝ} (he : e ≤ 1 / 4) :
    ShiftMom P q (fun ω => (shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k) *
      shiftedPiMoment t x k) (Sg * parabolicSemigroup.momentConst 1 * D * t ^ e) := by
  have h0 := ShiftMom.mul_const (P := P) (shiftedPiMoment t x k)
    (SA.momGrad hW hε hε' hξ hξ' x k D hD) (abs_shiftedPiMoment_le ht.1 x k)
    (mul_nonneg SA.nonneg.2.2.2 ((Real.rpow_nonneg (le_max_of_le_left hε.1.le) _).trans hD))
  have h1 : ShiftMom P q (fun ω => (shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k) *
      shiftedPiMoment t x k)
      (Sg * parabolicSemigroup.momentConst 1 * D * t ^ (1 / 4 : ℝ)) :=
    h0.mono (le_of_eq (by ring))
  have hD0 : 0 ≤ D := (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _).trans hD
  have := parabolicSemigroup.momentConst_nonneg 1
  have := SA.nonneg.2.2.2
  exact h1.tpow (by positivity) ht he

/-- The difference `gₖ R_σ - gₖ' R_σ'`. -/
theorem ShiftedPiSubAtoms.momGradRegSub
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    {σ : Symbol}
    (h1 : σ ≠ .one) (hx : ∀ j, σ ≠ .x j) (hlt : homogeneity κ σ < gamma κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (k : Fin 3) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) {e : ℝ} (he : e ≤ (homogeneity κ σ + κbar) / 4) :
    ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k *
        shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t σ -
      shiftedPiGrad N ξ' ω x k *
        shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t σ)
      ((Sg * C2 + Cg * S2) * D * t ^ e) := by
  have hD0 : 0 ≤ D := (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _).trans hD
  have ht0 : 0 < t := ht.1
  have hS2 := SA.nonneg.2.1
  have hSg := SA.nonneg.2.2.2
  have hC2 := SA.left.nonneg.2.1
  have hCg := SA.left.nonneg.2.2.2
  have hp := (SA.left.mom2 h1 hx hlt hW hε hξ hgr ht x).tpow hC2 ht he
  have hq' := (SA.momSub2 h1 hx hlt hW hε hε' hξ hξ' hgr hgr' ht x D hD).tpow
    (mul_nonneg hS2 hD0) ht he
  have hg' := SA.right.grad hW hε' hξ' x k
  have h0 := ShiftMom.mulDiff hq (measurable_shiftedPiGrad hξ x k)
    (measurable_shiftedPiGrad hξ' x k) (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _)
    (SA.momGrad2 hW hε hε' hξ hξ' x k D hD) hp hg' hq' (mul_nonneg hSg hD0)
    hCg (by positivity) (by positivity)
  exact h0.mono (le_of_eq (by ring))

end RegularityStructures.Phi43

end

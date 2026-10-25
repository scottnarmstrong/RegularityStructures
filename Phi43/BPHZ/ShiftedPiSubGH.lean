/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiSubTrees
import Mathlib.Tactic

/-!
# The sums `∑ₖ gₖ R_{Ψ²Xₖ}` and `R_{I(Ψ)} + ∑ₖ gₖ Mₖ`

These two random variables carry the random coefficients of the shifted row of `I(Ψ³)Ψ²`; their
`L^q` bounds and those of their differences are proved separately to keep each declaration small.
-/

@[expose] public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `∑ₖ gₖ R_{Ψ²Xₖ}`. -/
noncomputable def shiftedPiGsum (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) {Ω : Type*}
    (ξ : Ω → SpaceTime → ℝ) (x : ParabolicSpace) (t : ℝ) (ω : Ω) : ℝ :=
  shiftedPiGrad N ξ ω x 0 * shiftedPiReg N κ C (ξ ω) x t (.psiSqX 0) +
    shiftedPiGrad N ξ ω x 1 * shiftedPiReg N κ C (ξ ω) x t (.psiSqX 1) +
    shiftedPiGrad N ξ ω x 2 * shiftedPiReg N κ C (ξ ω) x t (.psiSqX 2)

/-- `R_{I(Ψ)} + ∑ₖ gₖ Mₖ`. -/
noncomputable def shiftedPiHsum (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) {Ω : Type*}
    (ξ : Ω → SpaceTime → ℝ) (x : ParabolicSpace) (t : ℝ) (ω : Ω) : ℝ :=
  shiftedPiReg N κ C (ξ ω) x t .iPsi + (shiftedPiGrad N ξ ω x 0 * shiftedPiMoment t x 0 +
    shiftedPiGrad N ξ ω x 1 * shiftedPiMoment t x 1 +
    shiftedPiGrad N ξ ω x 2 * shiftedPiMoment t x 2)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {κ : Kappa} {κbar θ : ℝ} {q : ℕ}
  {C1 C2 Ci Cg S1 S2 Si Sg : ℝ}

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} {C : RenormalisationConstants}

theorem measurable_shiftedPiGsum (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) :
    Measurable (shiftedPiGsum N κ C ξ x t) := by
  have m : ∀ k, Measurable fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ C (ξ ω) x t (.psiSqX k) := fun k =>
    (measurable_shiftedPiGrad hξ x k).mul (measurable_shiftedPiReg hξ hgr _ x ht _)
  exact ((m 0).add (m 1)).add (m 2)

theorem measurable_shiftedPiHsum (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) :
    Measurable (shiftedPiHsum N κ C ξ x t) := by
  have m : ∀ k, Measurable fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k := fun k =>
    (measurable_shiftedPiGrad hξ x k).mul_const _
  exact (measurable_shiftedPiReg hξ hgr _ x ht _).add (((m 0).add (m 1)).add (m 2))

end Measurability

theorem ShiftedPiAtoms.momGsum (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) {e : ℝ}
    (he : e ≤ (homogeneity κ (.psiSqX 0) + κbar) / 4) :
    ShiftMom P q (shiftedPiGsum N κ (shiftedPiHairerConst N ρ ε) ξ x t)
      (3 * (Cg * C2) * t ^ e) := by
  have ht0 : 0 < t := ht.1
  have hC2 := A.nonneg.2.1
  have hCg := A.nonneg.2.2.2
  have m : ∀ k, Measurable fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiSqX k) := fun k =>
    (measurable_shiftedPiGrad hξ x k).mul (measurable_shiftedPiReg hξ hgr _ x ht.1 _)
  have g : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiSqX k))
      (Cg * C2 * t ^ e) := fun k =>
    A.momGradReg (σ := .psiSqX k) (by simp) (by simp)
      (by simp only [homogeneity, gamma]; linarith [κ.2.1]) hW hε hξ hgr ht x k
      (by simpa only [homogeneity] using he)
  have s := ((g 0).add hq (m 0) (m 1) (g 1) (by positivity) (by positivity)).add hq
    ((m 0).add (m 1)) (m 2) (g 2) (by positivity) (by positivity)
  exact s.mono (le_of_eq (by ring))

theorem ShiftedPiAtoms.momHsum (A : ShiftedPiAtoms.{u} N ρ κ κbar q C1 C2 Ci Cg) (hq : 1 ≤ q)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) {e : ℝ}
    (he1 : e ≤ (homogeneity κ .iPsi + κbar) / 4) (he2 : e ≤ 1 / 4) :
    ShiftMom P q (shiftedPiHsum N κ (shiftedPiHairerConst N ρ ε) ξ x t)
      ((Ci + 3 * (Cg * parabolicSemigroup.momentConst 1)) * t ^ e) := by
  have ht0 : 0 < t := ht.1
  have hCi := A.nonneg.2.2.1
  have hCg := A.nonneg.2.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have m : ∀ k, Measurable fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k := fun k =>
    (measurable_shiftedPiGrad hξ x k).mul_const _
  have g : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k)
      (Cg * parabolicSemigroup.momentConst 1 * t ^ e) := fun k =>
    A.momGradMoment hW hε hξ ht x k he2
  have s := ((g 0).add hq (m 0) (m 1) (g 1) (by positivity) (by positivity)).add hq
    ((m 0).add (m 1)) (m 2) (g 2) (by positivity) (by positivity)
  have a := (A.momIPsi hW hε hξ hgr ht x).tpow hCi ht he1
  have := a.add hq (measurable_shiftedPiReg hξ hgr _ x ht.1 _) (((m 0).add (m 1)).add (m 2)) s
    (by positivity) (by positivity)
  exact this.mono (le_of_eq (by ring))

theorem ShiftedPiSubAtoms.momGsumSub
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) {e : ℝ} (he : e ≤ (homogeneity κ (.psiSqX 0) + κbar) / 4) :
    ShiftMom P q (fun ω => shiftedPiGsum N κ (shiftedPiHairerConst N ρ ε) ξ x t ω -
      shiftedPiGsum N κ (shiftedPiHairerConst N ρ' ε') ξ' x t ω)
      (3 * (Sg * C2 + Cg * S2) * D * t ^ e) := by
  have ht0 : 0 < t := ht.1
  have hD0 : 0 ≤ D := (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _).trans hD
  have hS2 := SA.nonneg.2.1
  have hSg := SA.nonneg.2.2.2
  have hC2 := SA.left.nonneg.2.1
  have hCg := SA.left.nonneg.2.2.2
  have m : ∀ k, Measurable fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiSqX k) -
      shiftedPiGrad N ξ' ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t (.psiSqX k) := fun k =>
    ((measurable_shiftedPiGrad hξ x k).mul (measurable_shiftedPiReg hξ hgr _ x ht.1 _)).sub
      ((measurable_shiftedPiGrad hξ' x k).mul (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _))
  have g : ∀ k : Fin 3, ShiftMom P q (fun ω => shiftedPiGrad N ξ ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ ε) (ξ ω) x t (.psiSqX k) -
      shiftedPiGrad N ξ' ω x k *
      shiftedPiReg N κ (shiftedPiHairerConst N ρ' ε') (ξ' ω) x t (.psiSqX k))
      ((Sg * C2 + Cg * S2) * D * t ^ e) := fun k =>
    SA.momGradRegSub hq (σ := .psiSqX k) (by simp) (by simp)
      (by simp only [homogeneity, gamma]; linarith [κ.2.1]) hW hε hε' hξ hξ' hgr hgr' ht x k D hD
      (by simpa only [homogeneity] using he)
  have s := ((g 0).add hq (m 0) (m 1) (g 1) (by positivity) (by positivity)).add hq
    ((m 0).add (m 1)) (m 2) (g 2) (by positivity) (by positivity)
  refine ShiftMom.congr (fun ω => ?_) (s.mono (le_of_eq (by ring)))
  simp only [shiftedPiGsum, Pi.add_apply]
  ring

theorem ShiftedPiSubAtoms.momHsumSub
    (SA : ShiftedPiSubAtoms.{u} N ρ ρ' κ κbar θ q C1 C2 Ci Cg S1 S2 Si Sg) (hq : 1 ≤ q)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (hgr' : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) (D : ℝ)
    (hD : (max ε ε') ^ θ ≤ D) {e : ℝ} (he1 : e ≤ (homogeneity κ .iPsi + κbar) / 4)
    (he2 : e ≤ 1 / 4) :
    ShiftMom P q (fun ω => shiftedPiHsum N κ (shiftedPiHairerConst N ρ ε) ξ x t ω -
      shiftedPiHsum N κ (shiftedPiHairerConst N ρ' ε') ξ' x t ω)
      ((Si + 3 * (Sg * parabolicSemigroup.momentConst 1)) * D * t ^ e) := by
  have ht0 : 0 < t := ht.1
  have hD0 : 0 ≤ D := (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _).trans hD
  have hSi := SA.nonneg.2.2.1
  have hSg := SA.nonneg.2.2.2
  have hM1 := parabolicSemigroup.momentConst_nonneg 1
  have m : ∀ k, Measurable fun ω => (shiftedPiGrad N ξ ω x k - shiftedPiGrad N ξ' ω x k) *
      shiftedPiMoment t x k := fun k =>
    ((measurable_shiftedPiGrad hξ x k).sub (measurable_shiftedPiGrad hξ' x k)).mul_const _
  have g : ∀ k : Fin 3, ShiftMom P q (fun ω => (shiftedPiGrad N ξ ω x k -
      shiftedPiGrad N ξ' ω x k) * shiftedPiMoment t x k)
      (Sg * parabolicSemigroup.momentConst 1 * D * t ^ e) := fun k =>
    SA.momGradMomentSub hW hε hε' hξ hξ' ht x k D hD he2
  have s := ((g 0).add hq (m 0) (m 1) (g 1) (by positivity) (by positivity)).add hq
    ((m 0).add (m 1)) (m 2) (g 2) (by positivity) (by positivity)
  have b := (SA.momSubIPsi hW hε hε' hξ hξ' hgr hgr' ht x D hD).tpow (mul_nonneg hSi hD0) ht he1
  have := b.add hq ((measurable_shiftedPiReg hξ hgr _ x ht.1 _).sub
    (measurable_shiftedPiReg hξ' hgr' _ x ht.1 _)) (((m 0).add (m 1)).add (m 2)) s
    (by positivity) (by positivity)
  refine ShiftMom.congr (fun ω => ?_) (this.mono (le_of_eq (by ring)))
  simp only [shiftedPiHsum, Pi.sub_apply, Pi.add_apply]
  ring


/-- The shift identity of `I(Ψ³)Ψ²` in terms of `shiftedPiGsum` and `shiftedPiHsum`. -/
theorem shiftedPi_reg_iPsiCubePsiSq_GH {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    {C C' : RenormalisationConstants} {a b : ℝ} {t : ℝ} (x : ParabolicSpace)
    (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω)) (ht : 0 < t)
    (h1 : C₁ C' = C₁ C + a) (h2 : C₂ C' = C₂ C + b) :
    shiftedPiReg N κ C' (ξ ω) x t .iPsiCubePsiSq =
      shiftedPiReg N κ C (ξ ω) x t .iPsiCubePsiSq - a * shiftedPiReg N κ C (ξ ω) x t .iPsiCube -
        3 * a * shiftedPiReg N κ C (ξ ω) x t .iPsiPsiSq -
        3 * a * shiftedPiGsum N κ C ξ x t ω + 3 * a ^ 2 * shiftedPiHsum N κ C ξ x t ω -
        3 * b * shiftedPiReg N κ C (ξ ω) x t .psi := by
  rw [shiftedPi_reg_iPsiCubePsiSq x hf hg ht h1 h2, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [shiftedPiGsum, shiftedPiHsum]

end RegularityStructures.Phi43

end

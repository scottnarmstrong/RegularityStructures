/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentField
public import Phi43.BPHZ.SemigroupTestCoord
import Mathlib.Tactic

/-!
# `Q_t Π_x ΨXᵢ (x)` as a tested field

For a smooth noise `ξ ω` with polynomial growth,
`Q_t Π_x ΨXᵢ (x) = lam ∫_{ℝ × T³} Ψ(u) g_i(u) du`, `lam = t^(1/4)`, `g_i = semigroupPeriodisedCoord t x i`
(`regPi_psiX_eq_tested`), and the integrand is integrable.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Cst : RenormalisationConstants} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ}
  {ω : Ω}

/-- **`Q_t Π_x ΨXᵢ (x)` is `t^(1/4)` times the pairing of `Ψ` with the test profile `g_i`.** -/
theorem regPi_psiX_eq_tested (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω))
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
        (Pi.single (Symbol.psiX i) (1 : ℝ) : Symbol → ℝ) t x =
      t ^ (1 / 4 : ℝ) * ∫ w, hairerPsiField N ξ ω w * semigroupPeriodisedCoord t x i w ∧
    Integrable (fun w => hairerPsiField N ξ ω w * semigroupPeriodisedCoord t x i w) := by
  set lam : ℝ := t ^ (1 / 4 : ℝ) with hlamdef
  have hlam : 0 < lam := Real.rpow_pos_of_pos ht _
  have hΨm : Measurable (hairerPsiField N ξ ω) :=
    (continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hf)).measurable
  have hint0 := integrable_kernel_mul_extensionPi (N := N) (κ := κ) (C := Cst) hf hg
    (Symbol.psiX i) ht x
  rw [extensionPi_psiX_eq hf i x] at hint0
  have hpt : ∀ y : ParabolicSpace, semigroupCoordKernel t x i y *
      hairerPsiField N ξ ω (spaceTimeProj y) =
      (parabolicSemigroup.kernel t x y * (hairerPsiField N ξ ω (spaceTimeProj y) *
        (y.2 i - x.2 i))) / lam := by
    intro y
    unfold semigroupCoordKernel
    rw [← hlamdef]
    field_simp
  have hint1 : Integrable (fun y : ParabolicSpace => semigroupCoordKernel t x i y *
      hairerPsiField N ξ ω (spaceTimeProj y)) :=
    (hint0.div_const lam).congr (Filter.Eventually.of_forall fun y => (hpt y).symm)
  obtain ⟨hI, hper⟩ := integral_mul_comp_proj_periodise (measurable_coordKernel t x i) hΨm hint1
  refine ⟨?_, ?_⟩
  · rw [regPi_canonicalModelOfLift_eq_integral hf hg _ ht x, extensionPi_psiX_eq hf i x]
    have e1 : ∀ y : ParabolicSpace, parabolicSemigroup.kernel t x y *
        (hairerPsiField N ξ ω (spaceTimeProj y) * (y.2 i - x.2 i)) =
        lam * (semigroupCoordKernel t x i y * hairerPsiField N ξ ω (spaceTimeProj y)) := by
      intro y
      rw [hpt y]
      field_simp
    simp only [e1]
    rw [integral_const_mul, hper]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [semigroupPeriodisedCoord]
    ring
  · refine hI.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [semigroupPeriodisedCoord]
    ring

end RegularityStructures.Phi43

end

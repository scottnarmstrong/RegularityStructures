/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiRandom
public import Phi43.BPHZ.ModelRegPiPsi
public import Phi43.BPHZ.SemigroupTestAllMoments
public import Phi43.BPHZ.TreeI2Psi2TestedMoment
public import Phi43.BPHZ.TreeI3Psi2TestedMoment
public import Phi43.BPHZ.TreeI3PsiTestedMoment
public import Phi43.BPHZ.TreeWickCube
public import Phi43.BPHZ.TreeWickSquare

/-!
# Almost sure integrability of `Q_t(x, ·) F(·)` for the tree fields

The hypothesis `hint` of the random corollaries `ae_regPi_single_*_eq` (`ModelRegPiRandom`) holds
for every tree field `F` with square integrable values and a uniform bound on the pointwise second
moments: by Fubini, `E ∫ |Q_t(x, y) F(y)| dy ≤ ‖Q_t(x, ·)‖₁ sup_y E|F(y)| < ∞`
(`kernel_mul_field_integrable_ae_of_sq_bound`).  We verify the hypotheses for `Ξ`, `Ψ²`, `Ψ³`,
`I(Ψ³)Ψ`, `I(Ψ²)Ψ²` and `I(Ψ³)Ψ²` (the case `Ψ` is `hairerPsiField_kernel_integrable_ae`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **Almost sure integrability of the kernel times a field with a uniform second moment bound.** -/
theorem kernel_mul_field_integrable_ae_of_sq_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → SpaceTime → ℝ}
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2)
    (hL2 : ∀ u, MemLp (fun ω => F ω u) 2 P) {V : ℝ} (hV : ∀ u, ∫ ω, F ω u ^ 2 ∂P ≤ V)
    {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * F ω (spaceTimeProj y)) := by
  have hK : Integrable (fun y => parabolicSemigroup.kernel t x y) :=
    integrable_parabolicKernel_sub ht x
  have hYj : AEStronglyMeasurable (Function.uncurry fun (ω : Ω) (y : ParabolicSpace) =>
      F ω (spaceTimeProj y)) (P.prod volume) :=
    (hF.comp (measurable_fst.prodMk
      (continuous_spaceTimeProj.measurable.comp measurable_snd))).aestronglyMeasurable
  have hYi : ∀ y : ParabolicSpace, Integrable (fun ω => F ω (spaceTimeProj y)) P :=
    fun y => (hL2 (spaceTimeProj y)).integrable one_le_two
  have hM : ∀ y : ParabolicSpace, ∫ ω, |F ω (spaceTimeProj y)| ∂P ≤ (V + 1) / 2 := by
    intro y
    have hsq : Integrable (fun ω => F ω (spaceTimeProj y) ^ 2) P :=
      (hL2 (spaceTimeProj y)).integrable_sq
    calc ∫ ω, |F ω (spaceTimeProj y)| ∂P
        ≤ ∫ ω, (F ω (spaceTimeProj y) ^ 2 + 1) / 2 ∂P := by
          refine integral_mono (hYi y).abs ((hsq.add (integrable_const 1)).div_const 2)
            fun ω => ?_
          nlinarith [sq_nonneg (|F ω (spaceTimeProj y)| - 1), sq_abs (F ω (spaceTimeProj y))]
      _ = (∫ ω, F ω (spaceTimeProj y) ^ 2 ∂P + 1) / 2 := by
          rw [integral_div, integral_add hsq (integrable_const 1)]
          simp
      _ ≤ (V + 1) / 2 := by linarith [hV (spaceTimeProj y)]
  exact (integrable_uncurry_mul_of_bound hK hYj hYi hM).prod_right_ae

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- Almost surely `Q_t(x, ·) ξ(proj ·)` is integrable on `ℝ⁴`. -/
theorem regularisedNoise_kernel_integrable_ae (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * ξ ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  exact kernel_mul_field_integrable_ae_of_sq_bound
    (regularisedNoise_measurable_uncurry P W ρ ε ξ hξ)
    (fun u => treePsi_noise_memLp hρ hε hW hξ u)
    (fun u => integral_regularisedNoise_sq_le hρ hε hW hξ u) ht x

/-- Almost surely `Q_t(x, ·) :Ψ²:(proj ·)` is integrable on `ℝ⁴`. -/
theorem hairerPsiWickSquare_kernel_integrable_ae (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * hairerPsiWickSquare N ρ ε ξ ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  exact kernel_mul_field_integrable_ae_of_sq_bound (measurable_hairerPsiWickSquare_uncurry N hξ)
    (fun u => hairerPsiWickSquare_memLp N hρ hε hW hξ u)
    (V := 2 * hairerCovariance N ρ ε 0 ^ 2) (fun u => by
      have h := hairerPsiWickSquare_integral_mul N hρ hε hW hξ u u
      rw [sub_self] at h
      simpa only [sq] using h.le) ht x

/-- Almost surely `Q_t(x, ·) :Ψ³:(proj ·)` is integrable on `ℝ⁴`. -/
theorem hairerPsiWickCube_kernel_integrable_ae (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * hairerPsiWickCube N ρ ε ξ ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  exact kernel_mul_field_integrable_ae_of_sq_bound (measurable_hairerPsiWickCube_uncurry N hξ)
    (fun u => hairerPsiWickCube_memLp N hρ hε hW hξ u)
    (V := 6 * hairerCovariance N ρ ε 0 ^ 3) (fun u => by
      have h := hairerPsiWickCube_integral_mul N hρ hε hW hξ u u
      rw [sub_self] at h
      simpa only [sq] using h.le) ht x

/-- Almost surely `Q_t(x, ·) I₃Ψ_{proj x}(proj ·)` is integrable on `ℝ⁴`. -/
theorem hairerI3PsiField_kernel_integrable_ae (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y *
        hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  exact kernel_mul_field_integrable_ae_of_sq_bound
    (measurable_hairerI3PsiField_uncurry N hξ (spaceTimeProj x))
    (fun u => hairerI3PsiField_memLp N hρ hε hW hξ (spaceTimeProj x) u)
    (V := 42 * hairerWickConstant N ρ ε ^ 4 * ((2 * ∫ w, |hairerKernelTorus N w|) *
          (2 * ∫ w, |hairerKernelTorus N w|))) (fun u => by
      refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        (hairerI3PsiField_pair_integrable_bound N hρ hε hW hξ (spaceTimeProj x) u u).1.abs
        (Filter.Eventually.of_forall fun ω => ?_))
        (hairerI3PsiField_pair_integrable_bound N hρ hε hW hξ (spaceTimeProj x) u u).2
      beta_reduce
      rw [← sq, abs_of_nonneg (sq_nonneg _)]) ht x

/-- Almost surely `Q_t(x, ·) F_{I(Ψ²)Ψ², proj x}(proj ·)` is integrable on `ℝ⁴`. -/
theorem hairerI2Psi2Field_kernel_integrable_ae (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y *
        hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  exact kernel_mul_field_integrable_ae_of_sq_bound
    (measurable_hairerI2Psi2Field_uncurry N hξ (spaceTimeProj x))
    (fun u => hairerI2Psi2Field_memLp N hρ hε hW hξ (spaceTimeProj x) u)
    (fun u => (hairerI2Psi2Field_sq_integrable_bound N hρ hε hW hξ (spaceTimeProj x) u).2) ht x

/-- Almost surely `Q_t(x, ·) F_{I(Ψ³)Ψ², proj x}(proj ·)` is integrable on `ℝ⁴`. -/
theorem hairerI3Psi2Field_kernel_integrable_ae (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t)
    (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y *
        hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω (spaceTimeProj y)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨M, hM⟩ := exists_hairerI3Psi2Field_sq_integral_le N hρ hε hW hξ (spaceTimeProj x)
  exact kernel_mul_field_integrable_ae_of_sq_bound
    (measurable_hairerI3Psi2Field_uncurry N hξ (spaceTimeProj x))
    (fun u => hairerI3Psi2Field_memLp N hρ hε hW hξ (spaceTimeProj x) u)
    (fun u => (hM u).2) ht x

end RegularityStructures.Phi43

end

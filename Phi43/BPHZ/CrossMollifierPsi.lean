/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierDifference

/-!
# Tree `Ψ` with two mollifiers: covariance of the difference

For regularised noises `ξ` (mollifier `ρ`, scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the
same white noise `W`, the difference `Ψ_{ρ,ε} - Ψ_{ρ',ε'}` has covariance
`ΔTwo = hairerKernelDiffCovarianceTwo` (`hairerPsiField_sub_integral_mulTwo`), from the identity
`∫ D(u - w) D(v - w) dw = ΔTwo(u - v)` for the kernel difference `D`
(`integral_hairerKernelDiffTwo_sub_mul`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

private theorem cmp_whiteNoise_memLp (hW : IsWhiteNoise P W) {h : SpaceTime → ℝ}
    (hh : MemLp h 2) : MemLp (W h) 2 P :=
  (hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0

private theorem cmp_integral_expand {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r s : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ) (hr : Integrable r μ)
    (hs : Integrable s μ) :
    ∫ x, ((p x - q x) - (r x - s x)) ∂μ = (∫ x, p x ∂μ - ∫ x, q x ∂μ) -
      (∫ x, r x ∂μ - ∫ x, s x ∂μ) := by
  have h := integral_sub (hp.sub hq) (hr.sub hs)
  simp only [Pi.sub_apply] at h
  rw [h, integral_sub hp hq, integral_sub hr hs]

/-- `∫ D(u - w) D(v - w) dw = ΔTwo(u - v)`. -/
theorem integral_hairerKernelDiffTwo_sub_mul (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε ε' : ℝ)
    (u v : SpaceTime) :
    ∫ w, hairerKernelDiffTwo N ρ ε ρ' ε' (u - w) * hairerKernelDiffTwo N ρ ε ρ' ε' (v - w) =
      hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (u - v) := by
  have h := integral_comp_sub_left_spaceTime
    (fun s => hairerKernelDiffTwo N ρ ε ρ' ε' (u - v + s) * hairerKernelDiffTwo N ρ ε ρ' ε' s) v
  simp only [sub_add_sub_cancel] at h
  rw [hairerKernelDiffCovarianceTwo, h]

/-- **Covariance of the difference of two mollified versions of `Ψ`.** -/
theorem hairerPsiField_sub_integral_mulTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (a b : SpaceTime) :
    ∫ ω, (hairerPsiField N ξ ω a - hairerPsiField N ξ' ω a) *
        (hairerPsiField N ξ ω b - hairerPsiField N ξ' ω b) ∂P =
      hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (a - b) := by
  have m1 := memLp_hairerMollifiedKernel_sub N hρ hε
  have m2 := memLp_hairerMollifiedKernel_sub N hρ' hε'
  set g : SpaceTime → SpaceTime → ℝ := fun z w => hairerMollifiedKernel N ρ ε (z - w) with hg
  set g' : SpaceTime → SpaceTime → ℝ := fun z w => hairerMollifiedKernel N ρ' ε' (z - w) with hg'
  have hWg : ∀ z, MemLp (W (g z)) 2 P := fun z => cmp_whiteNoise_memLp hW (m1 z)
  have hWg' : ∀ z, MemLp (W (g' z)) 2 P := fun z => cmp_whiteNoise_memLp hW (m2 z)
  have i1 : ∀ x y, Integrable (fun ω => W (g x) ω * W (g y) ω) P :=
    fun x y => (hWg x).integrable_mul (hWg y)
  have i2 : ∀ x y, Integrable (fun ω => W (g x) ω * W (g' y) ω) P :=
    fun x y => (hWg x).integrable_mul (hWg' y)
  have i3 : ∀ x y, Integrable (fun ω => W (g' x) ω * W (g' y) ω) P :=
    fun x y => (hWg' x).integrable_mul (hWg' y)
  have j1 : ∀ x y, Integrable (fun w => g x w * g y w) :=
    fun x y => (m1 x).integrable_mul (m1 y)
  have j2 : ∀ x y, Integrable (fun w => g x w * g' y w) :=
    fun x y => (m1 x).integrable_mul (m2 y)
  have j3 : ∀ x y, Integrable (fun w => g' x w * g' y w) :=
    fun x y => (m2 x).integrable_mul (m2 y)
  have e1 : ∀ x y, ∫ ω, W (g x) ω * W (g y) ω ∂P = ∫ w, g x w * g y w :=
    fun x y => whiteNoise_pairing_mul_integral hW (m1 x) (m1 y)
  have e2 : ∀ x y, ∫ ω, W (g x) ω * W (g' y) ω ∂P = ∫ w, g x w * g' y w :=
    fun x y => whiteNoise_pairing_mul_integral hW (m1 x) (m2 y)
  have e3 : ∀ x y, ∫ ω, W (g' x) ω * W (g' y) ω ∂P = ∫ w, g' x w * g' y w :=
    fun x y => whiteNoise_pairing_mul_integral hW (m2 x) (m2 y)
  have hae : ∫ ω, (hairerPsiField N ξ ω a - hairerPsiField N ξ' ω a) *
        (hairerPsiField N ξ ω b - hairerPsiField N ξ' ω b) ∂P =
      ∫ ω, (W (g a) ω - W (g' a) ω) * (W (g b) ω - W (g' b) ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hairerPsiField_ae_eq N hρ hε hW hξ a, hairerPsiField_ae_eq N hρ hε hW hξ b,
      hairerPsiField_ae_eq N hρ' hε' hW hξ' a, hairerPsiField_ae_eq N hρ' hε' hW hξ' b]
      with ω h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  rw [hae]
  have hexp : ∫ ω, (W (g a) ω - W (g' a) ω) * (W (g b) ω - W (g' b) ω) ∂P =
      (∫ ω, W (g a) ω * W (g b) ω ∂P - ∫ ω, W (g a) ω * W (g' b) ω ∂P) -
        (∫ ω, W (g b) ω * W (g' a) ω ∂P - ∫ ω, W (g' a) ω * W (g' b) ω ∂P) := by
    rw [← cmp_integral_expand (i1 a b) (i2 a b) (i2 b a) (i3 a b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    ring
  have hdet : ∫ w, hairerKernelDiffTwo N ρ ε ρ' ε' (a - w) * hairerKernelDiffTwo N ρ ε ρ' ε' (b - w) =
      ((∫ w, g a w * g b w) - ∫ w, g a w * g' b w) -
        ((∫ w, g b w * g' a w) - ∫ w, g' a w * g' b w) := by
    rw [← cmp_integral_expand (j1 a b) (j2 a b) (j2 b a) (j3 a b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hairerKernelDiffTwo, hg, hg']
    ring
  rw [hexp, e1 a b, e2 a b, e2 b a, e3 a b, ← integral_hairerKernelDiffTwo_sub_mul, hdet]

end RegularityStructures.Phi43

end

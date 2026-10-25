/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiLatticeReduce
public import Phi43.BPHZ.ProductIPsiPsiCoreGrowth
public import Phi43.BPHZ.ProductIPsiPsiField
public import Phi43.BPHZ.ModelRegPiAllMoments
public import Phi43.BPHZ.TreeAllMomentsSetup
import Mathlib.Tactic

/-!
# All moments of the tested fields of `I(Ψ)Ψ` and `I(Ψ)(Ψ² - c₁)` from the second moment

For the semigroup test `Q_t(x, ·)` on `ℝ⁴` and every `p ≥ 1`,
`E |∫ Q_t(x, y) F_x(y) dy|^(2p) ≤ A (E |∫ Q_t(x, y) F_x(y) dy|²)^p` with `A = A(p)` independent of
`N`, `ρ`, `ε`, `t`, `x`, `c₁`, the probability space and the noise, for
`F = hairerIPsiPsiField` and `F = hairerIPsiPsiSqField`.

The tested field is rewritten (almost surely, using the almost sure polynomial growth of the noise)
as `∫_{ℝ×T³} ((∫ k(u, w) Ψ(w) dw) Φ(u)) g(u) du` with `g`, `k` of `ProductIPsiPsiLatticeKernel`, and
`integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation` applies with
`P₁ = X`, `P₂ = X` (resp. `X² - c₁`), `P₃ = 0`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Almost surely the field `Q_t(x, ·) F_x` is integrable on `ℝ⁴` (`F = hairerIPsiPsiField`). -/
theorem ae_integrable_semigroup_hairerIPsiPsiField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hρ : IsMollifier ρ) (hW : IsWhiteNoise P W) (hε : 0 < ε)
    (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y := by
  have := hW.isProbabilityMeasure
  filter_upwards [regularisedNoise_ae_hasPhi43NoiseGrowth_of_pos hW hρ hε hξ] with ω hg
  have h := integrable_kernel_mul_extensionPi (N := N) (κ := (⟨1 / 32, by norm_num, by norm_num⟩ : Kappa))
    (C := ((0 : ℝ), (0 : ℝ))) (hξ.1 ω) hg Symbol.iPsiPsi ht x
  rw [extensionPi_iPsiPsi_eq (hξ.1 ω) x] at h
  exact h

/-- Almost surely the field `Q_t(x, ·) F_x` is integrable on `ℝ⁴` (`F = hairerIPsiPsiSqField`). -/
theorem ae_integrable_semigroup_hairerIPsiPsiSqField {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (N : ℕ) (c₁ : ℝ) (hρ : IsMollifier ρ) (hW : IsWhiteNoise P W)
    (hε : 0 < ε) (hξ : IsRegularisedNoise P W ρ ε ξ) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    ∀ᵐ ω ∂P, Integrable fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * hairerIPsiPsiSqField N ξ c₁ x ω y := by
  have := hW.isProbabilityMeasure
  filter_upwards [regularisedNoise_ae_hasPhi43NoiseGrowth_of_pos hW hρ hε hξ] with ω hg
  have h := integrable_kernel_mul_extensionPi (N := N) (κ := (⟨1 / 32, by norm_num, by norm_num⟩ : Kappa))
    (C := (c₁, (0 : ℝ))) (hξ.1 ω) hg Symbol.iPsiPsiSq ht x
  rw [extensionPi_iPsiPsiSq_eq (hξ.1 ω) x] at h
  exact h

/-- **All moments of the tested field of `I(Ψ)Ψ`, semigroup test on `ℝ⁴`.** -/
theorem hairerIPsiPsiField_semigroup_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ x : ParabolicSpace,
        Integrable (fun ω => (∫ y, parabolicSemigroup.kernel t x y *
          hairerIPsiPsiField N ξ x ω y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, parabolicSemigroup.kernel t x y *
            hairerIPsiPsiField N ξ x ω y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {t} ht x => ?_⟩
  obtain ⟨L, hL0, hL⟩ := integral_abs_hairerTaylorKernel_le N
  have key := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    (measurable_latticeG t x) (integrable_latticeG ht x) (measurable_uncurry_latticeK N t x)
    (fun u => (integrable_latticeK_and_integral_abs_le hL0 hL t x u).1)
    (fun u => (integrable_latticeK_and_integral_abs_le hL0 hL t x u).2)
    (fun c R => latticeK_support N t x c R) Polynomial.X Polynomial.X 0
    (by rw [Polynomial.natDegree_X]; omega) (by simp)
  have hae : ∀ᵐ ω ∂P, ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y =
      ∫ v, ((∫ w, latticeK N t x v w * (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω w)) *
        (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω v) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω v)) * latticeG t x v := by
    filter_upwards [ae_integrable_semigroup_hairerIPsiPsiField N hρ hW hε hξ ht x] with ω hi
    have h := integral_semigroup_mul_iPsi_field_eq hL0 hL (hξ.1 ω)
      (Φ := hairerPsiField N ξ ω)
      (continuous_hairerPsiField N hξ.1 ω).measurable ht x hi
    simpa [hairerIPsiPsiField] using h
  refine ⟨?_, ?_⟩
  · refine key.1.congr ?_
    filter_upwards [hae] with ω h
    rw [h]
  · have e1 : ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) ^
        (2 * p) ∂P = ∫ ω, (∫ v, ((∫ w, latticeK N t x v w *
          (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω w)) *
        (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω v) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω v)) * latticeG t x v) ^ (2 * p) ∂P :=
      integral_congr_ae (hae.mono fun ω h => by beta_reduce; rw [h])
    have e2 : ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) ^
        2 ∂P = ∫ ω, (∫ v, ((∫ w, latticeK N t x v w *
          (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω w)) *
        (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω v) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω v)) * latticeG t x v) ^ 2 ∂P :=
      integral_congr_ae (hae.mono fun ω h => by beta_reduce; rw [h])
    rw [e1, e2]
    exact key.2

/-- **All moments of the tested field of `I(Ψ)(Ψ² - c₁)`, semigroup test on `ℝ⁴`.** -/
theorem hairerIPsiPsiSqField_semigroup_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ) (c₁ : ℝ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ x : ParabolicSpace,
        Integrable (fun ω => (∫ y, parabolicSemigroup.kernel t x y *
          hairerIPsiPsiSqField N ξ c₁ x ω y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiSqField N ξ c₁ x ω y) ^
            (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, parabolicSemigroup.kernel t x y *
            hairerIPsiPsiSqField N ξ c₁ x ω y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N c₁ hρ hW hε hξ {t} ht x => ?_⟩
  obtain ⟨L, hL0, hL⟩ := integral_abs_hairerTaylorKernel_le N
  set P₂ : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C c₁ with hP₂
  have hd2 : P₂.natDegree ≤ 2 := by rw [hP₂]; compute_degree
  have key := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    (measurable_latticeG t x) (integrable_latticeG ht x) (measurable_uncurry_latticeK N t x)
    (fun u => (integrable_latticeK_and_integral_abs_le hL0 hL t x u).1)
    (fun u => (integrable_latticeK_and_integral_abs_le hL0 hL t x u).2)
    (fun c R => latticeK_support N t x c R) Polynomial.X P₂ 0
    (by rw [Polynomial.natDegree_X]; omega) (by simp)
  have hae : ∀ᵐ ω ∂P, ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiSqField N ξ c₁ x ω y =
      ∫ v, ((∫ w, latticeK N t x v w * (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω w)) *
        P₂.eval (hairerPsiField N ξ ω v) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω v)) * latticeG t x v := by
    filter_upwards [ae_integrable_semigroup_hairerIPsiPsiSqField N c₁ hρ hW hε hξ ht x] with ω hi
    have hΦ : Measurable (hairerTreePsiSq N ξ c₁ ω) :=
      (((continuous_hairerPsiField N hξ.1 ω).pow 2).sub continuous_const).measurable
    have h := integral_semigroup_mul_iPsi_field_eq hL0 hL (hξ.1 ω)
      (Φ := hairerTreePsiSq N ξ c₁ ω) hΦ ht x hi
    simpa [hairerIPsiPsiSqField, hP₂, hairerTreePsiSq] using h
  refine ⟨?_, ?_⟩
  · refine key.1.congr ?_
    filter_upwards [hae] with ω h
    rw [h]
  · have e1 : ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiSqField N ξ c₁ x ω y) ^
        (2 * p) ∂P = ∫ ω, (∫ v, ((∫ w, latticeK N t x v w *
          (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω w)) *
        P₂.eval (hairerPsiField N ξ ω v) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω v)) * latticeG t x v) ^ (2 * p) ∂P :=
      integral_congr_ae (hae.mono fun ω h => by beta_reduce; rw [h])
    have e2 : ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiSqField N ξ c₁ x ω y) ^
        2 ∂P = ∫ ω, (∫ v, ((∫ w, latticeK N t x v w *
          (Polynomial.X : Polynomial ℝ).eval (hairerPsiField N ξ ω w)) *
        P₂.eval (hairerPsiField N ξ ω v) +
          (0 : Polynomial ℝ).eval (hairerPsiField N ξ ω v)) * latticeG t x v) ^ 2 ∂P :=
      integral_congr_ae (hae.mono fun ω h => by beta_reduce; rw [h])
    rw [e1, e2]
    exact key.2

end RegularityStructures.Phi43

end

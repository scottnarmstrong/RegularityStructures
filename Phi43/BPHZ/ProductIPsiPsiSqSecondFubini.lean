/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondFieldFubini
public import Phi43.BPHZ.ProductIPsiPsiSqCovSix
public import Phi43.BPHZ.TreeWickSquareFour
import Mathlib.Tactic

/-!
# `E[(Q_t Π_x I(Ψ)(Ψ² - c₁) (x))²] = ∫∫ Q_t(x, y) Q_t(x, y') E[F(y) F(y')]`

The Fubini identity for `F = hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε)`, with the
integrability from `E v₁⁴ ≤ (C (1 + r))⁴` and `E (Ψ² - c)⁴ = 60 c⁴`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The weight in the `L¹` bound of `F(y) F(y')`, general constant. -/
def ipsiFourthWeightK (C K : ℝ) (x y y' : ParabolicSpace) : ℝ :=
  ((C * (1 + parabolicNorm (y - x))) ^ 4 + (C * (1 + parabolicNorm (y' - x))) ^ 4) / 4 + K

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem integrable_kernel_mul_ipsiFourthWeightK {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (C K : ℝ) :
    Integrable (fun q : ParabolicSpace × ParabolicSpace =>
      |parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2| *
        ipsiFourthWeightK C K x q.1 q.2) (volume.prod volume) := by
  have hKi : Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y| *
      (C * (1 + parabolicNorm (y - x))) ^ 4) := integrable_kernel_mul_pow_four ht x C
  have hK0 : Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y|) := by
    simpa using parabolicSemigroup.integrable_moment ht (r := 0) le_rfl x
  have e : ∀ q : ParabolicSpace × ParabolicSpace,
      |parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2| *
        ipsiFourthWeightK C K x q.1 q.2 =
      (1 / 4) * ((|parabolicSemigroup.kernel t x q.1| *
          (C * (1 + parabolicNorm (q.1 - x))) ^ 4) * |parabolicSemigroup.kernel t x q.2|) +
      (1 / 4) * (|parabolicSemigroup.kernel t x q.1| * (|parabolicSemigroup.kernel t x q.2| *
          (C * (1 + parabolicNorm (q.2 - x))) ^ 4)) +
      K * (|parabolicSemigroup.kernel t x q.1| * |parabolicSemigroup.kernel t x q.2|) :=
    fun q => by unfold ipsiFourthWeightK; rw [abs_mul]; ring
  simp_rw [e]
  exact ((((hKi.mul_prod hK0).const_mul _).add ((hK0.mul_prod hKi).const_mul _)).add
    ((hK0.mul_prod hK0).const_mul _))

theorem measurable_hairerIPsiPsiSqField_uncurry_cov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (c₁ : ℝ) (x : ParabolicSpace) :
    Measurable (fun q : Ω × ParabolicSpace => hairerIPsiPsiSqField N ξ c₁ x q.1 q.2) := by
  have h1 := measurable_hairerIPsiRecentred_prod_uncurry N hξ x
  have hg : Measurable (fun q : Ω × ParabolicSpace => (q.1, spaceTimeProj q.2)) :=
    measurable_fst.prodMk (continuous_spaceTimeProj.measurable.comp measurable_snd)
  have h2 : Measurable (fun q : Ω × ParabolicSpace =>
      hairerPsiField N ξ q.1 (spaceTimeProj q.2)) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2)
      (f := fun q : Ω × ParabolicSpace => (q.1, spaceTimeProj q.2))
      (measurable_hairerPsiField_uncurry N hξ) hg
  unfold hairerIPsiPsiSqField hairerTreePsiSq
  exact h1.mul ((h2.pow_const 2).sub_const c₁)

theorem measurable_hairerIPsiPsiSqField_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (c₁ : ℝ) (x y : ParabolicSpace) :
    Measurable (fun ω => hairerIPsiPsiSqField N ξ c₁ x ω y) :=
  Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiPsiSqField N ξ c₁ x q.1 q.2)
    (f := fun ω : Ω => (ω, y)) (measurable_hairerIPsiPsiSqField_uncurry_cov N hξ c₁ x)
    (measurable_id.prodMk measurable_const)

/-- **`L¹` bound of `F(y) F(y')`.** -/
theorem hairerIPsiPsiSqField_mul_integrable_bound (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : ParabolicSpace,
        Integrable (fun ω => hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
          hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y') P ∧
        ∫ ω, |hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
          hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y'| ∂P ≤
          ipsiFourthWeightK Ci (30 * hairerCovariance N ρ ε 0 ^ 4) x y y' := by
  obtain ⟨Ci, hCi, hi⟩ := hairerIPsiRecentred_pow_le.{u} N hρ (k := 2) (by norm_num)
  refine ⟨Ci, hCi, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y'
  have := hW.isProbabilityMeasure
  set Q0 := hairerCovariance N ρ ε 0 with hQ0
  have hwc : hairerWickConstant N ρ ε = Q0 := hairerWickConstant_eq_covariance_zero N ρ ε
  have hv4 : ∀ y : ParabolicSpace, Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4) P ∧
      ∫ ω, hairerIPsiRecentred N ξ ω x y ^ 4 ∂P ≤ (Ci * (1 + parabolicNorm (y - x))) ^ 4 :=
    fun y => by simpa using hi hW hε hξ x y
  have hS4i : ∀ z, Integrable (fun ω => hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω z ^ 4) P :=
    fun z => by
      have := integrable_hairerPsiWickSquare_pow_four N hρ hε.1 hW hξ z
      exact this
  have hS4 : ∀ z, ∫ ω, hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω z ^ 4 ∂P =
      60 * Q0 ^ 4 := fun z => by
    have := integral_hairerPsiWickSquare_pow_four N hρ hε.1 hW hξ z
    rw [hwc] at this
    exact this
  have s12 : Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y) ^ 4) P :=
    (hv4 y).1.add (hS4i _)
  have s123 : Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y) ^ 4 +
      hairerIPsiRecentred N ξ ω x y' ^ 4) P := s12.add (hv4 y').1
  have s1234 : Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y) ^ 4 +
      hairerIPsiRecentred N ξ ω x y' ^ 4 +
      hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y') ^ 4) P :=
    s123.add (hS4i _)
  have hdom := s1234.div_const 4
  have hpt : ∀ ω, |hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
      hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y'| ≤
      (hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y) ^ 4 +
      hairerIPsiRecentred N ξ ω x y' ^ 4 +
      hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y') ^ 4) / 4 :=
    fun ω => by
      have := abs_mul_four_le_pow_four (hairerIPsiRecentred N ξ ω x y)
        (hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y))
        (hairerIPsiRecentred N ξ ω x y')
        (hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y'))
      unfold hairerIPsiPsiSqField
      calc _ = |hairerIPsiRecentred N ξ ω x y *
            hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y) *
            hairerIPsiRecentred N ξ ω x y' *
            hairerTreePsiSq N ξ (hairerWickConstant N ρ ε) ω (spaceTimeProj y')| := by
            congr 1; ring
        _ ≤ _ := this
  have hFi : Integrable (fun ω => hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
      hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y') P := by
    refine hdom.mono' ((measurable_hairerIPsiPsiSqField_apply N hξ _ x y).mul
      (measurable_hairerIPsiPsiSqField_apply N hξ _ x y')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hpt ω
  refine ⟨hFi, (integral_mono hFi.abs hdom hpt).trans ?_⟩
  rw [integral_div, integral_add s123 (hS4i _), integral_add s12 (hv4 y').1,
    integral_add (hv4 y).1 (hS4i _), hS4, hS4]
  unfold ipsiFourthWeightK
  have a1 := (hv4 y).2
  have a2 := (hv4 y').2
  linarith

/-- **Fubini identity for the second moment of `Q_t Π_x I(Ψ)(Ψ² - c₁)`.** -/
theorem hairerIPsiPsiSqField_integral_sq_eq (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ}, IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ x : ParabolicSpace,
        ∫ ω, (∫ y, parabolicSemigroup.kernel t x y *
            hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y) ^ 2 ∂P =
          ∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
            parabolicSemigroup.kernel t x q.2 *
            ∫ ω, hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω q.1 *
              hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω q.2 ∂P := by
  obtain ⟨Ci, hCi, hb⟩ := hairerIPsiPsiSqField_mul_integrable_bound.{u} N hρ
  intro Ω _ P W ε ξ hW hε hξ t ht x
  have := hW.isProbabilityMeasure
  exact integral_sq_integral_eq_integral_prod (measurable_parabolicSemigroup_kernel t x)
    (measurable_hairerIPsiPsiSqField_uncurry_cov N hξ _ x) (fun y y' => (hb hW hε hξ x y y').1)
    (fun y y' => (hb hW hε hξ x y y').2)
    (integrable_kernel_mul_ipsiFourthWeightK ht x Ci _)

end RegularityStructures.Phi43

end

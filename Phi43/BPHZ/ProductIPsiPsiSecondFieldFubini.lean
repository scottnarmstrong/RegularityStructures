/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondFubini
public import Phi43.BPHZ.ProductIPsiPsiCovMoment
public import Phi43.BPHZ.ProductIPsiPsiCovFour
public import Phi43.BPHZ.ProductIPsiPsiCovField
public import Phi43.BPHZ.SemigroupTestPeriodise
import Mathlib.Tactic

/-!
# `E[(Q_t Π_x I(Ψ)Ψ (x))²] = ∫∫ Q_t(x, y) Q_t(x, y') E[F(y) F(y')]`

The Fubini identity for the tested field `F = hairerIPsiPsiField`, with the integrability
supplied by the fourth moments `E v₁⁴ ≤ (C (1 + r))⁴`, `E Ψ⁴ = 3 Q(0)²` and the moments of the
semigroup kernel.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem one_add_pow_four_le (r : ℝ) : (1 + r) ^ 4 ≤ 8 * (1 + r ^ 4) := by
  nlinarith [sq_nonneg (r - 1), sq_nonneg (r ^ 2 - 1), sq_nonneg r, sq_nonneg (r ^ 2 - r)]

/-- The semigroup kernel has `|Q_t(x, y)| (c (1 + ‖y - x‖))⁴` integrable. -/
theorem integrable_kernel_mul_pow_four {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) (c : ℝ) :
    Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y| *
      (c * (1 + parabolicNorm (y - x))) ^ 4) := by
  have i0 : Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y|) := by
    simpa using parabolicSemigroup.integrable_moment ht (r := 0) le_rfl x
  have i4 : Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y| *
      parabolicNorm (y - x) ^ 4) := by
    have := parabolicSemigroup.integrable_moment ht (r := 4) (by norm_num) x
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rfl
  have hm : Measurable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y| *
      (c * (1 + parabolicNorm (y - x))) ^ 4) :=
    (continuous_abs.measurable.comp (measurable_parabolicSemigroup_kernel t x)).mul
      ((measurable_const.mul (measurable_const.add (continuous_parabolicNorm.measurable.comp
        (measurable_id.sub measurable_const)))).pow_const 4)
  refine Integrable.mono' ((i0.add i4).const_mul (8 * c ^ 4)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hn := parabolicNorm_nonneg (y - x)
  have := one_add_pow_four_le (parabolicNorm (y - x))
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (by positivity))]
  simp only [Pi.add_apply]
  calc |parabolicSemigroup.kernel t x y| * (c * (1 + parabolicNorm (y - x))) ^ 4
      = c ^ 4 * (|parabolicSemigroup.kernel t x y| * (1 + parabolicNorm (y - x)) ^ 4) := by ring
    _ ≤ c ^ 4 * (|parabolicSemigroup.kernel t x y| * (8 * (1 + parabolicNorm (y - x) ^ 4))) := by
        gcongr
    _ = _ := by ring

/-- The weight in the `L¹` bound of `F(y) F(y')`. -/
noncomputable def ipsiFourthWeight (C Q0 : ℝ) (x y y' : ParabolicSpace) : ℝ :=
  ((C * (1 + parabolicNorm (y - x))) ^ 4 + (C * (1 + parabolicNorm (y' - x))) ^ 4) / 4 +
    3 / 2 * Q0 ^ 2

/-- Joint measurability in `ω` for fixed `y`. -/
theorem measurable_hairerIPsiPsiField_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : ParabolicSpace) :
    Measurable (fun ω => hairerIPsiPsiField N ξ x ω y) :=
  Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiPsiField N ξ x q.1 q.2)
    (f := fun ω : Ω => (ω, y)) (measurable_hairerIPsiPsiField_uncurry_cov N hξ x)
    (measurable_id.prodMk measurable_const)

/-- **`L¹` bound of `F(y) F(y')`.** -/
theorem hairerIPsiPsiField_mul_integrable_bound (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : ParabolicSpace,
        Integrable (fun ω => hairerIPsiPsiField N ξ x ω y * hairerIPsiPsiField N ξ x ω y') P ∧
        ∫ ω, |hairerIPsiPsiField N ξ x ω y * hairerIPsiPsiField N ξ x ω y'| ∂P ≤
          ipsiFourthWeight Ci (hairerCovariance N ρ ε 0) x y y' := by
  obtain ⟨Ci, hCi, hi⟩ := hairerIPsiRecentred_pow_le.{u} N hρ (k := 2) (by norm_num)
  refine ⟨Ci, hCi, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y'
  have := hW.isProbabilityMeasure
  set Q0 := hairerCovariance N ρ ε 0 with hQ0
  have hv4 : ∀ y : ParabolicSpace, Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4) P ∧
      ∫ ω, hairerIPsiRecentred N ξ ω x y ^ 4 ∂P ≤ (Ci * (1 + parabolicNorm (y - x))) ^ 4 :=
    fun y => by simpa using hi hW hε hξ x y
  have hΨ4 : ∀ z : SpaceTime, Integrable (fun ω => hairerPsiField N ξ ω z ^ 4) P := fun z => by
    have := (hairerPsiField_integral_mul_four N hρ hε.1 hW hξ z z z z).1
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hΨ4i : ∀ z : SpaceTime, ∫ ω, hairerPsiField N ξ ω z ^ 4 ∂P = 3 * Q0 ^ 2 := fun z =>
    hairerPsiField_integral_pow_four N hρ hε.1 hW hξ z
  have s12 : Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerPsiField N ξ ω (spaceTimeProj y) ^ 4) P := (hv4 y).1.add (hΨ4 _)
  have s123 : Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerPsiField N ξ ω (spaceTimeProj y) ^ 4 + hairerIPsiRecentred N ξ ω x y' ^ 4) P :=
    s12.add (hv4 y').1
  have s1234 : Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ 4 +
      hairerPsiField N ξ ω (spaceTimeProj y) ^ 4 + hairerIPsiRecentred N ξ ω x y' ^ 4 +
      hairerPsiField N ξ ω (spaceTimeProj y') ^ 4) P := s123.add (hΨ4 _)
  have hdom : Integrable (fun ω =>
      (hairerIPsiRecentred N ξ ω x y ^ 4 + hairerPsiField N ξ ω (spaceTimeProj y) ^ 4 +
        hairerIPsiRecentred N ξ ω x y' ^ 4 + hairerPsiField N ξ ω (spaceTimeProj y') ^ 4) / 4) P :=
    s1234.div_const 4
  have hpt : ∀ ω, |hairerIPsiPsiField N ξ x ω y * hairerIPsiPsiField N ξ x ω y'| ≤
      (hairerIPsiRecentred N ξ ω x y ^ 4 + hairerPsiField N ξ ω (spaceTimeProj y) ^ 4 +
        hairerIPsiRecentred N ξ ω x y' ^ 4 + hairerPsiField N ξ ω (spaceTimeProj y') ^ 4) / 4 :=
    fun ω => by
      have := abs_mul_four_le_pow_four (hairerIPsiRecentred N ξ ω x y)
        (hairerPsiField N ξ ω (spaceTimeProj y)) (hairerIPsiRecentred N ξ ω x y')
        (hairerPsiField N ξ ω (spaceTimeProj y'))
      unfold hairerIPsiPsiField
      calc _ = |hairerIPsiRecentred N ξ ω x y * hairerPsiField N ξ ω (spaceTimeProj y) *
            hairerIPsiRecentred N ξ ω x y' * hairerPsiField N ξ ω (spaceTimeProj y')| := by
            congr 1; ring
        _ ≤ _ := this
  have hFi : Integrable (fun ω => hairerIPsiPsiField N ξ x ω y *
      hairerIPsiPsiField N ξ x ω y') P := by
    refine hdom.mono' ((measurable_hairerIPsiPsiField_apply N hξ x y).mul
      (measurable_hairerIPsiPsiField_apply N hξ x y')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hpt ω
  refine ⟨hFi, (integral_mono hFi.abs hdom hpt).trans ?_⟩
  rw [integral_div, integral_add s123 (hΨ4 _), integral_add s12 (hv4 y').1,
    integral_add (hv4 y).1 (hΨ4 _), hΨ4i, hΨ4i]
  unfold ipsiFourthWeight
  have a1 := (hv4 y).2
  have a2 := (hv4 y').2
  linarith

theorem integrable_kernel_mul_ipsiFourthWeight {t : ℝ} (ht : 0 < t) (x : ParabolicSpace)
    (C Q0 : ℝ) :
    Integrable (fun q : ParabolicSpace × ParabolicSpace =>
      |parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2| *
        ipsiFourthWeight C Q0 x q.1 q.2) (volume.prod volume) := by
  have hKi : Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y| *
      (C * (1 + parabolicNorm (y - x))) ^ 4) := integrable_kernel_mul_pow_four ht x C
  have hK0 : Integrable (fun y : ParabolicSpace => |parabolicSemigroup.kernel t x y|) := by
    simpa using parabolicSemigroup.integrable_moment ht (r := 0) le_rfl x
  have e : ∀ q : ParabolicSpace × ParabolicSpace,
      |parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2| *
        ipsiFourthWeight C Q0 x q.1 q.2 =
      (1 / 4) * ((|parabolicSemigroup.kernel t x q.1| *
          (C * (1 + parabolicNorm (q.1 - x))) ^ 4) * |parabolicSemigroup.kernel t x q.2|) +
      (1 / 4) * (|parabolicSemigroup.kernel t x q.1| * (|parabolicSemigroup.kernel t x q.2| *
          (C * (1 + parabolicNorm (q.2 - x))) ^ 4)) +
      (3 / 2 * Q0 ^ 2) * (|parabolicSemigroup.kernel t x q.1| *
        |parabolicSemigroup.kernel t x q.2|) := fun q => by
    unfold ipsiFourthWeight; rw [abs_mul]; ring
  simp_rw [e]
  exact ((((hKi.mul_prod hK0).const_mul _).add ((hK0.mul_prod hKi).const_mul _)).add
    ((hK0.mul_prod hK0).const_mul _))

/-- **Fubini identity for the second moment of `Q_t Π_x I(Ψ)Ψ`.** -/
theorem hairerIPsiPsiField_integral_sq_eq (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ}, IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → ∀ {t : ℝ}, 0 < t → ∀ x : ParabolicSpace,
        ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) ^ 2 ∂P =
          ∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
            parabolicSemigroup.kernel t x q.2 *
            ∫ ω, hairerIPsiPsiField N ξ x ω q.1 * hairerIPsiPsiField N ξ x ω q.2 ∂P := by
  obtain ⟨Ci, hCi, hb⟩ := hairerIPsiPsiField_mul_integrable_bound.{u} N hρ
  intro Ω _ P W ε ξ hW hε hξ t ht x
  have := hW.isProbabilityMeasure
  exact integral_sq_integral_eq_integral_prod (measurable_parabolicSemigroup_kernel t x)
    (measurable_hairerIPsiPsiField_uncurry_cov N hξ x) (fun y y' => (hb hW hε hξ x y y').1)
    (fun y y' => (hb hW hε hξ x y y').2)
    (integrable_kernel_mul_ipsiFourthWeight ht x Ci _)

end RegularityStructures.Phi43

end

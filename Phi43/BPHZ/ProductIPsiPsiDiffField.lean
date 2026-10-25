/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffFubini
public import Phi43.BPHZ.ProductIPsiPsiDiffFour
public import Phi43.BPHZ.ProductIPsiPsiSecondFieldFubini
public import Phi43.BPHZ.ProductIPsiPsiSqSecondFubini
import Mathlib.Tactic

/-!
# `E[(Q_t Π_x I(Ψ)Ψ - Q_t Π'_x I(Ψ)Ψ)²] = ∬ Q Q' Δe`

For two models `i ∈ Fin 2`, `F_i = hairerIPsiPsiField N (ξ i) x`, `X_i = ∫ Q F_i`,
`e_{ij}(y, y') = E[F_i(y) F_j(y')]`:
`E[(X₀ - X₁)²] = ∬ Q(y) Q(y') (e₀₀ - e₀₁ - e₁₀ + e₁₁)(y, y') dy dy'`
(`ipsiMix_sub_integral_sq_eq`), from the `L¹` bounds of `F_i(y) F_j(y')` by fourth moments.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ}

/-- **`L¹` bound of `F_i(y) F_j(y')`, two models.** -/
theorem ipsiMix_mul_integrable_bound (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → (∀ i, ε i ∈ Set.Ioc (0 : ℝ) 1) →
      (∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) → ∀ (i j : Fin 2) (x y y' : ParabolicSpace),
        Integrable (fun ω => hairerIPsiPsiField N (ξ i) x ω y * hairerIPsiPsiField N (ξ j) x ω y') P ∧
        ∫ ω, |hairerIPsiPsiField N (ξ i) x ω y * hairerIPsiPsiField N (ξ j) x ω y'| ∂P ≤
          ipsiFourthWeightK Cm ((3 * hairerCovariance N (ρ i) (ε i) 0 ^ 2 +
            3 * hairerCovariance N (ρ j) (ε j) 0 ^ 2) / 4) x y y' := by
  obtain ⟨C0, hC0, h0⟩ := hairerIPsiRecentred_pow_le.{u} N (hρ 0) (k := 2) (by norm_num)
  obtain ⟨C1, hC1, h1⟩ := hairerIPsiRecentred_pow_le.{u} N (hρ 1) (k := 2) (by norm_num)
  refine ⟨C0 + C1, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ i j x y y'
  have := hW.isProbabilityMeasure
  have hv4 : ∀ (k : Fin 2) (z : ParabolicSpace),
      Integrable (fun ω => hairerIPsiRecentred N (ξ k) ω x z ^ 4) P ∧
      ∫ ω, hairerIPsiRecentred N (ξ k) ω x z ^ 4 ∂P ≤ ((C0 + C1) * (1 + parabolicNorm (z - x))) ^ 4 := by
    intro k z
    have hn := parabolicNorm_nonneg (z - x)
    fin_cases k
    · obtain ⟨a, b⟩ := h0 hW (hε 0) (hξ 0) x z
      have a' : Integrable (fun ω => hairerIPsiRecentred N (ξ 0) ω x z ^ 4) P := by simpa using a
      have b' : ∫ ω, hairerIPsiRecentred N (ξ 0) ω x z ^ 4 ∂P ≤
          (C0 * (1 + parabolicNorm (z - x))) ^ 4 := by simpa using b
      exact ⟨a', b'.trans (pow_le_pow_left₀ (by positivity) (by nlinarith) 4)⟩
    · obtain ⟨a, b⟩ := h1 hW (hε 1) (hξ 1) x z
      have a' : Integrable (fun ω => hairerIPsiRecentred N (ξ 1) ω x z ^ 4) P := by simpa using a
      have b' : ∫ ω, hairerIPsiRecentred N (ξ 1) ω x z ^ 4 ∂P ≤
          (C1 * (1 + parabolicNorm (z - x))) ^ 4 := by simpa using b
      exact ⟨a', b'.trans (pow_le_pow_left₀ (by positivity) (by nlinarith) 4)⟩
  have hΨ4 : ∀ (k : Fin 2) (z : SpaceTime), Integrable (fun ω => hairerPsiField N (ξ k) ω z ^ 4) P :=
    fun k z => (psiMix_pow_four N hρ (fun k => (hε k).1) hW hξ k z).1
  have hΨ4i : ∀ (k : Fin 2) (z : SpaceTime), ∫ ω, hairerPsiField N (ξ k) ω z ^ 4 ∂P =
      3 * hairerCovariance N (ρ k) (ε k) 0 ^ 2 := fun k z =>
    (psiMix_pow_four N hρ (fun k => (hε k).1) hW hξ k z).2
  have s12 : Integrable (fun ω => hairerIPsiRecentred N (ξ i) ω x y ^ 4 +
      hairerPsiField N (ξ i) ω (spaceTimeProj y) ^ 4) P := (hv4 i y).1.add (hΨ4 i _)
  have s123 : Integrable (fun ω => hairerIPsiRecentred N (ξ i) ω x y ^ 4 +
      hairerPsiField N (ξ i) ω (spaceTimeProj y) ^ 4 +
      hairerIPsiRecentred N (ξ j) ω x y' ^ 4) P := s12.add (hv4 j y').1
  have s1234 : Integrable (fun ω => hairerIPsiRecentred N (ξ i) ω x y ^ 4 +
      hairerPsiField N (ξ i) ω (spaceTimeProj y) ^ 4 +
      hairerIPsiRecentred N (ξ j) ω x y' ^ 4 +
      hairerPsiField N (ξ j) ω (spaceTimeProj y') ^ 4) P := s123.add (hΨ4 j _)
  have hdom := s1234.div_const 4
  have hpt : ∀ ω, |hairerIPsiPsiField N (ξ i) x ω y * hairerIPsiPsiField N (ξ j) x ω y'| ≤
      (hairerIPsiRecentred N (ξ i) ω x y ^ 4 +
      hairerPsiField N (ξ i) ω (spaceTimeProj y) ^ 4 +
      hairerIPsiRecentred N (ξ j) ω x y' ^ 4 +
      hairerPsiField N (ξ j) ω (spaceTimeProj y') ^ 4) / 4 := fun ω => by
    have := abs_mul_four_le_pow_four (hairerIPsiRecentred N (ξ i) ω x y)
      (hairerPsiField N (ξ i) ω (spaceTimeProj y)) (hairerIPsiRecentred N (ξ j) ω x y')
      (hairerPsiField N (ξ j) ω (spaceTimeProj y'))
    unfold hairerIPsiPsiField
    calc _ = |hairerIPsiRecentred N (ξ i) ω x y * hairerPsiField N (ξ i) ω (spaceTimeProj y) *
          hairerIPsiRecentred N (ξ j) ω x y' * hairerPsiField N (ξ j) ω (spaceTimeProj y')| := by
          congr 1; ring
      _ ≤ _ := this
  have hmi : ∀ k (z : ParabolicSpace), Measurable (fun ω => hairerIPsiPsiField N (ξ k) x ω z) :=
    fun k z => measurable_hairerIPsiPsiField_apply N (hξ k) x z
  have hFi : Integrable (fun ω => hairerIPsiPsiField N (ξ i) x ω y *
      hairerIPsiPsiField N (ξ j) x ω y') P := by
    refine hdom.mono' ((hmi i y).mul (hmi j y')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hpt ω
  refine ⟨hFi, (integral_mono hFi.abs hdom hpt).trans ?_⟩
  rw [integral_div, integral_add s123 (hΨ4 j _), integral_add s12 (hv4 j y').1,
    integral_add (hv4 i y).1 (hΨ4 i _), hΨ4i, hΨ4i]
  unfold ipsiFourthWeightK
  have a1 := (hv4 i y).2
  have a2 := (hv4 j y').2
  linarith

theorem integral_sd4_gen {α : Type*} [MeasurableSpace α] {μ : Measure α} {f1 f2 f3 f4 : α → ℝ}
    (i1 : Integrable f1 μ) (i2 : Integrable f2 μ) (i3 : Integrable f3 μ) (i4 : Integrable f4 μ) :
    ∫ w, (f1 w - f2 w - f3 w + f4 w) ∂μ = (∫ w, f1 w ∂μ) - (∫ w, f2 w ∂μ) - (∫ w, f3 w ∂μ) +
      ∫ w, f4 w ∂μ := by
  have j1 : Integrable (fun w => f1 w - f2 w) μ := i1.sub i2
  have j2 : Integrable (fun w => f1 w - f2 w - f3 w) μ := j1.sub i3
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2]

/-- **The second moment of the difference of two tested fields.** -/
theorem ipsiMix_sub_integral_sq_eq (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) :
    ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
      {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → (∀ i, ε i ∈ Set.Ioc (0 : ℝ) 1) →
      (∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) → ∀ {t : ℝ}, 0 < t → ∀ x : ParabolicSpace,
        ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N (ξ 0) x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N (ξ 1) x ω y) ^ 2 ∂P =
          ∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
            parabolicSemigroup.kernel t x q.2 *
            arrSd (fun i j => ∫ ω, hairerIPsiPsiField N (ξ i) x ω q.1 *
              hairerIPsiPsiField N (ξ j) x ω q.2 ∂P) := by
  obtain ⟨Cm, hCm, hb⟩ := ipsiMix_mul_integrable_bound.{u} N hρ
  intro Ω _ P W ε ξ hW hε hξ t ht x
  have := hW.isProbabilityMeasure
  set Q := fun y => parabolicSemigroup.kernel t x y with hQ
  set X : Fin 2 → Ω → ℝ := fun i ω => ∫ y, parabolicSemigroup.kernel t x y *
    hairerIPsiPsiField N (ξ i) x ω y with hX
  have hKm : Measurable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y) :=
    measurable_parabolicSemigroup_kernel t x
  have gen : ∀ i j : Fin 2,
      Integrable (fun ω => X i ω * X j ω) P ∧
      ∫ ω, X i ω * X j ω ∂P = ∫ q : ParabolicSpace × ParabolicSpace,
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          ∫ ω, hairerIPsiPsiField N (ξ i) x ω q.1 * hairerIPsiPsiField N (ξ j) x ω q.2 ∂P ∧
      Integrable (fun q : ParabolicSpace × ParabolicSpace =>
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          ∫ ω, hairerIPsiPsiField N (ξ i) x ω q.1 * hairerIPsiPsiField N (ξ j) x ω q.2 ∂P)
        (volume.prod volume) := fun i j =>
    integral_mul_integral_eq_integral_prod hKm (measurable_hairerIPsiPsiField_uncurry_cov N (hξ i) x)
      (measurable_hairerIPsiPsiField_uncurry_cov N (hξ j) x)
      (fun a a' => (hb hW hε hξ i j x a a').1) (fun a a' => (hb hW hε hξ i j x a a').2)
      (integrable_kernel_mul_ipsiFourthWeightK ht x Cm _)
  obtain ⟨i00, e00, j00⟩ := gen 0 0
  obtain ⟨i01, e01, j01⟩ := gen 0 1
  obtain ⟨i10, e10, j10⟩ := gen 1 0
  obtain ⟨i11, e11, j11⟩ := gen 1 1
  have lhs : ∀ ω, (X 0 ω - X 1 ω) ^ 2 =
      X 0 ω * X 0 ω - X 0 ω * X 1 ω - X 1 ω * X 0 ω + X 1 ω * X 1 ω := fun ω => by ring
  have rhs : ∀ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
      parabolicSemigroup.kernel t x q.2 * arrSd (fun i j => ∫ ω, hairerIPsiPsiField N (ξ i) x ω q.1 *
        hairerIPsiPsiField N (ξ j) x ω q.2 ∂P) =
      parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 0) x ω q.1 * hairerIPsiPsiField N (ξ 0) x ω q.2 ∂P) -
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 0) x ω q.1 * hairerIPsiPsiField N (ξ 1) x ω q.2 ∂P) -
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 1) x ω q.1 * hairerIPsiPsiField N (ξ 0) x ω q.2 ∂P) +
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 1) x ω q.1 * hairerIPsiPsiField N (ξ 1) x ω q.2 ∂P) :=
    fun q => by unfold arrSd; ring
  have L : ∫ ω, (X 0 ω - X 1 ω) ^ 2 ∂P = ∫ ω, (X 0 ω * X 0 ω - X 0 ω * X 1 ω -
      X 1 ω * X 0 ω + X 1 ω * X 1 ω) ∂P := integral_congr_ae (ae_of_all _ lhs)
  have R : ∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
      parabolicSemigroup.kernel t x q.2 * arrSd (fun i j => ∫ ω, hairerIPsiPsiField N (ξ i) x ω q.1 *
        hairerIPsiPsiField N (ξ j) x ω q.2 ∂P) = ∫ q : ParabolicSpace × ParabolicSpace,
      (parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 0) x ω q.1 * hairerIPsiPsiField N (ξ 0) x ω q.2 ∂P) -
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 0) x ω q.1 * hairerIPsiPsiField N (ξ 1) x ω q.2 ∂P) -
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 1) x ω q.1 * hairerIPsiPsiField N (ξ 0) x ω q.2 ∂P) +
        parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
          (∫ ω, hairerIPsiPsiField N (ξ 1) x ω q.1 * hairerIPsiPsiField N (ξ 1) x ω q.2 ∂P)) :=
    integral_congr_ae (ae_of_all _ rhs)
  change ∫ ω, (X 0 ω - X 1 ω) ^ 2 ∂P = _
  rw [L, R, integral_sd4_gen i00 i01 i10 i11]
  erw [integral_sd4_gen j00 j01 j10 j11]
  rw [e00, e01, e10, e11]
  rfl

end RegularityStructures.Phi43

end

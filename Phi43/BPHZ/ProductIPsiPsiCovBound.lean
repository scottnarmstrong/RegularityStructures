/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovIdentity
public import Phi43.BPHZ.ProductIPsiPsiCovLint
public import Phi43.BPHZ.ProductIPsiPsiCovMoment
public import Phi43.BPHZ.TreeI2Psi2FieldMean
import Mathlib.Tactic

/-!
# The pointwise covariance bound for `Π_x I(Ψ)Ψ`

With `r = ‖y - x‖`, `r' = ‖y' - x‖`, `e₁ = s(x - y)`, `e₂ = s(x - y')` (periodic sizes),
`d = s(y - y')` and `W(r) = r^γ (1 + r)`,
`|E[F(y) F(y')]| ≤ C (W(r) W(r') (1 + e₁^(-θ)) (1 + e₂^(-θ)) + r^((3-δ)/2) r'^((3-δ)/2) d^(-1))`,
uniformly in `ε ∈ (0, 1]`, for `y, y'` in general position
(`hairerIPsiPsiField_cov_abs_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ipsi_cov_alg {A A' B R R' Q X Y K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hAA : |A * A'| ≤ K * X) (hRR : |R * R'| ≤ K * X) (hB : |B * Q| ≤ M * Y) :
    |A * A' + B * Q + R * R'| ≤ (2 * K + M) * (X + Y) := by
  calc |A * A' + B * Q + R * R'| ≤ |A * A'| + |B * Q| + |R * R'| := abs_add_three _ _ _
    _ ≤ _ := by nlinarith [mul_nonneg hK hY, mul_nonneg hM hX]

/-- `|E v₁(y) v₁(y')| ≤ C r^((3-δ)/2) r'^((3-δ)/2)`. -/
theorem abs_hairerIPsiRecentred_integral_mul_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : ParabolicSpace, 0 < parabolicNorm (y - x) → 0 < parabolicNorm (y' - x) →
        |∫ ω, hairerIPsiRecentred N ξ ω x y * hairerIPsiRecentred N ξ ω x y' ∂P| ≤
          C * (parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2)) := by
  obtain ⟨Cm, hCm, hm⟩ := hairerIPsiRecentred_integral_sq_le.{u} N hρ hδ hδ1
  obtain ⟨Ci, hCi, hi⟩ := hairerIPsiRecentred_pow_le.{u} N hρ (k := 1) (by norm_num)
  refine ⟨Cm, hCm, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' hr hr'
  have hsq : ∀ z : ParabolicSpace, ∫ ω, hairerIPsiRecentred N ξ ω x z ^ 2 ∂P ≤
      Cm * (parabolicNorm (z - x) ^ ((3 - δ) / 2)) ^ 2 := fun z => by
    have hh := hm hW hε hξ x z
    have e : (parabolicNorm (z - x) ^ ((3 - δ) / 2)) ^ 2 = parabolicNorm (z - x) ^ (3 - δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (parabolicNorm_nonneg _)]
      congr 1; push_cast; ring
    rwa [e]
  have hmeas : ∀ z : ParabolicSpace, AEStronglyMeasurable
      (fun ω => hairerIPsiRecentred N ξ ω x z) P := fun z =>
    (Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ q.1 x q.2)
      (f := fun ω : Ω => (ω, z)) (measurable_hairerIPsiRecentred_prod_uncurry N hξ x)
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact abs_integral_mul_le_of_sq_le (hi hW hε hξ x y).1 (hi hW hε hξ x y').1 (hmeas y) (hmeas y')
    (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hr' _) (hsq y) (hsq y')

/-- **Pointwise covariance bound for `Π_x I(Ψ)Ψ`.** -/
theorem hairerIPsiPsiField_cov_abs_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {θ γ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hγ1 : γ < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : ParabolicSpace, 0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y) →
        0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y') →
        0 < torusParabolicSize (spaceTimeProj y - spaceTimeProj y') →
        0 < parabolicNorm (y - x) → 0 < parabolicNorm (y' - x) →
        |∫ ω, hairerIPsiPsiField N ξ x ω y * hairerIPsiPsiField N ξ x ω y' ∂P| ≤
          C * ((parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
            (parabolicNorm (y' - x) ^ γ * (1 + parabolicNorm (y' - x))) *
            ((1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-θ)) *
              (1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y') ^ (-θ))) +
            parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2) *
              torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ))) := by
  obtain ⟨Ck, hCk, hk⟩ := ipsiTaylorKernel_pairing_le N hρ hθ hθ1 hγ hγ1
  obtain ⟨Cm, hCm, hm⟩ := abs_hairerIPsiRecentred_integral_mul_le.{u} N hρ hδ hδ1
  obtain ⟨Cq, hCq, hq⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨2 * Ck ^ 2 + Cm * Cq, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y y' h1 h2 hd hr hr'
  have kA := hk hε.1 hε.2 x y h1
  have kA' := hk hε.1 hε.2 x y' h2
  have kR := hk hε.1 hε.2 x y h2
  have kR'0 := hk hε.1 hε.2 x y' h1
  have hQ : ∀ w : SpaceTime, hairerCovariance N ρ ε (spaceTimeProj y - w) =
      hairerCovariance N ρ ε (w - spaceTimeProj y) :=
    fun w => by rw [← hairerCovariance_neg N ρ ε (spaceTimeProj y - w), neg_sub]
  have kR' : Integrable (fun w => ipsiTaylorKernel N x y' w *
        hairerCovariance N ρ ε (spaceTimeProj y - w)) ∧
      |∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (spaceTimeProj y - w)| ≤
        Ck * (parabolicNorm (y' - x) ^ γ * (1 + parabolicNorm (y' - x))) *
          (1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-θ)) := by
    simp only [hQ]
    exact kR'0
  rw [hairerIPsiPsiField_integral_mul N hρ hε.1 hW hξ x y y' kA.1 kA'.1 kR.1 kR'.1]
  have hB := hm hW hε hξ x y y' hr hr'
  have hQd := hq hε.1 hε.2 _ hd
  have e1 : 0 ≤ torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-θ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have e2 : 0 ≤ torusParabolicSize (spaceTimeProj x - spaceTimeProj y') ^ (-θ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set r := parabolicNorm (y - x) with hrdef
  set r' := parabolicNorm (y' - x) with hrdef'
  set e1' := torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-θ) with he1
  set e2' := torusParabolicSize (spaceTimeProj x - spaceTimeProj y') ^ (-θ) with he2
  have hrr : 0 ≤ r ^ γ * (1 + r) := by positivity
  have hrr' : 0 ≤ r' ^ γ * (1 + r') := by positivity
  have hX : 0 ≤ (r ^ γ * (1 + r)) * (r' ^ γ * (1 + r')) * ((1 + e1') * (1 + e2')) := by positivity
  have hY : 0 ≤ r ^ ((3 - δ) / 2) * r' ^ ((3 - δ) / 2) *
      torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ)) := by positivity
  refine ipsi_cov_alg (K := Ck ^ 2) (M := Cm * Cq) (by positivity) (by positivity) hX hY ?_ ?_ ?_
  · rw [abs_mul]
    calc _ ≤ (Ck * (r ^ γ * (1 + r)) * (1 + e1')) * (Ck * (r' ^ γ * (1 + r')) * (1 + e2')) :=
          mul_le_mul kA.2 kA'.2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [abs_mul]
    calc _ ≤ (Ck * (r ^ γ * (1 + r)) * (1 + e2')) * (Ck * (r' ^ γ * (1 + r')) * (1 + e1')) :=
          mul_le_mul kR.2 kR'.2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [abs_mul]
    calc _ ≤ (Cm * (r ^ ((3 - δ) / 2) * r' ^ ((3 - δ) / 2))) *
          (Cq * torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ))) :=
          mul_le_mul hB hQd (abs_nonneg _) (by positivity)
      _ = _ := by ring

end RegularityStructures.Phi43

end

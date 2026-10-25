/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSqCovIdentity
public import Phi43.BPHZ.ProductIPsiPsiCovBound
import Mathlib.Tactic

/-!
# The pointwise covariance bound for `Π_x I(Ψ)(Ψ² - c₁)`

With the notation of `ProductIPsiPsiCovBound` and `d = s(p - p')`,
`|E[F(y) F(y')]| ≤ C (W(r) W(r') (1 + e₁^(-θ)) (1 + e₂^(-θ)) d^(-1) +
  r^((3-δ)/2) r'^((3-δ)/2) d^(-2))`
(`hairerIPsiPsiSqField_cov_abs_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ipsi_sq_cov_alg {A A' B R R' Q X Y D1 D2 K M Cq : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hAA : |A * A'| ≤ K * X) (hRR : |R * R'| ≤ K * X) (hB : |B| ≤ M * Y)
    (hQ : |Q| ≤ Cq * D1) (hD : D2 = D1 ^ 2) :
    |2 * B * Q ^ 2 + 4 * (A * A' * Q) + 4 * (R * R' * Q)| ≤
      (8 * K * Cq) * (X * D1) + (2 * M * Cq ^ 2) * (Y * D2) := by
  have hQ2 : Q ^ 2 ≤ Cq ^ 2 * D1 ^ 2 := by
    have := abs_nonneg Q
    nlinarith [sq_abs Q, mul_self_le_mul_self this hQ]
  have h1 : |2 * B * Q ^ 2| ≤ 2 * (M * Y) * (Cq ^ 2 * D1 ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg Q)]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) hQ2 (sq_nonneg _)
      (by positivity)
  have h2 : |4 * (A * A' * Q)| ≤ 4 * (K * X * (Cq * D1)) := by
    rw [abs_mul, abs_mul]
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hAA hQ (abs_nonneg _) (by positivity))
      (by norm_num)
  have h3 : |4 * (R * R' * Q)| ≤ 4 * (K * X * (Cq * D1)) := by
    rw [abs_mul, abs_mul]
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hRR hQ (abs_nonneg _) (by positivity))
      (by norm_num)
  calc _ ≤ |2 * B * Q ^ 2| + |4 * (A * A' * Q)| + |4 * (R * R' * Q)| := abs_add_three _ _ _
    _ ≤ 2 * (M * Y) * (Cq ^ 2 * D1 ^ 2) + 4 * (K * X * (Cq * D1)) + 4 * (K * X * (Cq * D1)) := by
        linarith
    _ = _ := by rw [hD]; ring

theorem ipsi_sq_weighted_alg {a b X D Y D2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : 0 ≤ X * D)
    (hY : 0 ≤ Y * D2) : a * (X * D) + b * (Y * D2) ≤ (a + b) * (X * D + Y * D2) := by
  nlinarith [mul_nonneg ha hY, mul_nonneg hb hX]

/-- **Pointwise covariance bound for `Π_x I(Ψ)(Ψ² - c₁)`.** -/
theorem hairerIPsiPsiSqField_cov_abs_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {θ γ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hγ1 : γ < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y y' : ParabolicSpace, 0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y) →
        0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y') →
        0 < torusParabolicSize (spaceTimeProj y - spaceTimeProj y') →
        0 < parabolicNorm (y - x) → 0 < parabolicNorm (y' - x) →
        |∫ ω, hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
            hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y' ∂P| ≤
          C * (((parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
            (parabolicNorm (y' - x) ^ γ * (1 + parabolicNorm (y' - x))) *
            ((1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-θ)) *
              (1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y') ^ (-θ)))) *
              torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ)) +
            (parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2)) *
              torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(2 : ℝ))) := by
  obtain ⟨Ck, hCk, hk⟩ := ipsiTaylorKernel_pairing_le N hρ hθ hθ1 hγ hγ1
  obtain ⟨Cm, hCm, hm⟩ := abs_hairerIPsiRecentred_integral_mul_le.{u} N hρ hδ hδ1
  obtain ⟨Cq, hCq, hq⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨8 * Ck ^ 2 * Cq + 2 * Cm * Cq ^ 2, by positivity, ?_⟩
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
  rw [hairerIPsiPsiSqField_integral_mul N hρ hε.1 hW hξ x y y' kA.1 kA'.1 kR.1 kR'.1]
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
  set D1 := torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ)) with hD1
  have hrr : 0 ≤ r ^ γ * (1 + r) := by positivity
  have hrr' : 0 ≤ r' ^ γ * (1 + r') := by positivity
  have hX : 0 ≤ (r ^ γ * (1 + r)) * (r' ^ γ * (1 + r')) * ((1 + e1') * (1 + e2')) := by positivity
  have hY : 0 ≤ r ^ ((3 - δ) / 2) * r' ^ ((3 - δ) / 2) := by positivity
  have hD1n : 0 ≤ D1 := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hD2 : torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(2 : ℝ)) = D1 ^ 2 := by
    rw [hD1, ← Real.rpow_natCast, ← Real.rpow_mul (torusParabolicSize_nonneg _)]
    congr 1; push_cast; ring
  have h := ipsi_sq_cov_alg (K := Ck ^ 2) (M := Cm) (Cq := Cq) (by positivity) hCm hX hY
    (A := ∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - spaceTimeProj y))
    (A' := ∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (w - spaceTimeProj y'))
    (R := ∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - spaceTimeProj y'))
    (R' := ∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (spaceTimeProj y - w))
    (B := ∫ ω, hairerIPsiRecentred N ξ ω x y * hairerIPsiRecentred N ξ ω x y' ∂P)
    (Q := hairerCovariance N ρ ε (spaceTimeProj y - spaceTimeProj y'))
    (D2 := D1 ^ 2) ?_ ?_ hB hQd rfl
  · rw [hD2]
    refine h.trans ?_
    exact ipsi_sq_weighted_alg (by positivity) (by positivity) (mul_nonneg hX hD1n)
      (mul_nonneg hY (sq_nonneg _))
  · rw [abs_mul]
    calc _ ≤ (Ck * (r ^ γ * (1 + r)) * (1 + e1')) * (Ck * (r' ^ γ * (1 + r')) * (1 + e2')) :=
          mul_le_mul kA.2 kA'.2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [abs_mul]
    calc _ ≤ (Ck * (r ^ γ * (1 + r)) * (1 + e2')) * (Ck * (r' ^ γ * (1 + r')) * (1 + e1')) :=
          mul_le_mul kR.2 kR'.2 (abs_nonneg _) (by positivity)
      _ = _ := by ring

end RegularityStructures.Phi43

end

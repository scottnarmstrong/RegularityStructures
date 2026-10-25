/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondDomination
public import Phi43.BPHZ.ProductIPsiPsiSqCovBound
import Mathlib.Tactic

/-!
# Domination of the tested covariance of `I(Ψ)(Ψ² - c₁)` by a periodisable majorant

Almost everywhere on `ℝ⁴ × ℝ⁴`,
`|Q(y) Q(y') E[F(y) F(y')]| ≤ C (lam^γ lam^γ h h' Θ₁ s(u - v)^(-1) + lam^a lam^a h h' s(u - v)^(-2))`
(`ipsi_sq_tested_cov_dominated`), and the corresponding integral bounds from the profile double
bounds.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Almost everywhere domination of the tested covariance, Wick-square product.** -/
theorem ipsi_sq_tested_cov_dominated (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {θ γ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hγ1 : γ < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∀ᵐ q : ParabolicSpace × ParabolicSpace ∂volume,
          |parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
            ∫ ω, hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω q.1 *
              hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω q.2 ∂P| ≤
          C * (((t ^ (1 / 4 : ℝ)) ^ γ * (t ^ (1 / 4 : ℝ)) ^ γ) *
              (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-θ)) *
                  (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-θ))) *
                  torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)))) +
            ((t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2) * (t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2)) *
              (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(2 : ℝ)))) := by
  obtain ⟨C, hC, hcov⟩ := hairerIPsiPsiSqField_cov_abs_le.{u} N hρ hθ hθ1 hγ hγ1 hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  filter_upwards [ipsi_ae_time_ne x] with q ⟨h1, h2, h3⟩
  set y := q.1 with hy
  set y' := q.2 with hy'
  have p1 : 0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y) :=
    torusParabolicSize_pos_of_time_ne (z := spaceTimeProj x - spaceTimeProj y) (by
      simp only [spaceTimeProj, Prod.fst_sub]; exact sub_ne_zero.2 (Ne.symm h1))
  have p2 : 0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y') :=
    torusParabolicSize_pos_of_time_ne (z := spaceTimeProj x - spaceTimeProj y') (by
      simp only [spaceTimeProj, Prod.fst_sub]; exact sub_ne_zero.2 (Ne.symm h2))
  have p3 : 0 < torusParabolicSize (spaceTimeProj y - spaceTimeProj y') :=
    torusParabolicSize_pos_of_time_ne (z := spaceTimeProj y - spaceTimeProj y') (by
      simp only [spaceTimeProj, Prod.fst_sub]; exact sub_ne_zero.2 h3)
  have r1 : 0 < parabolicNorm (y - x) :=
    parabolicNorm_pos_of_time_ne (z := y - x) (by
      simp only [Prod.fst_sub]; exact sub_ne_zero.2 h1)
  have r2 : 0 < parabolicNorm (y' - x) :=
    parabolicNorm_pos_of_time_ne (z := y' - x) (by
      simp only [Prod.fst_sub]; exact sub_ne_zero.2 h2)
  have hc := hcov hW hε hξ x y y' p1 p2 p3 r1 r2
  have sw1 := ipsi_size_swap (spaceTimeProj x) (spaceTimeProj y)
  have sw2 := ipsi_size_swap (spaceTimeProj x) (spaceTimeProj y')
  rw [sw1, sw2] at hc
  set l := t ^ (1 / 4 : ℝ) with hl
  have hn1 := parabolicNorm_nonneg (y - x)
  have hn2 := parabolicNorm_nonneg (y' - x)
  have hT : 0 ≤ ((1 + torusParabolicSize (spaceTimeProj y - spaceTimeProj x) ^ (-θ)) *
      (1 + torusParabolicSize (spaceTimeProj y' - spaceTimeProj x) ^ (-θ))) *
      torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ)) := by
    have a1 := Real.rpow_nonneg (torusParabolicSize_nonneg (spaceTimeProj y - spaceTimeProj x)) (-θ)
    have a2 := Real.rpow_nonneg (torusParabolicSize_nonneg (spaceTimeProj y' - spaceTimeProj x)) (-θ)
    have a3 := Real.rpow_nonneg (torusParabolicSize_nonneg (spaceTimeProj y - spaceTimeProj y'))
      (-(1 : ℝ))
    positivity
  have hD : 0 ≤ torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hcc : |∫ ω, hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
        hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y' ∂P| ≤
      C * ((parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
        (parabolicNorm (y' - x) ^ γ * (1 + parabolicNorm (y' - x))) *
        (((1 + torusParabolicSize (spaceTimeProj y - spaceTimeProj x) ^ (-θ)) *
          (1 + torusParabolicSize (spaceTimeProj y' - spaceTimeProj x) ^ (-θ))) *
          torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ))) +
        parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2) *
          torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(2 : ℝ))) := by
    refine hc.trans (le_of_eq ?_)
    ring
  have hW1 := ipsi_weightW_le hlam hlam1 hn1 hγ.le hγ1.le
  have hW2 := ipsi_weightW_le hlam hlam1 hn2 hγ.le hγ1.le
  have hV1 := ipsi_rpow_le_weight (a := (3 - δ) / 2) hlam hn1 (by linarith) (by linarith)
  have hV2 := ipsi_rpow_le_weight (a := (3 - δ) / 2) hlam hn2 (by linarith) (by linarith)
  have mk : ∀ (z : ParabolicSpace) {W' b : ℝ},
      W' ≤ b * (1 + parabolicNorm (z - x) / l) ^ 2 →
      |parabolicSemigroup.kernel t x z| * W' ≤ b * ipsiWeightedKernel t x z := by
    intro z W' b hh
    unfold ipsiWeightedKernel
    calc |parabolicSemigroup.kernel t x z| * W'
        ≤ |parabolicSemigroup.kernel t x z| * (b * (1 + parabolicNorm (z - x) / l) ^ 2) :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = _ := by ring
  have hlg : 0 ≤ l ^ γ := Real.rpow_nonneg hlam.le _
  have hla : 0 ≤ l ^ ((3 - δ) / 2) := Real.rpow_nonneg hlam.le _
  exact ipsi_pointwise_alg (q := parabolicSemigroup.kernel t x y)
    (q' := parabolicSemigroup.kernel t x y') hC hT hD (by positivity) (by positivity) hlg hla
    (ipsiWeightedKernel_nonneg t x y) hcc (mk y hW1) (mk y' hW2) (mk y hV1) (mk y' hV2)

end RegularityStructures.Phi43

end

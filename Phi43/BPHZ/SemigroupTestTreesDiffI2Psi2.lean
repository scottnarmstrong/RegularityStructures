/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Local
public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Cov
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2
public import Phi43.BPHZ.TreeI2Psi2CrossTestedPair

/-!
# The semigroup-tested second moment of the cross-mollifier difference of `I(Ψ²) Ψ²`

For `t ∈ (0, 1]`, `lam = t^(1/4)`, `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`:
`E|∫ (F_{ρ,ε} - F_{ρ',ε'})(w) q^♯_t(x, w) dw|² ≤ C (max ε ε')^(2θ) lam^(-(2θ+δ))`
(`hairerI2Psi2Field_sub_semigroupPeriodised_second_moment_le_delta`).

The covariance of the difference is bounded by the local cross bound
(`hairerI2Psi2Field_sub_cov_bound_cross`) when `s(y - x), s(y' - x) ≤ 1` and by the global cross
bound (`hairerI2Psi2Field_sub_cov_bound_cross_global`) otherwise.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem i2Psi2Diff_region_alg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hnb : ¬(p ≤ 1 ∧ q ≤ 1)) :
    (1 + p ^ 2 + q ^ 2) ^ 3 ≤ 32 * (p ^ 6 + q ^ 6) := by
  have hR : 1 ≤ p ^ 2 + q ^ 2 := by
    by_contra hlt
    have := not_le.1 hlt
    apply hnb
    constructor <;> nlinarith [sq_nonneg p, sq_nonneg q]
  have a1 : 1 + p ^ 2 + q ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by linarith
  have a2 : (1 + p ^ 2 + q ^ 2) ^ 3 ≤ (2 * (p ^ 2 + q ^ 2)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) a1 3
  have a3 : (p ^ 2 + q ^ 2) ^ 3 ≤ 4 * (p ^ 6 + q ^ 6) := by
    nlinarith [sq_nonneg (p ^ 2 - q ^ 2), mul_nonneg (sq_nonneg p) (sq_nonneg q),
      sq_nonneg (p ^ 2), sq_nonneg (q ^ 2), mul_nonneg (mul_nonneg (sq_nonneg p) (sq_nonneg q))
        (add_nonneg (sq_nonneg p) (sq_nonneg q))]
  calc (1 + p ^ 2 + q ^ 2) ^ 3 ≤ (2 * (p ^ 2 + q ^ 2)) ^ 3 := a2
    _ = 8 * (p ^ 2 + q ^ 2) ^ 3 := by ring
    _ ≤ 8 * (4 * (p ^ 6 + q ^ 6)) := by linarith
    _ = 32 * (p ^ 6 + q ^ 6) := by ring

theorem i2Psi2DiffF_eq_localMajorant (x u v : SpaceTime) (θ δ : ℝ) :
    i2Psi2DiffF θ δ (torusParabolicSize (u - x)) (torusParabolicSize (v - x))
      (torusParabolicSize (u - v)) = i2Psi2DiffLocalMajorant x θ δ u v := by
  unfold i2Psi2DiffF i2Psi2DiffLocalMajorant
  simp only [Real.rpow_zero, mul_one, one_mul]
  ring

/-- **Second moment of the tested cross-mollifier difference of `I(Ψ²) Ψ²`, with loss `δ`.** -/
theorem hairerI2Psi2Field_sub_semigroupPeriodised_second_moment_le_delta (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω w -
            hairerI2Psi2Field N ρ' ε' ξ' (spaceTimeProj x) ω w) * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by
  obtain ⟨Cc, hCc, hloc⟩ := hairerI2Psi2Field_sub_cov_bound_cross.{u} N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨Cg, hCg, hglob⟩ := hairerI2Psi2Field_sub_cov_bound_cross_global.{u} N hρ hρ' hθ hθ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨Cc * |i2Psi2DiffLocalConst B parabolicMomentConst θ δ| +
    32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1|, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hη : 0 ≤ 2 * θ + δ := by linarith
  have hL1 : 1 ≤ (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hmax : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hμ2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hmax.le _
  set μ2 : ℝ := (max ε ε') ^ (2 * θ) with hμ2def
  have hYm : Measurable (fun q : Ω × SpaceTime => hairerI2Psi2Field N ρ ε ξ x' q.1 q.2 -
      hairerI2Psi2Field N ρ' ε' ξ' x' q.1 q.2) :=
    (measurable_hairerI2Psi2Field_uncurry N hξ x').sub (measurable_hairerI2Psi2Field_uncurry N hξ' x')
  have hL2 := fun u => hairerI2Psi2Field_sub_memLp_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x' u
  obtain ⟨M, hMb⟩ := hairerI2Psi2Field_sub_pair_integrable_bound_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x'
  have hM : ∀ u : SpaceTime, ∫ ω, (hairerI2Psi2Field N ρ ε ξ x' ω u - hairerI2Psi2Field N ρ' ε' ξ' x' ω u) *
      (hairerI2Psi2Field N ρ ε ξ x' ω u - hairerI2Psi2Field N ρ' ε' ξ' x' ω u) ∂P ≤ M := by
    intro u
    obtain ⟨hi, hb⟩ := hMb u u
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => hairerI2Psi2Field N ρ ε ξ x' ω u - hairerI2Psi2Field N ρ' ε' ξ' x' ω u) hYm
  have hMl := (h.doubleBound_i2Psi2DiffLocal hlam hθ hθ1 hδ1).const_mul (mul_nonneg hCc hμ2)
  have hMg := (h.doubleBound_global hlam hlam1 (n := 6) (e := 2 + 2 * θ) (a := 1)
    (by linarith) (by linarith) (by norm_num) (by linarith) (by norm_num)).const_mul
    (by positivity : (0 : ℝ) ≤ 32 * Cg * μ2)
  have hbound := semigroupDoubleBound_of_majorants (x := x')
    (Φ := fun u v => ∫ ω, (hairerI2Psi2Field N ρ ε ξ x' ω u - hairerI2Psi2Field N ρ' ε' ξ' x' ω u) *
      (hairerI2Psi2Field N ρ ε ξ x' ω v - hairerI2Psi2Field N ρ' ε' ξ' x' ω v) ∂P) h.measurable hΦ
    hMl hMg
    (fun u v => mul_nonneg (mul_nonneg hCc hμ2) (i2Psi2DiffLocalMajorant_nonneg x' θ δ u v))
    (fun u v => mul_nonneg (by positivity) (semigroupTestGlobalMajorant_nonneg x' 6 (2 + 2 * θ) 1 u v))
    (by
      filter_upwards [ae_pos_triple x'] with w hw h1 h2
      have hc := hloc hW hε hε' hξ hξ' x' w.1 w.2 hw.1 hw.2.1 hw.2.2 h1 h2
      rw [i2Psi2DiffF_eq_localMajorant] at hc
      exact hc)
    (by
      filter_upwards [ae_pos_triple x'] with w hw hnb
      have hc := hglob hW hε hε' hξ hξ' x' w.1 w.2 hw.1 hw.2.1 hw.2.2
      refine hc.trans ?_
      rw [semigroupTestGlobalMajorant_eq (n := 6) (e := 2 + 2 * θ) (a := 1) hw.1 hw.2.1]
      have hu6 : torusParabolicSize (w.1 - x') ^ (6 : ℝ) = torusParabolicSize (w.1 - x') ^ 6 := by
        exact_mod_cast Real.rpow_natCast (torusParabolicSize (w.1 - x')) 6
      have hv6 : torusParabolicSize (w.2 - x') ^ (6 : ℝ) = torusParabolicSize (w.2 - x') ^ 6 := by
        exact_mod_cast Real.rpow_natCast (torusParabolicSize (w.2 - x')) 6
      rw [hu6, hv6]
      have key := i2Psi2Diff_region_alg (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) hnb
      have hS' : 0 ≤ torusParabolicSize (w.1 - w.2) ^ (-(2 + 2 * θ)) +
          torusParabolicSize (w.1 - x') ^ (-(1 : ℝ)) + torusParabolicSize (w.2 - x') ^ (-(1 : ℝ)) + 1 := by
        have := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - w.2)) (-(2 + 2 * θ))
        have := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - x')) (-(1 : ℝ))
        have := Real.rpow_nonneg (torusParabolicSize_nonneg (w.2 - x')) (-(1 : ℝ))
        linarith
      have hCμ : 0 ≤ Cg * μ2 := mul_nonneg hCg hμ2
      calc Cg * μ2 * (1 + torusParabolicSize (w.1 - x') ^ 2 + torusParabolicSize (w.2 - x') ^ 2) ^ 3 *
            (torusParabolicSize (w.1 - w.2) ^ (-(2 + 2 * θ)) + torusParabolicSize (w.1 - x') ^ (-(1 : ℝ)) +
              torusParabolicSize (w.2 - x') ^ (-(1 : ℝ)) + 1)
          = (Cg * μ2) * ((1 + torusParabolicSize (w.1 - x') ^ 2 +
              torusParabolicSize (w.2 - x') ^ 2) ^ 3 *
            (torusParabolicSize (w.1 - w.2) ^ (-(2 + 2 * θ)) + torusParabolicSize (w.1 - x') ^ (-(1 : ℝ)) +
              torusParabolicSize (w.2 - x') ^ (-(1 : ℝ)) + 1)) := by ring
        _ ≤ (Cg * μ2) * ((32 * (torusParabolicSize (w.1 - x') ^ 6 + torusParabolicSize (w.2 - x') ^ 6)) *
            (torusParabolicSize (w.1 - w.2) ^ (-(2 + 2 * θ)) + torusParabolicSize (w.1 - x') ^ (-(1 : ℝ)) +
              torusParabolicSize (w.2 - x') ^ (-(1 : ℝ)) + 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right key hS') hCμ
        _ = _ := by ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : (Cc * μ2) * (i2Psi2DiffLocalConst B parabolicMomentConst θ δ *
      (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ))) ≤
      Cc * |i2Psi2DiffLocalConst B parabolicMomentConst θ δ| * μ2 *
        (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by
    have hl := Real.rpow_nonneg hlam.le (-(2 * θ + δ))
    calc (Cc * μ2) * (i2Psi2DiffLocalConst B parabolicMomentConst θ δ *
          (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)))
        = (Cc * μ2) * i2Psi2DiffLocalConst B parabolicMomentConst θ δ *
          (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by ring
      _ ≤ (Cc * μ2) * |i2Psi2DiffLocalConst B parabolicMomentConst θ δ| *
          (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _)
            (mul_nonneg hCc hμ2)) hl
      _ = _ := by ring
  have e2 : (32 * Cg * μ2) * semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1 ≤
      32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1| * μ2 *
        (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by
    have h0 : 0 ≤ 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1| *
        μ2 := by positivity
    calc (32 * Cg * μ2) * semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1
        ≤ (32 * Cg * μ2) * |semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (2 + 2 * θ) 1| * μ2 * 1 := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 h0
  nlinarith [e1, e2]

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Local
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Field
public import Phi43.BPHZ.SemigroupTestTreesAssembly
public import Phi43.BPHZ.TreeI2Psi2TestedMoment

/-!
# The a-priori bound (10.2) for `I(Ψ²) Ψ²` against the periodised semigroup kernel

For `t ∈ (0, 1]`, `lam = t^(1/4)` and a base point `x ∈ ℝ⁴`,
`E|∫ F_{proj x}(w) q^♯_t(x, w) dw|² ≤ C lam^(-δ)` for `δ ∈ (0, 1/2]`, uniformly in `ε ∈ (0, 1]`,
`t ∈ (0, 1]` and `x` (`hairerI2Psi2Field_semigroupPeriodised_second_moment_le_delta`), and with
`δ = min (1/2, 7κ)` the bound `C lam^(2 (-4κ) + κ)` of [Hai14, (10.2)]
(`hairerI2Psi2Field_semigroupPeriodised_second_moment_le`).

The covariance of the field is bounded by the local bound of `hairerI2Psi2Field_cov_bound` when
`s(y - x), s(y' - x) ≤ 1` and by `hairerI2Psi2Field_cov_bound_global` otherwise.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem rpow_mul_rpow_le_add_rpow_two_mul {r r' a : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    r ^ a * r' ^ a ≤ r ^ (2 * a) + r' ^ (2 * a) := by
  have e1 : r ^ (2 * a) = (r ^ a) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num; ring_nf
  have e2 : r' ^ (2 * a) = (r' ^ a) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr']; norm_num; ring_nf
  rw [e1, e2]
  nlinarith [sq_nonneg (r ^ a - r' ^ a), Real.rpow_nonneg hr a, Real.rpow_nonneg hr' a]

/-- The algebra of the global region: with `p, q ≥ 0` not both at most `1`. -/
theorem global_region_alg {C p q d2 d1 dh A B : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hnb : ¬(p ≤ 1 ∧ q ≤ 1)) (hd2 : 0 ≤ d2) (hd1 : d1 ≤ d2 + 1) (hdh : dh ≤ d2 + 1)
    (hd1' : 0 ≤ d1) (hdh' : 0 ≤ dh) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    C * (1 + p ^ 2 + q ^ 2) ^ 3 * (d2 + d1 + dh + A + B) ≤
      96 * C * ((p ^ 6 + q ^ 6) * (d2 + A + B + 1)) := by
  have hR : 1 ≤ p ^ 2 + q ^ 2 := by
    by_contra hlt
    have := not_le.1 hlt
    apply hnb
    constructor <;> nlinarith [sq_nonneg p, sq_nonneg q]
  have h1 : (1 + p ^ 2 + q ^ 2) ^ 3 ≤ 32 * (p ^ 6 + q ^ 6) := by
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
  have h2 : d2 + d1 + dh + A + B ≤ 3 * (d2 + A + B + 1) := by linarith
  have hS : 0 ≤ d2 + d1 + dh + A + B := by linarith
  calc C * (1 + p ^ 2 + q ^ 2) ^ 3 * (d2 + d1 + dh + A + B)
      ≤ C * (32 * (p ^ 6 + q ^ 6)) * (3 * (d2 + A + B + 1)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 hS (by positivity)
    _ = 96 * C * ((p ^ 6 + q ^ 6) * (d2 + A + B + 1)) := by ring

/-- `s^(-e) ≤ s^(-f) + 1` for `0 ≤ e ≤ f`. -/
theorem rpow_neg_le_rpow_neg_add_one {s e f : ℝ} (hs : 0 < s) (he : 0 ≤ e) (hef : e ≤ f) :
    s ^ (-e) ≤ s ^ (-f) + 1 := by
  rcases le_total s 1 with h | h
  · have : s ^ (-e) ≤ s ^ (-f) := Real.rpow_le_rpow_of_exponent_ge hs h (by linarith)
    have := Real.rpow_nonneg hs.le (-f)
    linarith
  · have : s ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have := Real.rpow_nonneg hs.le (-f)
    linarith

/-- **Second moment of the tested tree `I(Ψ²) Ψ²`, semigroup test, with loss `δ`.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x ∈ ℝ⁴`. -/
theorem hairerI2Psi2Field_semigroupPeriodised_second_moment_le_delta (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤ C * (t ^ (1 / 4 : ℝ)) ^ (-δ) := by
  have hδ₁0 : 0 < δ / 2 := by linarith
  have hδ₁4 : δ / 2 ≤ 1 / 4 := by linarith
  have ha0 : 0 < (1 - δ) / 2 := by linarith
  have ha2 : (1 - δ) / 2 < 1 / 2 := by linarith
  obtain ⟨Cc, hCc, hloc⟩ := hairerI2Psi2Field_cov_bound.{u} N hρ hδ₁0 hδ₁4 ha0 ha2
  obtain ⟨Cg, hCg, hglob⟩ := hairerI2Psi2Field_cov_bound_global.{u} N hρ
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨Cc * |i2Psi2LocalConst B parabolicMomentConst (δ / 2) ((1 - δ) / 2)| +
    96 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2)|, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hL1 : 1 ≤ (t ^ (1 / 4 : ℝ)) ^ (-δ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hYm := measurable_hairerI2Psi2Field_uncurry N hξ x'
  have hL2 := fun u => hairerI2Psi2Field_memLp N hρ hε.1 hW hξ x' u
  have hM : ∀ u : SpaceTime, ∫ ω, hairerI2Psi2Field N ρ ε ξ x' ω u *
      hairerI2Psi2Field N ρ ε ξ x' ω u ∂P ≤
      (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (24 * hairerWickConstant N ρ ε ^ 4) +
          (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (32 * hairerWickConstant N ρ ε ^ 4) +
          (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) *
            (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) := by
    intro u
    obtain ⟨hi, hb⟩ := hairerI2Psi2Field_pair_integrable_bound N hρ hε.1 hW hξ x' u u
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => hairerI2Psi2Field N ρ ε ξ x' ω u) hYm
  have hMl := (h.doubleBound_i2Psi2Local hlam hlam1 hδ hδ1).const_mul hCc
  have hMg := (h.doubleBound_global hlam hlam1 (n := 6) (e := 2) (a := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).const_mul
    (by positivity : (0 : ℝ) ≤ 96 * Cg)
  have hbound := semigroupDoubleBound_of_majorants (x := x') (Φ := fun u v => ∫ ω,
      hairerI2Psi2Field N ρ ε ξ x' ω u * hairerI2Psi2Field N ρ ε ξ x' ω v ∂P) h.measurable hΦ
    hMl hMg
    (fun u v => mul_nonneg hCc (i2Psi2LocalMajorant_nonneg x' (δ / 2) ((1 - δ) / 2) u v))
    (fun u v => mul_nonneg (by positivity) (semigroupTestGlobalMajorant_nonneg x' 6 2 (1 / 2) u v))
    (by
      filter_upwards [ae_pos_triple x'] with w hw h1 h2
      have hc := hloc hW hε hξ x' w.1 w.2 hw.1 hw.2.1 hw.2.2 h1 h2
      refine hc.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCc
      have pa := rpow_mul_rpow_le_add_rpow_two_mul (r := torusParabolicSize (w.1 - x'))
        (r' := torusParabolicSize (w.2 - x')) (a := (1 - δ) / 2)
        (torusParabolicSize_nonneg _) (torusParabolicSize_nonneg _)
      have hd1 : 0 ≤ torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have := mul_le_mul_of_nonneg_right pa hd1
      simp only [i2Psi2LocalMajorant, Real.rpow_zero, mul_one, one_mul]
      linarith)
    (by
      filter_upwards [ae_pos_triple x'] with w hw hnb
      have hc := hglob hW hε hξ x' w.1 w.2 hw.1 hw.2.1 hw.2.2
      refine hc.trans ?_
      rw [semigroupTestGlobalMajorant_eq (n := 6) (e := 2) (a := 1 / 2) hw.1 hw.2.1]
      have hu6 : torusParabolicSize (w.1 - x') ^ (6 : ℝ) = torusParabolicSize (w.1 - x') ^ 6 := by
        exact_mod_cast Real.rpow_natCast (torusParabolicSize (w.1 - x')) 6
      have hv6 : torusParabolicSize (w.2 - x') ^ (6 : ℝ) = torusParabolicSize (w.2 - x') ^ 6 := by
        exact_mod_cast Real.rpow_natCast (torusParabolicSize (w.2 - x')) 6
      rw [hu6, hv6]
      have key := global_region_alg (C := Cg) (A := torusParabolicSize (w.1 - x') ^ (-(1 / 2 : ℝ)))
        (B := torusParabolicSize (w.2 - x') ^ (-(1 / 2 : ℝ))) hCg (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) hnb
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) (-(2 : ℝ)))
        (rpow_neg_le_rpow_neg_add_one hw.2.2 (by norm_num) (by norm_num :
          (1 : ℝ) ≤ 2))
        (rpow_neg_le_rpow_neg_add_one hw.2.2 (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 2))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) (-(1 / 2 : ℝ)))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) (-(1 / 2 : ℝ)))
      refine key.trans (le_of_eq ?_)
      ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : Cc * (i2Psi2LocalConst B parabolicMomentConst (δ / 2) ((1 - δ) / 2) *
      (t ^ (1 / 4 : ℝ)) ^ (-δ)) ≤
      Cc * |i2Psi2LocalConst B parabolicMomentConst (δ / 2) ((1 - δ) / 2)| *
        (t ^ (1 / 4 : ℝ)) ^ (-δ) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hCc)
      (Real.rpow_nonneg hlam.le _)
  have e2 : 96 * Cg * semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2) ≤
      96 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2)| *
        (t ^ (1 / 4 : ℝ)) ^ (-δ) := by
    have h0 : 0 ≤ 96 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2)| := by
      positivity
    calc 96 * Cg * semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2)
        ≤ 96 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = 96 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 2 (1 / 2)| * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 h0
  linarith

/-- **The a-priori bound (10.2) for `I(Ψ²) Ψ²`, semigroup test** [Hai14, (10.2) with
`2|τ| + κ = -8κ + κ`]: `E|∫ F_{proj x} q^♯_t(x, ·)|² ≤ C lam^(2(-4κ) + κ)` (that is, `lam^(-7κ)`),
`lam = t^(1/4)`, uniformly in `ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x`. -/
theorem hairerI2Psi2Field_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (2 * (-4 * κ) + κ) := by
  have hδ : 0 < min (1 / 2 : ℝ) (7 * κ) := lt_min (by norm_num) (by linarith)
  obtain ⟨C, hC, h⟩ := hairerI2Psi2Field_semigroupPeriodised_second_moment_le_delta.{u} N hρ hδ
    (min_le_left _ _)
  refine ⟨C, hC, fun {Ω _ P W ε ξ} hW hε hξ {t} ht ht1 x => ?_⟩
  refine (h hW hε hξ ht ht1 x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) ?_
  have := min_le_right (1 / 2 : ℝ) (7 * κ)
  linarith

end RegularityStructures.Phi43

end

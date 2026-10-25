/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3PsiLocal
public import Phi43.BPHZ.SemigroupTestTreesI3PsiField
public import Phi43.BPHZ.SemigroupTestTreesAssembly
public import Phi43.BPHZ.TreeI3PsiTestedMoment

/-!
# The a-priori bound (10.2) for `I(Ψ³)Ψ` against the periodised semigroup kernel

For `t ∈ (0, 1]`, `lam = t^(1/4)` and a base point `x ∈ ℝ⁴`,
`E|∫ I₃Ψ_{proj x}(w) q^♯_t(x, w) dw|² ≤ C lam^(-δ)` for `δ ∈ (0, 1/4]`, uniformly in `ε ∈ (0, 1]`,
`t ∈ (0, 1]` and `x` (`hairerI3PsiField_semigroupPeriodised_second_moment_le_delta`), and with
`δ = min (1/4, 7κ)` the bound `C lam^(2 (-4κ) + κ)` of [Hai14, (10.2)]
(`hairerI3PsiField_semigroupPeriodised_second_moment_le`).

The covariance of `I₃Ψ_{x}` is bounded by the local bound of `hairerI3PsiField_cov_bound` when
`s(y - x), s(y' - x) ≤ 1` and by the global bound `hairerI3PsiField_cov_bound_global` otherwise; the
polynomial growth of the latter is absorbed by the moments of the profile
(`SemigroupTestProfile.doubleBound_global`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `s^(-δ) ≤ s^(-1) + 1` for `0 ≤ δ ≤ 1`. -/
theorem rpow_neg_le_rpow_neg_one_add_one {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    s ^ (-δ) ≤ s ^ (-(1 : ℝ)) + 1 := by
  rcases le_total s 1 with h | h
  · have : s ^ (-δ) ≤ s ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hs h (by linarith)
    linarith
  · have : s ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have := Real.rpow_nonneg hs.le (-(1 : ℝ))
    linarith

/-- **Second moment of the tested tree `I(Ψ³)Ψ`, semigroup test, with loss `δ`.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x ∈ ℝ⁴`. -/
theorem hairerI3PsiField_semigroupPeriodised_second_moment_le_delta (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤ C * (t ^ (1 / 4 : ℝ)) ^ (-δ) := by
  obtain ⟨Cc, hCc, hloc⟩ := hairerI3PsiField_cov_bound.{u} N hρ hδ hδ1
  obtain ⟨Cg, hCg, hglob⟩ := hairerI3PsiField_cov_bound_global.{u} N hρ hδ hδ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨Cc * |i3PsiLocalConst B parabolicMomentConst δ| +
    4 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 2 1 δ|, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hL1 : 1 ≤ (t ^ (1 / 4 : ℝ)) ^ (-δ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hYm := measurable_hairerI3PsiField_uncurry N hξ x'
  have hL2 := fun u => hairerI3PsiField_memLp N hρ hε.1 hW hξ x' u
  have hM : ∀ u : SpaceTime, ∫ ω, hairerI3PsiField N ρ ε ξ x' ω u * hairerI3PsiField N ρ ε ξ x' ω u ∂P ≤
      42 * hairerWickConstant N ρ ε ^ 4 * ((2 * ∫ w, |hairerKernelTorus N w|) *
        (2 * ∫ w, |hairerKernelTorus N w|)) := by
    intro u
    obtain ⟨hi, hb⟩ := hairerI3PsiField_pair_integrable_bound N hρ hε.1 hW hξ x' u u
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => hairerI3PsiField N ρ ε ξ x' ω u) hYm
  have hMl := (h.doubleBound_i3PsiLocal hlam hδ hδ1).const_mul hCc
  have hMg := (h.doubleBound_global hlam hlam1 (n := 2) (e := 1) (a := δ) (by norm_num)
    (by norm_num) (by linarith) (by norm_num) (by linarith)).const_mul
    (by positivity : (0 : ℝ) ≤ 4 * Cg)
  have hbound := semigroupDoubleBound_of_majorants (x := x') (Φ := fun u v => ∫ ω,
      hairerI3PsiField N ρ ε ξ x' ω u * hairerI3PsiField N ρ ε ξ x' ω v ∂P) h.measurable hΦ hMl hMg
    (fun u v => mul_nonneg hCc (i3PsiLocalMajorant_nonneg x' δ u v))
    (fun u v => by
      refine mul_nonneg (by positivity) ?_
      unfold semigroupTestGlobalMajorant
      have h1 : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x') ^ a * torusParabolicSize (u - v) ^ b :=
        fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      have h2 : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x') ^ a * torusParabolicSize (u - v) ^ b :=
        fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      have h3 : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x') ^ a * torusParabolicSize (v - x') ^ b :=
        fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      have := h1 2 (-1)
      have := h2 2 (-1)
      have := h1 (2 - δ) 0
      have := h2 (2 - δ) 0
      have := h3 (-δ) 2
      have := h3 2 (-δ)
      have := h1 2 0
      have := h2 2 0
      linarith)
    (by
      filter_upwards [ae_pos_triple x'] with w hw h1 h2
      have hc := hloc hW hε hξ x' w.1 w.2 hw.1 hw.2.1 hw.2.2 h1 h2
      refine hc.trans (le_of_eq ?_)
      simp only [i3PsiLocalMajorant, Real.rpow_zero, mul_one, one_mul]
      ring)
    (by
      filter_upwards [ae_pos_triple x'] with w hw hnb
      have hc := hglob hW hε hξ x' w.1 w.2 hw.1 hw.2.1 hw.2.2
      refine hc.trans ?_
      rw [semigroupTestGlobalMajorant_eq (n := 2) (e := 1) (a := δ) hw.1 hw.2.1]
      set su := torusParabolicSize (w.1 - x') with hsu
      set sv := torusParabolicSize (w.2 - x') with hsv
      set d := torusParabolicSize (w.1 - w.2) with hd
      have hq := rpow_neg_le_rpow_neg_one_add_one hw.2.2 hδ.le (by linarith)
      have hq0 : 0 ≤ d ^ (-(1 : ℝ)) := Real.rpow_nonneg hw.2.2.le _
      have hα : 0 ≤ su ^ (-δ) := Real.rpow_nonneg hw.1.le _
      have hβ : 0 ≤ sv ^ (-δ) := Real.rpow_nonneg hw.2.1.le _
      have hu2 : su ^ (2 : ℝ) = su ^ 2 := Real.rpow_two su
      have hv2 : sv ^ (2 : ℝ) = sv ^ 2 := Real.rpow_two sv
      rw [hu2, hv2]
      have hR : 1 ≤ su ^ 2 + sv ^ 2 := by
        by_contra hlt
        have := not_le.1 hlt
        apply hnb
        constructor <;> nlinarith [sq_nonneg su, sq_nonneg sv]
      have a1 : 1 + su ^ 2 + sv ^ 2 ≤ 2 * (su ^ 2 + sv ^ 2) := by linarith
      have a2 : d ^ (-(1 : ℝ)) + d ^ (-δ) + su ^ (-δ) + sv ^ (-δ) ≤
          2 * (d ^ (-(1 : ℝ)) + su ^ (-δ) + sv ^ (-δ) + 1) := by linarith
      have n1 : 0 ≤ 1 + su ^ 2 + sv ^ 2 := by positivity
      have n2 : 0 ≤ su ^ 2 + sv ^ 2 := by positivity
      have n3 : 0 ≤ d ^ (-(1 : ℝ)) + su ^ (-δ) + sv ^ (-δ) + 1 := by positivity
      have key := mul_le_mul a1 a2 (by linarith [Real.rpow_nonneg hw.2.2.le (-δ)]) (by positivity)
      calc Cg * (1 + su ^ 2 + sv ^ 2) * (d ^ (-(1 : ℝ)) + d ^ (-δ) + su ^ (-δ) + sv ^ (-δ))
          = Cg * ((1 + su ^ 2 + sv ^ 2) * (d ^ (-(1 : ℝ)) + d ^ (-δ) + su ^ (-δ) + sv ^ (-δ))) := by
            ring
        _ ≤ Cg * (2 * (su ^ 2 + sv ^ 2) * (2 * (d ^ (-(1 : ℝ)) + su ^ (-δ) + sv ^ (-δ) + 1))) :=
            mul_le_mul_of_nonneg_left key hCg
        _ = 4 * Cg * ((su ^ 2 + sv ^ 2) * (d ^ (-(1 : ℝ)) + su ^ (-δ) + sv ^ (-δ) + 1)) := by
            ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : Cc * (i3PsiLocalConst B parabolicMomentConst δ * (t ^ (1 / 4 : ℝ)) ^ (-δ)) ≤
      Cc * |i3PsiLocalConst B parabolicMomentConst δ| * (t ^ (1 / 4 : ℝ)) ^ (-δ) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hCc)
      (Real.rpow_nonneg hlam.le _)
  have e2 : 4 * Cg * semigroupTestGlobalConst B parabolicMomentConst 2 1 δ ≤
      4 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 2 1 δ| *
        (t ^ (1 / 4 : ℝ)) ^ (-δ) := by
    have h0 : 0 ≤ 4 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 2 1 δ| := by positivity
    calc 4 * Cg * semigroupTestGlobalConst B parabolicMomentConst 2 1 δ
        ≤ 4 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 2 1 δ| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = 4 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 2 1 δ| * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 h0
  linarith

/-- **The a-priori bound (10.2) for `I(Ψ³)Ψ`, semigroup test** [Hai14, (10.2) for
`τ = I(Ψ³)Ψ`, homogeneity `-4κ`]: `E|∫ I₃Ψ_{proj x} q^♯_t(x, ·)|² ≤ C lam^(2(-4κ) + κ)`
(that is, `lam^(-7κ)`), `lam = t^(1/4)`, uniformly in `ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x`. -/
theorem hairerI3PsiField_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (2 * (-4 * κ) + κ) := by
  have hδ : 0 < min (1 / 4 : ℝ) (7 * κ) := lt_min (by norm_num) (by linarith)
  obtain ⟨C, hC, h⟩ := hairerI3PsiField_semigroupPeriodised_second_moment_le_delta.{u} N hρ hδ
    (min_le_left _ _)
  refine ⟨C, hC, fun {Ω _ P W ε ξ} hW hε hξ {t} ht ht1 x => ?_⟩
  refine (h hW hε hξ ht ht1 x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) ?_
  have := min_le_right (1 / 4 : ℝ) (7 * κ)
  linarith

end RegularityStructures.Phi43

end

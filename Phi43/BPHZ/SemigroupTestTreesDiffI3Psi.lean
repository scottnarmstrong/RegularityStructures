/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3PsiLocal
public import Phi43.BPHZ.SemigroupTestTreesDiffI3PsiCov
public import Phi43.BPHZ.SemigroupTestTreesI3Psi

/-!
# The a-priori bound for the cross-mollifier difference of `I(Ψ³)Ψ` against the semigroup kernel

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise, `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, `t ∈ (0, 1]`, `lam = t^(1/4)` and every `x`,
`E|∫ (I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'})_{proj x} q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(-(2θ + δ))`
(`hairerI3PsiField_sub_semigroupPeriodised_second_moment_le_delta`), and, for `θ ≤ κ ≤ 1/16`, with
the exponent `2 (-4κ) + κ` of the single-model bound
(`hairerI3PsiField_sub_semigroupPeriodised_second_moment_le`).

The covariance of the difference is bounded by the local cross bound
`hairerI3PsiField_sub_cov_bound_cross` when `s(y - x), s(y' - x) ≤ 1` and by the global cross bound
`hairerI3PsiField_sub_cov_bound_cross_global` otherwise; the polynomial growth of the latter is
absorbed by the moments of the profile.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `s^(-e) ≤ s^(-f) + 1` for `0 ≤ e ≤ f`. -/
private theorem rpow_neg_le_rpow_neg_add_one_diff {s e f : ℝ} (hs : 0 < s) (he : 0 ≤ e)
    (hef : e ≤ f) : s ^ (-e) ≤ s ^ (-f) + 1 := by
  rcases le_total s 1 with h | h
  · have : s ^ (-e) ≤ s ^ (-f) := Real.rpow_le_rpow_of_exponent_ge hs h (by linarith)
    have := Real.rpow_nonneg hs.le (-f)
    linarith
  · have : s ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have := Real.rpow_nonneg hs.le (-f)
    linarith

/-- Real algebra for the global region of the difference bound. -/
private theorem diff_global_alg {Cg m su sv Q d₁ d₂ d₃ r r' : ℝ} (hCg : 0 ≤ Cg) (hm : 0 ≤ m)
    (hQ : Q = 1 + su ^ 2 + sv ^ 2) (hnb : 1 ≤ su ^ 2 + sv ^ 2)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h₁ : d₁ ≤ d₂ + 1) (h₃ : d₃ ≤ d₂ + 1) :
    Cg * m * Q ^ 2 * (d₁ + d₂ + d₃ + r + r') ≤
      24 * Cg * m * ((su ^ 4 + sv ^ 4) * (d₂ + r + r' + 1)) := by
  have hQ2 : Q ^ 2 ≤ 8 * (su ^ 4 + sv ^ 4) := by
    have h1 : Q ≤ 2 * (su ^ 2 + sv ^ 2) := by rw [hQ]; linarith
    have h0 : 0 ≤ Q := by rw [hQ]; positivity
    calc Q ^ 2 ≤ (2 * (su ^ 2 + sv ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ 8 * (su ^ 4 + sv ^ 4) := by linarith [sq_nonneg (su ^ 2 - sv ^ 2)]
  have hS : d₁ + d₂ + d₃ + r + r' ≤ 3 * (d₂ + r + r' + 1) := by linarith
  have hS0 : 0 ≤ d₁ + d₂ + d₃ + r + r' := by positivity
  have hP : 0 ≤ su ^ 4 + sv ^ 4 := by positivity
  calc Cg * m * Q ^ 2 * (d₁ + d₂ + d₃ + r + r')
      = (Cg * m) * (Q ^ 2 * (d₁ + d₂ + d₃ + r + r')) := by ring
    _ ≤ (Cg * m) * ((8 * (su ^ 4 + sv ^ 4)) * (3 * (d₂ + r + r' + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hQ2 hS hS0 (by positivity)) (mul_nonneg hCg hm)
    _ = _ := by ring

/-- **Second moment of the cross-mollifier difference of `I(Ψ³)Ψ`, semigroup test, with loss
`2θ + δ`.** -/
theorem hairerI3PsiField_sub_semigroupPeriodised_second_moment_le_delta (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω w -
            hairerI3PsiField N ρ' ε' ξ' (spaceTimeProj x) ω w) *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by
  obtain ⟨Cc, hCc, hloc⟩ := hairerI3PsiField_sub_cov_bound_cross.{u} N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨Cg, hCg, hglob⟩ := hairerI3PsiField_sub_cov_bound_cross_global.{u} N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨Cc * |i3PsiDiffLocalConst B parabolicMomentConst θ δ| +
    24 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)|,
    by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hL1 : 1 ≤ (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hm2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hYm : Measurable fun q : Ω × SpaceTime => hairerI3PsiField N ρ ε ξ x' q.1 q.2 -
      hairerI3PsiField N ρ' ε' ξ' x' q.1 q.2 :=
    (measurable_hairerI3PsiField_uncurry N hξ x').sub (measurable_hairerI3PsiField_uncurry N hξ' x')
  have hL2 : ∀ u, MemLp (fun ω => hairerI3PsiField N ρ ε ξ x' ω u -
      hairerI3PsiField N ρ' ε' ξ' x' ω u) 2 P := fun u =>
    (hairerI3PsiField_memLp N hρ hε.1 hW hξ x' u).sub (hairerI3PsiField_memLp N hρ' hε'.1 hW hξ' x' u)
  set M : ℝ := 2 * (42 * hairerWickConstant N ρ ε ^ 4 * ((2 * ∫ w, |hairerKernelTorus N w|) *
        (2 * ∫ w, |hairerKernelTorus N w|))) +
      2 * (42 * hairerWickConstant N ρ' ε' ^ 4 * ((2 * ∫ w, |hairerKernelTorus N w|) *
        (2 * ∫ w, |hairerKernelTorus N w|))) with hMdef
  have hM : ∀ u : SpaceTime, ∫ ω, (hairerI3PsiField N ρ ε ξ x' ω u -
      hairerI3PsiField N ρ' ε' ξ' x' ω u) * (hairerI3PsiField N ρ ε ξ x' ω u -
      hairerI3PsiField N ρ' ε' ξ' x' ω u) ∂P ≤ M := by
    intro u
    obtain ⟨hi1, hb1⟩ := hairerI3PsiField_pair_integrable_bound N hρ hε.1 hW hξ x' u u
    obtain ⟨hi2, hb2⟩ := hairerI3PsiField_pair_integrable_bound N hρ' hε'.1 hW hξ' x' u u
    have hDint : Integrable (fun ω => (hairerI3PsiField N ρ ε ξ x' ω u -
        hairerI3PsiField N ρ' ε' ξ' x' ω u) * (hairerI3PsiField N ρ ε ξ x' ω u -
        hairerI3PsiField N ρ' ε' ξ' x' ω u)) P := by
      simpa [sq] using (hL2 u).integrable_sq
    have hle : ∀ ω, (hairerI3PsiField N ρ ε ξ x' ω u - hairerI3PsiField N ρ' ε' ξ' x' ω u) *
        (hairerI3PsiField N ρ ε ξ x' ω u - hairerI3PsiField N ρ' ε' ξ' x' ω u) ≤
        2 * (hairerI3PsiField N ρ ε ξ x' ω u * hairerI3PsiField N ρ ε ξ x' ω u) +
          2 * (hairerI3PsiField N ρ' ε' ξ' x' ω u * hairerI3PsiField N ρ' ε' ξ' x' ω u) :=
      fun ω => by
        linarith [sq_nonneg (hairerI3PsiField N ρ ε ξ x' ω u + hairerI3PsiField N ρ' ε' ξ' x' ω u)]
    calc ∫ ω, (hairerI3PsiField N ρ ε ξ x' ω u - hairerI3PsiField N ρ' ε' ξ' x' ω u) *
          (hairerI3PsiField N ρ ε ξ x' ω u - hairerI3PsiField N ρ' ε' ξ' x' ω u) ∂P
        ≤ ∫ ω, (2 * (hairerI3PsiField N ρ ε ξ x' ω u * hairerI3PsiField N ρ ε ξ x' ω u) +
            2 * (hairerI3PsiField N ρ' ε' ξ' x' ω u * hairerI3PsiField N ρ' ε' ξ' x' ω u)) ∂P :=
          integral_mono hDint ((hi1.const_mul 2).add (hi2.const_mul 2)) hle
      _ = 2 * ∫ ω, hairerI3PsiField N ρ ε ξ x' ω u * hairerI3PsiField N ρ ε ξ x' ω u ∂P +
            2 * ∫ ω, hairerI3PsiField N ρ' ε' ξ' x' ω u * hairerI3PsiField N ρ' ε' ξ' x' ω u ∂P := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ M := by
          have c1 := (integral_mono hi1 hi1.abs fun ω => le_abs_self _).trans hb1
          have c2 := (integral_mono hi2 hi2.abs fun ω => le_abs_self _).trans hb2
          rw [hMdef]
          linarith
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => hairerI3PsiField N ρ ε ξ x' ω u - hairerI3PsiField N ρ' ε' ξ' x' ω u) hYm
  have hMl := (h.doubleBound_i3PsiDiffLocal hlam hθ hθ1 hδ1).const_mul
    (mul_nonneg hCc hm2)
  have hMg := (h.doubleBound_global hlam hlam1 (n := 4) (e := 1 + 2 * θ) (a := 2 * θ + δ)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)).const_mul
    (by positivity : (0 : ℝ) ≤ 24 * Cg * (max ε ε') ^ (2 * θ))
  have hbound := semigroupDoubleBound_of_majorants (x := x') (Φ := fun u v => ∫ ω,
      (hairerI3PsiField N ρ ε ξ x' ω u - hairerI3PsiField N ρ' ε' ξ' x' ω u) *
      (hairerI3PsiField N ρ ε ξ x' ω v - hairerI3PsiField N ρ' ε' ξ' x' ω v) ∂P)
    h.measurable hΦ hMl hMg
    (fun u v => mul_nonneg (mul_nonneg hCc hm2) (i3PsiDiffLocalMajorant_nonneg x' θ δ u v))
    (fun u v => mul_nonneg (by positivity) (semigroupTestGlobalMajorant_nonneg x' 4 _ _ u v))
    (by
      filter_upwards [ae_pos_triple x'] with w hw h1 h2
      have hc := hloc hW hε hε' hξ hξ' x' w.1 w.2 hw.1 hw.2.1 hw.2.2 h1 h2
      refine hc.trans (le_of_eq ?_)
      simp only [i3PsiDiffLocalMajorant, Real.rpow_zero, mul_one, one_mul]
      ring)
    (by
      filter_upwards [ae_pos_triple x'] with w hw hnb
      have hc := hglob hW hε hε' hξ hξ' x' w.1 w.2 hw.1 hw.2.1 hw.2.2
      refine hc.trans ?_
      rw [semigroupTestGlobalMajorant_eq (n := 4) (e := 1 + 2 * θ) (a := 2 * θ + δ) hw.1 hw.2.1]
      set su := torusParabolicSize (w.1 - x')
      set sv := torusParabolicSize (w.2 - x')
      set d := torusParabolicSize (w.1 - w.2) with hd
      have h4u : su ^ (4 : ℝ) = su ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h4v : sv ^ (4 : ℝ) = sv ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h4u, h4v]
      have hR : 1 ≤ su ^ 2 + sv ^ 2 := by
        by_contra hlt
        have := not_le.1 hlt
        apply hnb
        constructor <;> nlinarith [sq_nonneg su, sq_nonneg sv]
      have key := diff_global_alg (Cg := Cg) (m := (max ε ε') ^ (2 * θ)) (su := su) (sv := sv)
        (Q := 1 + su ^ 2 + sv ^ 2) (d₁ := d ^ (-(1 : ℝ))) (d₂ := d ^ (-(1 + 2 * θ)))
        (d₃ := d ^ (-(2 * θ + δ))) (r := su ^ (-(2 * θ + δ))) (r' := sv ^ (-(2 * θ + δ))) hCg hm2
        rfl hR (Real.rpow_nonneg hw.2.2.le _) (Real.rpow_nonneg hw.2.2.le _)
        (Real.rpow_nonneg hw.2.2.le _) (Real.rpow_nonneg hw.1.le _) (Real.rpow_nonneg hw.2.1.le _)
        (rpow_neg_le_rpow_neg_add_one_diff hw.2.2 (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : (1 : ℝ) ≤ 1 + 2 * θ))
        (rpow_neg_le_rpow_neg_add_one_diff hw.2.2 (by linarith) (by linarith))
      refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
      · ring
      · ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : Cc * (max ε ε') ^ (2 * θ) * (i3PsiDiffLocalConst B parabolicMomentConst θ δ *
      (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ))) ≤
      Cc * |i3PsiDiffLocalConst B parabolicMomentConst θ δ| * (max ε ε') ^ (2 * θ) *
        (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self (i3PsiDiffLocalConst B parabolicMomentConst θ δ))
      (Real.rpow_nonneg hlam.le (-(2 * θ + δ)))
    linarith [mul_le_mul_of_nonneg_left this (mul_nonneg hCc hm2)]
  have e2 : 24 * Cg * (max ε ε') ^ (2 * θ) *
      semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ) ≤
      24 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)| *
        (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := by
    have h0 : 0 ≤ 24 * Cg * (max ε ε') ^ (2 * θ) *
        |semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)| := by
      positivity
    calc 24 * Cg * (max ε ε') ^ (2 * θ) *
          semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)
        ≤ 24 * Cg * (max ε ε') ^ (2 * θ) *
          |semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = 24 * Cg * (max ε ε') ^ (2 * θ) *
          |semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)| * 1 := by
          ring
      _ ≤ 24 * Cg * (max ε ε') ^ (2 * θ) *
          |semigroupTestGlobalConst B parabolicMomentConst 4 (1 + 2 * θ) (2 * θ + δ)| *
          (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ + δ)) := mul_le_mul_of_nonneg_left hL1 h0
      _ = _ := by ring
  linarith [e1, e2]

/-- **The a-priori bound (10.2) for the cross-mollifier difference of `I(Ψ³)Ψ`, semigroup test**:
`E|∫ (I₃Ψ_{ρ,ε} - I₃Ψ_{ρ',ε'})_{proj x} q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(2(-4κ) + κ)`,
`lam = t^(1/4)`, for `0 < θ ≤ κ ≤ 1/16`, uniformly in `ε, ε' ∈ (0, 1]`, `t ∈ (0, 1]` and `x`. -/
theorem hairerI3PsiField_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {κ θ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 16) (hθ : 0 < θ) (hθκ : θ ≤ κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω w -
            hairerI3PsiField N ρ' ε' ξ' (spaceTimeProj x) ω w) *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (2 * (-4 * κ) + κ) := by
  obtain ⟨C, hC, h⟩ := hairerI3PsiField_sub_semigroupPeriodised_second_moment_le_delta.{u} N hρ hρ'
    (δ := 4 * κ) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨C, hC, fun {Ω _ P W ε ε' ξ ξ'} hW hε hε' hξ hξ' {t} ht ht1 x => ?_⟩
  refine (h hW hε hε' hξ hξ' ht ht1 x).trans ?_
  have hm2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hm2)
  exact Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) (by linarith)

end RegularityStructures.Phi43

end

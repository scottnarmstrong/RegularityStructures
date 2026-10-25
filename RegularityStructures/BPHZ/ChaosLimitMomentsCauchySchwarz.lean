/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Second moment of a weighted random integral

For an integrable weight `k` on `β` with `∫ |k| ≤ L` and a jointly measurable random function
`H ω b` with `E H(b)² ≤ M` for every `b`,
`E (∫ k(b) H(·, b) db)² ≤ L² M`
(`integral_sq_integral_mul_le`). The pointwise Cauchy-Schwarz inequality is
`sq_integral_mul_le_integral_abs_mul_integral`; the expectation is exchanged with the integral by
Fubini.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {β : Type*} [MeasurableSpace β]

/-- Cauchy-Schwarz for a weighted integral: `(∫ k h)² ≤ (∫ |k|) (∫ |k| h²)`. -/
theorem sq_integral_mul_le_integral_abs_mul_integral {ν : Measure β} {k h : β → ℝ}
    (hk : Integrable k ν) (hkh2 : Integrable (fun b => |k b| * h b ^ 2) ν)
    (hhm : AEStronglyMeasurable h ν) :
    (∫ b, k b * h b ∂ν) ^ 2 ≤ (∫ b, |k b| ∂ν) * ∫ b, |k b| * h b ^ 2 ∂ν := by
  set L' := ∫ b, |k b| ∂ν with hL'
  set Q := ∫ b, |k b| * h b ^ 2 ∂ν with hQ
  set J := ∫ b, |k b| * |h b| ∂ν with hJ
  have hkabs : Integrable (fun b => |k b|) ν := hk.abs
  have hkh : Integrable (fun b => |k b| * |h b|) ν := by
    refine Integrable.mono' (hkabs.add hkh2 |>.div_const 2)
      (hkabs.1.mul hhm.norm) (Filter.Eventually.of_forall fun b => ?_)
    simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs, abs_abs]
    have := abs_nonneg (k b)
    nlinarith [sq_nonneg (|h b| - 1), sq_abs (h b), mul_nonneg this (sq_nonneg (|h b| - 1))]
  have hJ0 : 0 ≤ J := integral_nonneg fun b => by positivity
  have hQ0 : 0 ≤ Q := integral_nonneg fun b => by positivity
  have hL0 : 0 ≤ L' := integral_nonneg fun b => abs_nonneg _
  have habs : |∫ b, k b * h b ∂ν| ≤ J := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun b => abs_mul _ _)
  have hJsq : J ^ 2 ≤ L' * Q := by
    rcases hL0.eq_or_lt with h0 | hpos
    · have hk0 : (fun b => |k b|) =ᵐ[ν] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun b => abs_nonneg _) hkabs).1 h0.symm
      have : J = 0 := by
        rw [hJ]
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hk0] with b hb
        simp [hb]
      rw [this, ← h0]
      simp
    · have key : ∀ a c : ℝ, 0 ≤ a ^ 2 * Q - 2 * a * c * J + c ^ 2 * L' := by
        intro a c
        have hnn : 0 ≤ ∫ b, |k b| * (a * |h b| - c) ^ 2 ∂ν :=
          integral_nonneg fun b => by positivity
        have hexp : (∫ b, |k b| * (a * |h b| - c) ^ 2 ∂ν) =
            a ^ 2 * Q - 2 * a * c * J + c ^ 2 * L' := by
          have e : ∀ b, |k b| * (a * |h b| - c) ^ 2 =
              a ^ 2 * (|k b| * h b ^ 2) - 2 * a * c * (|k b| * |h b|) + c ^ 2 * |k b| := by
            intro b
            rw [← sq_abs (h b)]
            ring
          have i1 : Integrable (fun b => a ^ 2 * (|k b| * h b ^ 2)) ν := hkh2.const_mul _
          have i2 : Integrable (fun b => 2 * a * c * (|k b| * |h b|)) ν := hkh.const_mul _
          have i3 : Integrable (fun b => c ^ 2 * |k b|) ν := hkabs.const_mul _
          calc (∫ b, |k b| * (a * |h b| - c) ^ 2 ∂ν)
              = ∫ b, (a ^ 2 * (|k b| * h b ^ 2) - 2 * a * c * (|k b| * |h b|) +
                  c ^ 2 * |k b|) ∂ν := integral_congr_ae (Filter.Eventually.of_forall e)
            _ = (∫ b, a ^ 2 * (|k b| * h b ^ 2) ∂ν) - (∫ b, 2 * a * c * (|k b| * |h b|) ∂ν) +
                  ∫ b, c ^ 2 * |k b| ∂ν := by
              rw [integral_add (f := fun b => a ^ 2 * (|k b| * h b ^ 2) - 2 * a * c * (|k b| * |h b|))
                (g := fun b => c ^ 2 * |k b|) (i1.sub i2) i3, integral_sub i1 i2]
            _ = _ := by rw [integral_const_mul, integral_const_mul, integral_const_mul]
        rw [← hexp]
        exact hnn
      have h1 := key L' J
      nlinarith [h1, hpos]
  calc (∫ b, k b * h b ∂ν) ^ 2 = |∫ b, k b * h b ∂ν| ^ 2 := (sq_abs _).symm
    _ ≤ J ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ L' * Q := hJsq

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Second moment of a weighted random integral.** -/
theorem integral_sq_integral_mul_le {P : Measure Ω} [SFinite P] {ν : Measure β} [SFinite ν]
    {k : β → ℝ} (hkm : Measurable k) (hk : Integrable k ν) {L M : ℝ}
    (hL : ∫ b, |k b| ∂ν ≤ L) (hM0 : 0 ≤ M) {H : Ω → β → ℝ}
    (hH : Measurable (Function.uncurry H))
    (hHb : ∀ ω, Integrable (fun b => |k b| * H ω b ^ 2) ν)
    (hHi : ∀ b, Integrable (fun ω => H ω b ^ 2) P) (hM : ∀ b, ∫ ω, H ω b ^ 2 ∂P ≤ M) :
    Integrable (fun ω => (∫ b, k b * H ω b ∂ν) ^ 2) P ∧
      ∫ ω, (∫ b, k b * H ω b ∂ν) ^ 2 ∂P ≤ L * (L * M) := by
  have hL0 : 0 ≤ L := (integral_nonneg fun b => abs_nonneg (k b)).trans hL
  have hkam : Measurable fun b => |k b| := continuous_abs.measurable.comp hkm
  have hH2 : Measurable (Function.uncurry fun ω b => H ω b ^ 2) := hH.pow_const 2
  have hfm : Measurable (Function.uncurry fun ω b => |k b| * H ω b ^ 2) :=
    (hkam.comp measurable_snd).mul hH2
  have hfint : Integrable (Function.uncurry fun ω b => |k b| * H ω b ^ 2) (P.prod ν) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun b => by exact (hHi b).const_mul |k b|, ?_⟩
    have heq : (fun b => ∫ ω, ‖Function.uncurry (fun ω b => |k b| * H ω b ^ 2) (ω, b)‖ ∂P) =
        fun b => |k b| * ∫ ω, H ω b ^ 2 ∂P := by
      funext b
      have hn : ∀ ω, ‖Function.uncurry (fun ω b => |k b| * H ω b ^ 2) (ω, b)‖ =
          |k b| * H ω b ^ 2 := fun ω => by
        simp only [Function.uncurry_apply_pair]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      simp_rw [hn]
      exact integral_const_mul _ _
    rw [heq]
    refine Integrable.mono' (hk.abs.mul_const M)
      (hkam.mul (hH2.stronglyMeasurable.integral_prod_left (μ := P)).measurable
        ).aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (integral_nonneg fun ω => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hM b) (abs_nonneg _)
  have hQint : Integrable (fun ω => ∫ b, |k b| * H ω b ^ 2 ∂ν) P := hfint.integral_prod_left
  have hswap : ∫ ω, ∫ b, |k b| * H ω b ^ 2 ∂ν ∂P = ∫ b, ∫ ω, |k b| * H ω b ^ 2 ∂P ∂ν :=
    integral_integral_swap hfint
  have hpt : ∀ ω, (∫ b, k b * H ω b ∂ν) ^ 2 ≤ L * ∫ b, |k b| * H ω b ^ 2 ∂ν := fun ω =>
    (sq_integral_mul_le_integral_abs_mul_integral hk (hHb ω)
      (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).trans
      (mul_le_mul_of_nonneg_right hL (integral_nonneg fun b => by positivity))
  have hmeasI : Measurable fun ω => (∫ b, k b * H ω b ∂ν) ^ 2 := by
    have hkH : Measurable (Function.uncurry fun ω b => k b * H ω b) :=
      (hkm.comp measurable_snd).mul hH
    exact (hkH.stronglyMeasurable.integral_prod_right (ν := ν)).measurable.pow_const 2
  refine ⟨Integrable.mono' (hQint.const_mul L) hmeasI.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  calc ∫ ω, (∫ b, k b * H ω b ∂ν) ^ 2 ∂P
      ≤ ∫ ω, L * ∫ b, |k b| * H ω b ^ 2 ∂ν ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (hQint.const_mul L) (Filter.Eventually.of_forall hpt)
    _ = L * ∫ b, |k b| * ∫ ω, H ω b ^ 2 ∂P ∂ν := by
        rw [integral_const_mul, hswap]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
        exact integral_const_mul _ _
    _ ≤ L * (L * M) := by
        refine mul_le_mul_of_nonneg_left ?_ hL0
        calc ∫ b, |k b| * ∫ ω, H ω b ^ 2 ∂P ∂ν ≤ ∫ b, |k b| * M ∂ν :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun b =>
                mul_nonneg (abs_nonneg _) (integral_nonneg fun ω => sq_nonneg _))
                (hk.abs.mul_const M) (Filter.Eventually.of_forall fun b =>
                  mul_le_mul_of_nonneg_left (hM b) (abs_nonneg _))
          _ = (∫ b, |k b| ∂ν) * M := integral_mul_const _ _
          _ ≤ L * M := mul_le_mul_of_nonneg_right hL hM0

end RegularityStructures

end

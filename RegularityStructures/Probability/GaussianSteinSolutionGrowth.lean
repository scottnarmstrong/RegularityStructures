/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianStein
public import RegularityStructures.Probability.GaussianSteinGrowth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Polynomial growth of the explicit Gaussian Stein solution

The centered Gaussian datum has Gaussian tails.  Splitting the primitive at the origin and using
the zero-integral identity turns those tails into a polynomial bound for the Stein solution.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace RegularityStructures

theorem gaussianSteinSolution_polynomial_bound_of_datum {q : ℝ → ℝ}
    (hq : Integrable q (volume : Measure ℝ))
    (hqzero : ∫ x, q x = 0)
    (hqbound : ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ x : ℝ, |q x| ≤ K * (1 + |x|) ^ N * rexp (-x ^ 2 / 2)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      |√(2 * π) * rexp (x ^ 2 / 2) * gaussianSteinPrimitive q x| ≤
        C * (1 + |x|) ^ N := by
  rcases hqbound with ⟨K, N, hK, hqbound⟩
  rcases gaussian_tail_integral_bound_of_polynomial_weight hq
      ⟨K, N, hK, hqbound⟩ with ⟨Dpos, Npos, hDpos, htailpos⟩
  have hqneg : Integrable (fun x : ℝ => q (-x)) (volume : Measure ℝ) := by
    have hneg : Integrable (q ∘ (fun x : ℝ => -x)) (volume : Measure ℝ) ↔
        Integrable q (volume : Measure ℝ) := by
      simpa using ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
        (Homeomorph.neg ℝ).measurableEmbedding :
        Integrable (q ∘ (fun x : ℝ => -x)) (volume : Measure ℝ) ↔
          Integrable q (volume : Measure ℝ))
    exact by simpa [Function.comp_def] using hneg.mpr hq
  have hqnegbound : ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ x : ℝ, |q (-x)| ≤ K * (1 + |x|) ^ N * rexp (-x ^ 2 / 2) := by
    refine ⟨K, N, hK, ?_⟩
    intro x
    simpa using hqbound (-x)
  rcases gaussian_tail_integral_bound_of_polynomial_weight hqneg hqnegbound with
    ⟨Dneg, Nneg, hDneg, htailneg⟩
  have htail_pos : ∀ x : ℝ, 1 ≤ x →
      |∫ t in Ioi x, q t| ≤ Dpos * (1 + x ^ Npos) * rexp (-x ^ 2 / 2) := htailpos
  have htail_neg : ∀ x : ℝ, 1 ≤ x →
      |∫ t in Ioi x, q (-t)| ≤ Dneg * (1 + x ^ Nneg) * rexp (-x ^ 2 / 2) := htailneg
  have hprim_abs : ∀ x : ℝ, 1 ≤ |x| →
      |gaussianSteinPrimitive q x| ≤
        (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) * rexp (-x ^ 2 / 2) := by
    intro x hx
    by_cases hxpos : 0 ≤ x
    · have hx1 : 1 ≤ x := by simpa [abs_of_nonneg hxpos] using hx
      have hpart := intervalIntegral.integral_Iic_add_Ioi
        (μ := (volume : Measure ℝ)) (b := x) hq.integrableOn hq.integrableOn
      have hprim : gaussianSteinPrimitive q x = -∫ t in Ioi x, q t := by
        dsimp [gaussianSteinPrimitive]
        linarith [hpart, hqzero]
      have htail := htail_pos x hx1
      rw [hprim, abs_neg]
      have hNp : x ^ Npos ≤ |x| ^ (max Npos Nneg) := by
        have hpow : x ^ Npos ≤ (1 + x) ^ Npos := by
          exact pow_le_pow_left₀ (by positivity) (by linarith) Npos
        have hmax : Npos ≤ max Npos Nneg := Nat.le_max_left _ _
        have hbase : 1 ≤ |x| := by simpa [abs_of_nonneg hxpos] using hx1
        simpa [abs_of_nonneg hxpos] using
          (pow_le_pow_right₀ hbase hmax)
      have hD : Dpos * (1 + x ^ Npos) ≤
          (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) := by
        calc
          Dpos * (1 + x ^ Npos) ≤ Dpos * (1 + |x| ^ (max Npos Nneg)) := by
            have hsum : 1 + x ^ Npos ≤ 1 + |x| ^ (max Npos Nneg) := by linarith
            exact mul_le_mul_of_nonneg_left hsum hDpos
          _ ≤ (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) := by
            exact mul_le_mul_of_nonneg_right (by linarith)
              (by positivity)
      calc
        |∫ t in Ioi x, q t| ≤ Dpos * (1 + x ^ Npos) * rexp (-x ^ 2 / 2) := htail
        _ ≤ (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) * rexp (-x ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
    · have hxneg : x ≤ 0 := le_of_not_ge hxpos
      have hx1 : 1 ≤ -x := by
        have : |x| = -x := abs_of_nonpos hxneg
        simpa [this] using hx
      have hprim : gaussianSteinPrimitive q x =
          ∫ t in Ioi (-x), q (-t) := by
        dsimp [gaussianSteinPrimitive]
        symm
        simp [neg_neg] at *
      have htail := htail_neg (-x) hx1
      rw [hprim]
      have hNle : (-x) ^ Nneg ≤ |x| ^ (max Npos Nneg) := by
        have hmax : Nneg ≤ max Npos Nneg := Nat.le_max_right _ _
        have hpow : (-x) ^ Nneg ≤ |x| ^ (max Npos Nneg) := by
          rw [abs_of_nonpos hxneg]
          exact pow_le_pow_right₀ hx1 hmax
        exact hpow
      have hD : Dneg * (1 + (-x) ^ Nneg) ≤
          (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) := by
        have hbase : 0 ≤ 1 + |x| ^ (max Npos Nneg) := by positivity
        have hone : 1 ≤ 1 + |x| ^ (max Npos Nneg) := by
          exact le_add_of_nonneg_right (pow_nonneg (abs_nonneg x) _)
        calc
          Dneg * (1 + (-x) ^ Nneg) ≤ Dneg * (1 + |x| ^ (max Npos Nneg)) := by
            have hsum : 1 + (-x) ^ Nneg ≤ 1 + |x| ^ (max Npos Nneg) := by
              linarith [hNle]
            exact mul_le_mul_of_nonneg_left hsum hDneg
          _ ≤ (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) := by
            exact mul_le_mul_of_nonneg_right (by linarith)
              (by positivity)
      calc
        |∫ t in Ioi (-x), q (-t)| ≤ Dneg * (1 + (-x) ^ Nneg) * rexp (-(-x) ^ 2 / 2) := htail
        _ ≤ (Dpos + Dneg) * (1 + |x| ^ (max Npos Nneg)) * rexp (-x ^ 2 / 2) := by
          have heq : -(-x) ^ 2 / 2 = -x ^ 2 / 2 := by ring
          rw [heq]
          exact mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
  let B : ℝ := ∫ x, |q x|
  have hBint : Integrable (fun x : ℝ => |q x|) (volume : Measure ℝ) := hq.norm
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun x => abs_nonneg (q x))
  have hprim_compact : ∀ x : ℝ, |x| ≤ 1 → |gaussianSteinPrimitive q x| ≤ B := by
    intro x hx
    calc
      |gaussianSteinPrimitive q x| ≤ ∫ t in Iic x, |q t| := by
        dsimp [gaussianSteinPrimitive]
        exact norm_integral_le_integral_norm q
      _ ≤ ∫ t, |q t| := by
        exact setIntegral_le_integral hBint (ae_of_all _ fun t => abs_nonneg (q t))
      _ = B := rfl
  have hsqrt : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have hA : 0 ≤ √(2 * π) * rexp (1 / 2) * B := by positivity
  let M : ℕ := max Npos Nneg
  let A : ℝ := √(2 * π) * rexp (1 / 2) * B +
    2 * √(2 * π) * (Dpos + Dneg)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, M, hA_nonneg, ?_⟩
  intro x
  by_cases htailx : 1 ≤ |x|
  · have hprim := hprim_abs x htailx
    have hfac : 0 ≤ √(2 * π) * rexp (x ^ 2 / 2) :=
      mul_nonneg hsqrt (Real.exp_pos _).le
    calc
      |√(2 * π) * rexp (x ^ 2 / 2) * gaussianSteinPrimitive q x| =
          √(2 * π) * rexp (x ^ 2 / 2) *
            |gaussianSteinPrimitive q x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hsqrt, abs_of_pos (Real.exp_pos _)]
      _ ≤ √(2 * π) * rexp (x ^ 2 / 2) *
          ((Dpos + Dneg) * (1 + |x| ^ M) * rexp (-x ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left hprim hfac
      _ = √(2 * π) * (Dpos + Dneg) * (1 + |x| ^ M) := by
        dsimp [M]
        rw [show √(2 * π) * rexp (x ^ 2 / 2) *
            ((Dpos + Dneg) * (1 + |x| ^ M) * rexp (-x ^ 2 / 2)) =
            √(2 * π) * (Dpos + Dneg) * (1 + |x| ^ M) *
              (rexp (x ^ 2 / 2) * rexp (-x ^ 2 / 2)) by ring]
        rw [← Real.exp_add]
        have : x ^ 2 / 2 + -x ^ 2 / 2 = 0 := by ring
        rw [this, Real.exp_zero]
        ring
      _ ≤ A * (1 + |x|) ^ M := by
        have hone : 1 ≤ (1 + |x|) ^ M := by
          exact one_le_pow₀ (by linarith [abs_nonneg x])
        have hpow : |x| ^ M ≤ (1 + |x|) ^ M := by
          exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) M
        dsimp [A]
        have hcoef : 0 ≤ √(2 * π) * (Dpos + Dneg) := by positivity
        calc
          √(2 * π) * (Dpos + Dneg) * (1 + |x| ^ M) ≤
              √(2 * π) * (Dpos + Dneg) * (2 * (1 + |x|) ^ M) := by
                have hsum : 1 + |x| ^ M ≤ 2 * (1 + |x|) ^ M := by
                  linarith
                exact mul_le_mul_of_nonneg_left hsum hcoef
          _ = 2 * (√(2 * π) * (Dpos + Dneg)) * (1 + |x|) ^ M := by ring
          _ ≤ (√(2 * π) * rexp (1 / 2) * B +
              2 * √(2 * π) * (Dpos + Dneg)) * (1 + |x|) ^ M := by
            have hcoef' : 2 * √(2 * π) * (Dpos + Dneg) ≤
                √(2 * π) * rexp (1 / 2) * B +
                  2 * √(2 * π) * (Dpos + Dneg) := by
              linarith [hA]
            have hS : 0 ≤ (1 + |x|) ^ M :=
              pow_nonneg (add_nonneg (by norm_num) (abs_nonneg x)) M
            have hcoef'' : 2 * (√(2 * π) * (Dpos + Dneg)) ≤
                √(2 * π) * rexp (1 / 2) * B +
                  2 * √(2 * π) * (Dpos + Dneg) := by
              simpa only [mul_assoc] using hcoef'
            exact mul_le_mul_of_nonneg_right hcoef'' hS
  · have hx : |x| ≤ 1 := by linarith
    have hprim := hprim_compact x hx
    have hxsq : x ^ 2 / 2 ≤ 1 / 2 := by
      have hsq : x ^ 2 ≤ 1 := by
        calc
          x ^ 2 = |x| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
          _ = 1 := by norm_num
      linarith
    have hexp : rexp (x ^ 2 / 2) ≤ rexp (1 / 2) := Real.exp_le_exp.mpr hxsq
    have hbound : |√(2 * π) * rexp (x ^ 2 / 2) *
        gaussianSteinPrimitive q x| ≤ √(2 * π) * rexp (1 / 2) * B := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsqrt, abs_of_pos (Real.exp_pos _)]
      have hleft : √(2 * π) * rexp (x ^ 2 / 2) *
          |gaussianSteinPrimitive q x| ≤
          √(2 * π) * rexp (x ^ 2 / 2) * B :=
        mul_le_mul_of_nonneg_left hprim
          (mul_nonneg hsqrt (Real.exp_pos (x ^ 2 / 2)).le)
      have hright : √(2 * π) * rexp (x ^ 2 / 2) * B ≤
          √(2 * π) * rexp (1 / 2) * B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp hsqrt) hB
      exact hleft.trans hright
    calc
      |√(2 * π) * rexp (x ^ 2 / 2) * gaussianSteinPrimitive q x| ≤
          √(2 * π) * rexp (1 / 2) * B := hbound
      _ ≤ A * (1 + |x|) ^ M := by
        have hone : 1 ≤ (1 + |x|) ^ M := by
          exact one_le_pow₀ (by linarith [abs_nonneg x])
        dsimp [A]
        have hbase : 0 ≤ √(2 * π) * rexp (1 / 2) * B := hA
        have hfirst : √(2 * π) * rexp (1 / 2) * B ≤
            √(2 * π) * rexp (1 / 2) * B * (1 + |x|) ^ M := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hbase
        have hsecond : √(2 * π) * rexp (1 / 2) * B * (1 + |x|) ^ M ≤
            (√(2 * π) * rexp (1 / 2) * B +
              2 * √(2 * π) * (Dpos + Dneg)) * (1 + |x|) ^ M := by
          have htailcoef : 0 ≤ 2 * √(2 * π) * (Dpos + Dneg) := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith [htailcoef])
            (by positivity)
        exact hfirst.trans hsecond

end RegularityStructures

end

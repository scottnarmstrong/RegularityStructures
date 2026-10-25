/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.MomentBump

/-!
# Causal bumps with prescribed polynomial moments

As `exists_moment_bump`, but the bump is supported in `{t > 0} ∩ {parabolicNorm ≤ 1}`:
the Gram-matrix construction is run with a nonnegative bump `χ` supported in a small ball around
`(1/4, 0)`, and the resulting `ψ = (∑ aⱼ z^j) χ` vanishes wherever `χ` does
(`exists_moment_bump_of_bump`, `exists_moment_bump_causal`).

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5 and Section 7 (non-anticipative kernels).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A smooth bump centred at `(1/4, 0)`, supported in the sup-norm ball of radius `1/8`. -/
def causalBump : ContDiffBump ((1 / 4 : ℝ), (0 : Fin 3 → ℝ)) where
  rIn := 1 / 16
  rOut := 1 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end RegularityStructures

end

public section

open MeasureTheory Matrix
open scoped ContDiff

namespace RegularityStructures

theorem causalBump_pos_time {z : ParabolicSpace} (hz : causalBump z ≠ 0) : 1 / 8 < z.1 := by
  have h : dist z ((1 / 4 : ℝ), (0 : Fin 3 → ℝ)) < 1 / 8 := by
    by_contra hc
    exact hz (causalBump.zero_of_le_dist (not_lt.1 hc))
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at h
  simp only at h
  linarith [h.1.1]

theorem causalBump_parabolicNorm_le {z : ParabolicSpace} (hz : causalBump z ≠ 0) :
    parabolicNorm z ≤ 1 := by
  have h : dist z ((1 / 4 : ℝ), (0 : Fin 3 → ℝ)) < 1 / 8 := by
    by_contra hc
    exact hz (causalBump.zero_of_le_dist (not_lt.1 hc))
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only at h1 h2 h3
  rw [dist_pi_lt_iff (by norm_num)] at h3
  have hs : Real.sqrt |z.1| < 5 / 8 := by
    rw [Real.sqrt_lt' (by norm_num), abs_of_pos (by linarith)]
    linarith
  have hc : ∀ i, |z.2 i| < 1 / 8 := fun i => by simpa using h3 i
  have : ∑ i, |z.2 i| ≤ ∑ _i : Fin 3, (1 / 8 : ℝ) :=
    Finset.sum_le_sum fun i _ => (hc i).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  unfold parabolicNorm
  norm_num at this
  linarith

/-- A smooth function with prescribed moments `∫ z^k ψ = c k` (for `|k|_𝔰 < N`) that vanishes
wherever the nonnegative bump `χ` does, for any smooth `χ ≥ 0` supported in the unit parabolic
ball and positive on a nonempty open set. -/
theorem exists_moment_bump_of_bump {χ : ParabolicSpace → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hnn : ∀ z, 0 ≤ χ z) (hsupp : ∀ z, 1 < parabolicNorm z → χ z = 0)
    (hpos : ∃ U : Set ParabolicSpace, IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, 0 < χ z)
    (N : ℕ) (c : PolyIndex N → ℝ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, χ z = 0 → ψ z = 0) ∧
      ∀ k : PolyIndex N, ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = c k := by
  have hU : IsUnit (momentGram N χ).det := isUnit_det_momentGram hχ hnn hsupp hpos
  set a : PolyIndex N → ℝ := (momentGram N χ)⁻¹ *ᵥ c with ha
  have hGa : momentGram N χ *ᵥ a = c := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  refine ⟨fun z => (∑ j, a j * momentMono j.1 z) * χ z, ?_, ?_, fun k => ?_⟩
  · refine (ContDiff.sum fun j _ => ?_).mul hχ
    exact contDiff_const.mul (contDiff_momentMono j.1)
  · intro z hz
    simp [hz]
  · have hint : ∀ j : PolyIndex N,
        Integrable fun z => a j * (momentMono k.1 z * momentMono j.1 z * χ z) :=
      fun j => (integrable_momentMono_mul_mul hχ hsupp k.1 j.1).const_mul (a j)
    have : ∀ z, evalParabolic (MvPolynomial.monomial k.1 1) z *
        ((∑ j, a j * momentMono j.1 z) * χ z) =
        ∑ j, a j * (momentMono k.1 z * momentMono j.1 z * χ z) := fun z => by
      change momentMono k.1 z * _ = _
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [this]
    rw [integral_finsetSum _ fun j _ => hint j, ← congrFun hGa k]
    simp only [Matrix.mulVec, dotProduct, momentGram]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]; ring

/-- A smooth function supported in the unit parabolic ball and in `{t > 0}` whose moments
`∫ z^k ψ`, for `|k|_𝔰 < N`, are prescribed to be `c k`. -/
theorem exists_moment_bump_causal (N : ℕ) (c : PolyIndex N → ℝ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, 1 < parabolicNorm z → ψ z = 0) ∧
      (∀ z, z.1 ≤ 0 → ψ z = 0) ∧
      ∀ k : PolyIndex N, ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = c k := by
  have hχ : ContDiff ℝ ∞ (causalBump : ParabolicSpace → ℝ) := causalBump.contDiff
  obtain ⟨ψ, hψ, hψ0, hψm⟩ := exists_moment_bump_of_bump hχ (fun z => causalBump.nonneg)
    (fun z hz => by
      by_contra h
      exact absurd (causalBump_parabolicNorm_le h) (not_le.2 hz))
    ⟨Metric.ball ((1 / 4 : ℝ), (0 : Fin 3 → ℝ)) (1 / 8), Metric.isOpen_ball,
      ⟨_, Metric.mem_ball_self (by norm_num)⟩, fun z hz => causalBump.pos_of_mem_ball hz⟩ N c
  refine ⟨ψ, hψ, fun z hz => hψ0 z ?_, fun z hz => hψ0 z ?_, hψm⟩
  · by_contra h
    exact absurd (causalBump_parabolicNorm_le h) (not_le.2 hz)
  · by_contra h
    linarith [causalBump_pos_time h]

end RegularityStructures

end

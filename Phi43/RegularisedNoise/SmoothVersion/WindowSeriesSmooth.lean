/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientFormula
public import Phi43.RegularisedNoise.SmoothVersion.Series
public import Phi43.RegularisedNoise.SmoothVersion.WeightedSummability

/-!
# Smoothness of a polynomially controlled window Fourier series

This is the deterministic/samplewise part of the finite-window construction.  A polynomial bound on
the real white-noise coefficients is absorbed by taking sufficiently many powers in the coefficient
decay estimate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

namespace RegularityStructures.Phi43

def smoothVersionWindowSeriesTerm (Phi : SpaceTime → ℝ) (a b : ℝ)
    (i : Sum WindowFrequency WindowFrequency) (z : SpaceTime) : ℝ :=
  match i with
  | Sum.inl k => (smoothVersionWindowCoefficientFormula Phi a b k z).re
  | Sum.inr k => -(smoothVersionWindowCoefficientFormula Phi a b k z).im

theorem isSmoothOnSpaceTime_smoothVersionWindowSeriesTerm
    (Phi : SpaceTime → ℝ) (a b : ℝ) (i : Sum WindowFrequency WindowFrequency) :
    IsSmoothOnSpaceTime (smoothVersionWindowSeriesTerm Phi a b i) := by
  cases i with
  | inl k =>
      exact isSmoothOnSpaceTime_smoothVersionWindowCoefficientFormula_re Phi a b k
  | inr k =>
      exact (isSmoothOnSpaceTime_smoothVersionWindowCoefficientFormula_im Phi a b k).neg

theorem isSmoothOnSpaceTime_tsum_smoothVersionWindowSeries_of_polynomial_growth
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) (hN : 0 < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1)
    (hL : 1 ≤ b - a) {X : Sum WindowFrequency WindowFrequency → ℝ}
    {p : ℕ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hX : ∀ i, |X i| ≤ C₀ * smoothVersionFrequencyNormSq (match i with
      | Sum.inl k => k
      | Sum.inr k => k) ^ p) :
    IsSmoothOnSpaceTime (fun z =>
      ∑' i, X i * smoothVersionWindowSeriesTerm Phi a b i z) := by
  have hbase : ∀ q : ℕ, Summable (fun k : WindowFrequency =>
      smoothVersionFrequencyNormSq k ^ (q + p) *
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖) := by
    intro q
    obtain ⟨Cq, hCq, hdecay⟩ := smoothVersion_windowCoefficientAmplitude_decay
      hPhi hR hR0 hN a b ha hb (6 + 2 * (q + p))
    exact summable_smoothVersion_fourier_weighted_of_coordinate_decay (q + p)
      ⟨‖smoothVersionWindowCoefficientAmplitude Phi a b 0‖,
        norm_nonneg _, le_rfl⟩
      ⟨Cq, hCq, fun i k hki => hdecay i k hki⟩
  let v : ℕ → Sum WindowFrequency WindowFrequency → ℝ := fun q i =>
    C₀ * (q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q *
      smoothVersionFrequencyNormSq (match i with
        | Sum.inl k => k
        | Sum.inr k => k) ^ (q + p) *
      ‖smoothVersionWindowCoefficientAmplitude Phi a b (match i with
        | Sum.inl k => k
        | Sum.inr k => k)‖
  have hv : ∀ q, Summable (v q) := by
    intro q
    exact Summable.sum (v q)
      ((hbase q).mul_left (C₀ * (q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q) |>.congr
        (by
          intro k
          simp [v]
          ring))
      ((hbase q).mul_left (C₀ * (q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q) |>.congr
        (by
          intro k
          simp [v]
          ring))
  apply isSmoothOnSpaceTime_tsum_of_derivative_bounds
  · intro i
    exact contDiff_const.mul (isSmoothOnSpaceTime_smoothVersionWindowSeriesTerm Phi a b i)
  · exact hv
  · intro q i r
    cases i with
    | inl k =>
        have hterm := norm_iteratedFDeriv_smoothVersionWindowCoefficientFormula_re_le
          Phi a b k q hL r
        let fR : (ℝ × (Fin 3 → ℝ)) → ℝ := fun s =>
          smoothVersionWindowSeriesTerm Phi a b (Sum.inl k) (s.1, torusProj s.2)
        have hfR : ContDiff ℝ ∞ fR := by
          have hR' := isSmoothOnSpaceTime_smoothVersionWindowCoefficientFormula_re Phi a b k
          unfold IsSmoothOnSpaceTime at hR'
          simpa [fR, smoothVersionWindowSeriesTerm] using hR'
        have hscalar : ContDiffAt ℝ (q : ℕ∞ω) fR r :=
          (hfR.contDiffAt (x := r)).of_le (by exact_mod_cast le_top)
        rw [show (fun s : ℝ × (Fin 3 → ℝ) =>
            X (Sum.inl k) *
              smoothVersionWindowSeriesTerm Phi a b (Sum.inl k)
                (s.1, torusProj s.2)) =
            (fun s => X (Sum.inl k) •
              smoothVersionWindowSeriesTerm Phi a b (Sum.inl k)
                (s.1, torusProj s.2)) by
          funext s
          simp [smul_eq_mul, smoothVersionWindowSeriesTerm]]
        rw [iteratedFDeriv_const_smul_apply' hscalar, norm_smul]
        calc
          |X (Sum.inl k)| *
              ‖iteratedFDeriv ℝ q
                (fun s : ℝ × (Fin 3 → ℝ) =>
                  smoothVersionWindowSeriesTerm Phi a b (Sum.inl k)
                    (s.1, torusProj s.2)) r‖ ≤
              (C₀ * smoothVersionFrequencyNormSq k ^ p) *
                (‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
                  (q.factorial : ℝ) * 2 *
                    (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q) := by
                    have hSk : 0 ≤ smoothVersionFrequencyNormSq k := by
                      dsimp [smoothVersionFrequencyNormSq]
                      positivity
                    exact mul_le_mul (hX (Sum.inl k)) hterm (norm_nonneg _)
                      (mul_nonneg hC₀ (pow_nonneg hSk _))
          _ = v q (Sum.inl k) := by
            simp [v]
            ring_nf
    | inr k =>
        have hterm := norm_iteratedFDeriv_smoothVersionWindowCoefficientFormula_im_le
          Phi a b k q hL r
        let fI : (ℝ × (Fin 3 → ℝ)) → ℝ := fun s =>
          smoothVersionWindowSeriesTerm Phi a b (Sum.inr k) (s.1, torusProj s.2)
        have hfI : ContDiff ℝ ∞ fI := by
          have hI' := isSmoothOnSpaceTime_smoothVersionWindowCoefficientFormula_im Phi a b k
          unfold IsSmoothOnSpaceTime at hI'
          simpa [fI, smoothVersionWindowSeriesTerm] using hI'.neg
        have hscalar : ContDiffAt ℝ (q : ℕ∞ω) fI r :=
          (hfI.contDiffAt (x := r)).of_le (by exact_mod_cast le_top)
        rw [show (fun s : ℝ × (Fin 3 → ℝ) =>
            X (Sum.inr k) *
              smoothVersionWindowSeriesTerm Phi a b (Sum.inr k)
                (s.1, torusProj s.2)) =
            (fun s => X (Sum.inr k) •
              smoothVersionWindowSeriesTerm Phi a b (Sum.inr k)
                (s.1, torusProj s.2)) by
          funext s
          simp [smul_eq_mul, smoothVersionWindowSeriesTerm]]
        rw [iteratedFDeriv_const_smul_apply' hscalar, norm_smul]
        calc
          |X (Sum.inr k)| *
              ‖iteratedFDeriv ℝ q
                (fun s : ℝ × (Fin 3 → ℝ) =>
                  smoothVersionWindowSeriesTerm Phi a b (Sum.inr k)
                    (s.1, torusProj s.2)) r‖ ≤
              (C₀ * smoothVersionFrequencyNormSq k ^ p) *
                (‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
                  (q.factorial : ℝ) * 2 *
                    (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q) := by
                    have hterm' : ‖iteratedFDeriv ℝ q
                        (fun s : ℝ × (Fin 3 → ℝ) =>
                          smoothVersionWindowSeriesTerm Phi a b (Sum.inr k)
                            (s.1, torusProj s.2)) r‖ ≤
                        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
                          (q.factorial : ℝ) * 2 *
                            (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q := by
                      unfold smoothVersionWindowSeriesTerm
                      change ‖iteratedFDeriv ℝ q
                        (-(fun s : ℝ × (Fin 3 → ℝ) =>
                          (smoothVersionWindowCoefficientFormula Phi a b k
                            (s.1, torusProj s.2)).im)) r‖ ≤ _
                      rw [iteratedFDeriv_neg_apply, norm_neg]
                      exact hterm
                    have hSk : 0 ≤ smoothVersionFrequencyNormSq k := by
                      dsimp [smoothVersionFrequencyNormSq]
                      positivity
                    exact mul_le_mul (hX (Sum.inr k)) hterm' (norm_nonneg _)
                      (mul_nonneg hC₀ (pow_nonneg hSk _))
          _ = v q (Sum.inr k) := by
            simp [v]
            ring_nf

end RegularityStructures.Phi43

end

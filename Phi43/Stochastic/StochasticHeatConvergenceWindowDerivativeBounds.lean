/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowSeriesSmooth
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Quantitative derivative bounds for the fixed-window noise series

The same summable Fourier majorants that prove smoothness also bound the
derivatives of the sum. The coefficient-growth constant factors out exactly,
so it can subsequently carry the polynomial integer-time weight from
Borel--Cantelli. This is deterministic infrastructure for
the convergence of the noise potentials (`phi43Noise_cauchy`) [Hai14, Proposition 9.5].
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

def stochasticHeatWindowDerivativeMajorant (Phi : SpaceTime → ℝ) (a b : ℝ)
    (q : ℕ) (i : Sum WindowFrequency WindowFrequency) : ℝ :=
  (q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q *
    smoothVersionFrequencyNormSq (i.elim id id) ^ (q + 3) *
      ‖smoothVersionWindowCoefficientAmplitude Phi a b (i.elim id id)‖

theorem stochasticHeatWindowDerivativeMajorant_nonneg (Phi : SpaceTime → ℝ) (a b : ℝ)
    (q : ℕ) (i : Sum WindowFrequency WindowFrequency) :
    0 ≤ stochasticHeatWindowDerivativeMajorant Phi a b q i := by
  unfold stochasticHeatWindowDerivativeMajorant smoothVersionFrequencyNormSq
  positivity

theorem summable_stochasticHeatWindowDerivativeMajorant
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi) {R N : ℝ}
    (hR : ∀ z : SpaceTime, R < |z.1| → Phi z = 0) (hR0 : 0 ≤ R) (hN : 0 < N)
    {a b : ℝ} (ha : a = -N - R - 1) (hb : b = N + R + 1) (q : ℕ) :
    Summable (stochasticHeatWindowDerivativeMajorant Phi a b q) := by
  obtain ⟨C, hC, hdecay⟩ := smoothVersion_windowCoefficientAmplitude_decay
    hPhi hR hR0 hN a b ha hb (6 + 2 * (q + 3))
  have hs := summable_smoothVersion_fourier_weighted_of_coordinate_decay (q + 3)
    ⟨‖smoothVersionWindowCoefficientAmplitude Phi a b 0‖, norm_nonneg _, le_rfl⟩
    ⟨C, hC, hdecay⟩
  have hf := hs.mul_left ((q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q)
  refine Summable.sum _ ?_ ?_
  · apply hf.congr
    intro k
    change _ = (q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q *
      smoothVersionFrequencyNormSq k ^ (q + 3) *
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖
    ring
  · apply hf.congr
    intro k
    change _ = (q.factorial : ℝ) * 2 * (8 * Real.pi) ^ q *
      smoothVersionFrequencyNormSq k ^ (q + 3) *
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖
    ring

private theorem windowSeriesTerm_derivative_le (Phi : SpaceTime → ℝ) (a b : ℝ)
    (hL : 1 ≤ b - a) (q : ℕ) (i : Sum WindowFrequency WindowFrequency)
    (z : ℝ × (Fin 3 → ℝ)) :
    ‖iteratedFDeriv ℝ q (fun w => smoothVersionWindowSeriesTerm Phi a b i
      (w.1, torusProj w.2)) z‖ ≤
      ‖smoothVersionWindowCoefficientAmplitude Phi a b (i.elim id id)‖ *
        (q.factorial : ℝ) * 2 * (8 * Real.pi * smoothVersionFrequencyNormSq (i.elim id id)) ^ q := by
  cases i with
  | inl k => exact norm_iteratedFDeriv_smoothVersionWindowCoefficientFormula_re_le Phi a b k q hL z
  | inr k =>
    change ‖iteratedFDeriv ℝ q (-(fun w : ℝ × (Fin 3 → ℝ) =>
      (smoothVersionWindowCoefficientFormula Phi a b k (w.1, torusProj w.2)).im)) z‖ ≤ _
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact norm_iteratedFDeriv_smoothVersionWindowCoefficientFormula_im_le Phi a b k q hL z

open scoped ContDiff in
private theorem windowWeightedSeriesTerm_derivative_le (Phi : SpaceTime → ℝ) (a b : ℝ)
    (hL : 1 ≤ b - a) {X : Sum WindowFrequency WindowFrequency → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hX : ∀ i, |X i| ≤ C * smoothVersionFrequencyNormSq (i.elim id id) ^ 3)
    (q : ℕ) (i : Sum WindowFrequency WindowFrequency) (z : ℝ × (Fin 3 → ℝ)) :
    ‖iteratedFDeriv ℝ q (fun w => X i * smoothVersionWindowSeriesTerm Phi a b i
      (w.1, torusProj w.2)) z‖ ≤ C * stochasticHeatWindowDerivativeMajorant Phi a b q i := by
  have hsm := isSmoothOnSpaceTime_smoothVersionWindowSeriesTerm Phi a b i
  unfold IsSmoothOnSpaceTime at hsm
  have hsmq := (hsm.contDiffAt (x := z)).of_le
    (by exact_mod_cast le_top : (q : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ q (fun w => X i • smoothVersionWindowSeriesTerm Phi a b i
    (w.1, torusProj w.2)) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hsmq, norm_smul, Real.norm_eq_abs]
  apply (mul_le_mul (hX i) (windowSeriesTerm_derivative_le Phi a b hL q i z)
    (norm_nonneg _) (mul_nonneg hC (by unfold smoothVersionFrequencyNormSq; positivity))).trans_eq
  unfold stochasticHeatWindowDerivativeMajorant
  rw [mul_pow, pow_add]
  ring

theorem summable_stochasticHeatWindowSeries
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi) {R N : ℝ}
    (hR : ∀ z : SpaceTime, R < |z.1| → Phi z = 0) (hR0 : 0 ≤ R) (hN : 0 < N)
    {a b : ℝ} (ha : a = -N - R - 1) (hb : b = N + R + 1) (hL : 1 ≤ b - a)
    {X : Sum WindowFrequency WindowFrequency → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hX : ∀ i, |X i| ≤ C * smoothVersionFrequencyNormSq (i.elim id id) ^ 3)
    (z : SpaceTime) :
    Summable (fun i => X i * smoothVersionWindowSeriesTerm Phi a b i z) := by
  have hrep : torusProj (torusRep z.2) = z.2 := by
    funext i
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := z.2 i)
  apply ((summable_stochasticHeatWindowDerivativeMajorant hPhi hR hR0 hN ha hb 0).mul_left C).of_norm_bounded
  intro i
  have h := windowWeightedSeriesTerm_derivative_le Phi a b hL hC hX 0 i (z.1, torusRep z.2)
  simpa only [norm_iteratedFDeriv_zero, hrep] using h

open scoped ContDiff in
theorem norm_iteratedFDeriv_smoothVersion_windowSeries_le
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi) {R N : ℝ}
    (hR : ∀ z : SpaceTime, R < |z.1| → Phi z = 0) (hR0 : 0 ≤ R) (hN : 0 < N)
    {a b : ℝ} (ha : a = -N - R - 1) (hb : b = N + R + 1) (hL : 1 ≤ b - a)
    {X : Sum WindowFrequency WindowFrequency → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hX : ∀ i, |X i| ≤ C * smoothVersionFrequencyNormSq (i.elim id id) ^ 3)
    (q : ℕ) (z : ℝ × (Fin 3 → ℝ)) :
    ‖iteratedFDeriv ℝ q (fun w => ∑' i, X i * smoothVersionWindowSeriesTerm Phi a b i
      (w.1, torusProj w.2)) z‖ ≤
        C * ∑' i, stochasticHeatWindowDerivativeMajorant Phi a b q i := by
  let f := fun (i : Sum WindowFrequency WindowFrequency) (w : ℝ × (Fin 3 → ℝ)) =>
    X i * smoothVersionWindowSeriesTerm Phi a b i (w.1, torusProj w.2)
  have hf : ∀ i, ContDiff ℝ ∞ (f i) := fun i =>
    contDiff_const.mul (isSmoothOnSpaceTime_smoothVersionWindowSeriesTerm Phi a b i)
  have hs (k : ℕ) := (summable_stochasticHeatWindowDerivativeMajorant hPhi hR hR0 hN ha hb k).mul_left C
  have hbound (k : ℕ) (i : Sum WindowFrequency WindowFrequency) (w : ℝ × (Fin 3 → ℝ)) :=
    windowWeightedSeriesTerm_derivative_le Phi a b hL hC hX k i w
  have heq := iteratedFDeriv_tsum_apply (N := ⊤) hf (fun k _ => hs k)
    (fun k i w _ => hbound k i w) (show (q : ℕ∞) ≤ ⊤ from le_top) z
  change ‖iteratedFDeriv ℝ q (fun w => ∑' i, f i w) z‖ ≤ _
  rw [heq]
  have hnorm : Summable (fun i => ‖iteratedFDeriv ℝ q (f i) z‖) :=
    (hs q).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbound q i z)
  calc
    _ ≤ ∑' i, ‖iteratedFDeriv ℝ q (f i) z‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, C * stochasticHeatWindowDerivativeMajorant Phi a b q i :=
      hnorm.tsum_le_tsum (fun i => hbound q i z) (hs q)
    _ = _ := tsum_mul_left

end RegularityStructures.Phi43

end

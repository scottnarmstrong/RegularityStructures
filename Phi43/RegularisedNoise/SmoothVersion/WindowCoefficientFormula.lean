/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientDecayReal
public import Phi43.RegularisedNoise.SmoothVersion.GlobalCharacterDerivative

/-!
# Smooth translated Fourier coefficients

The coefficient of a translated, time-supported kernel is a fixed complex scalar times a
character in the translation variable.  This file names that formula and records the smoothness
of its real and imaginary parts for use by the random Fourier-series certificate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff ComplexConjugate

namespace RegularityStructures.Phi43

def smoothVersionWindowCoefficientFormula (Phi : SpaceTime → ℝ) (a b : ℝ)
    (k : WindowFrequency) (z : SpaceTime) : ℂ :=
  (b - a)⁻¹ •
    (globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0) *
      (conj (globalWindowFourierMode (b - a) k z) *
        ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u))

def smoothVersionWindowCoefficientAmplitude (Phi : SpaceTime → ℝ) (a b : ℝ)
    (k : WindowFrequency) : ℂ :=
  (b - a)⁻¹ •
    (globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0) *
      ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u)

private theorem smoothVersionWindowCoefficientFormula_eq_amplitude_smul
    (Phi : SpaceTime → ℝ) (a b : ℝ) (k : WindowFrequency) (z : SpaceTime) :
    smoothVersionWindowCoefficientFormula Phi a b k z =
      smoothVersionWindowCoefficientAmplitude Phi a b k •
        conj (globalWindowFourierMode (b - a) k z) := by
  unfold smoothVersionWindowCoefficientFormula smoothVersionWindowCoefficientAmplitude
  simp [Algebra.smul_def]
  ring

private theorem contDiff_globalWindowFourierMode (L : ℝ) (k : WindowFrequency) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      globalWindowFourierMode L k (p.1, torusProj p.2)) := by
  unfold globalWindowFourierMode
  simp only [torusProj, fourier_coe_apply]
  have hspace : ∀ i : Fin 3, ContDiff ℝ ∞
      (fun p : ℝ × (Fin 3 → ℝ) => (p.2 i : ℂ)) := by
    intro i
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd)
  apply ContDiff.mul
  · let harg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
        (2 * (Real.pi : ℂ) * Complex.I * (k 0 : ℂ)) *
          ((L⁻¹ * p.1 : ℝ) : ℂ) / (1 : ℂ)) :=
      (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))).div_const 1
    exact Complex.contDiff_exp.comp harg
  · refine contDiff_prod ?_
    intro i hi
    let harg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
        (2 * (Real.pi : ℂ) * Complex.I * (k i.succ : ℂ)) *
          ((p.2 i : ℝ) : ℂ) / (1 : ℂ)) :=
      (contDiff_const.mul (hspace i)).div_const 1
    exact Complex.contDiff_exp.comp harg

theorem isSmoothOnSpaceTime_smoothVersionWindowCoefficientFormula_re
    (Phi : SpaceTime → ℝ) (a b : ℝ) (k : WindowFrequency) :
    IsSmoothOnSpaceTime
      (fun z => (smoothVersionWindowCoefficientFormula Phi a b k z).re) := by
  unfold smoothVersionWindowCoefficientFormula IsSmoothOnSpaceTime
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
    (smoothVersionWindowCoefficientFormula Phi a b k (p.1, torusProj p.2)).re)
  apply Complex.reCLM.contDiff.comp
  have hc := contDiff_globalWindowFourierMode (b - a) k
  have hcc : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      conj (globalWindowFourierMode (b - a) k (p.1, torusProj p.2))) := by
    exact Complex.conjCLE.contDiff.comp hc
  unfold smoothVersionWindowCoefficientFormula
  apply ContDiff.const_smul
  apply ContDiff.mul
  · fun_prop
  · apply ContDiff.mul
    · exact hcc
    · fun_prop

theorem isSmoothOnSpaceTime_smoothVersionWindowCoefficientFormula_im
    (Phi : SpaceTime → ℝ) (a b : ℝ) (k : WindowFrequency) :
    IsSmoothOnSpaceTime
      (fun z => (smoothVersionWindowCoefficientFormula Phi a b k z).im) := by
  unfold smoothVersionWindowCoefficientFormula IsSmoothOnSpaceTime
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
    (smoothVersionWindowCoefficientFormula Phi a b k (p.1, torusProj p.2)).im)
  apply Complex.imCLM.contDiff.comp
  have hc := contDiff_globalWindowFourierMode (b - a) k
  have hcc : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      conj (globalWindowFourierMode (b - a) k (p.1, torusProj p.2))) := by
    exact Complex.conjCLE.contDiff.comp hc
  unfold smoothVersionWindowCoefficientFormula
  apply ContDiff.const_smul
  apply ContDiff.mul
  · fun_prop
  · apply ContDiff.mul
    · exact hcc
    · fun_prop

theorem smoothVersionWindowCoefficientFormula_eq_mFourierCoeff
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) (k : WindowFrequency) :
    smoothVersionWindowCoefficientFormula Phi a b k z =
      UnitAddTorus.mFourierCoeff
        (fun y : UnitAddTorus (Fin 4) =>
          (Phi (z - windowPoint a b y) : ℂ)) k := by
  symm
  simpa [smoothVersionWindowCoefficientFormula] using
    (mFourierCoeff_windowKernel_eq_character hPhi hR hR0 hz ha hb k
      (integrable_windowKernel_pullback hPhi hR hR0 hz ha hb k))

theorem norm_iteratedFDeriv_smoothVersionWindowCoefficientFormula_re_le
    (Phi : SpaceTime → ℝ) (a b : ℝ) (k : WindowFrequency) (q : ℕ)
    (hL : 1 ≤ b - a) (p : ℝ × (Fin 3 → ℝ)) :
    ‖iteratedFDeriv ℝ q
        (fun r : ℝ × (Fin 3 → ℝ) =>
          (smoothVersionWindowCoefficientFormula Phi a b k
            (r.1, torusProj r.2)).re) p‖ ≤
      ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
        (q.factorial : ℝ) * 2 *
          (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q := by
  have hchar := contDiff_globalWindowFourierMode (b - a) k
  have hconj : ContDiff ℝ ∞ (fun r : ℝ × (Fin 3 → ℝ) =>
      conj (globalWindowFourierMode (b - a) k (r.1, torusProj r.2))) := by
    exact Complex.conjCLE.contDiff.comp hchar
  have hformula : ContDiff ℝ ∞ (fun r : ℝ × (Fin 3 → ℝ) =>
      smoothVersionWindowCoefficientFormula Phi a b k (r.1, torusProj r.2)) := by
    rw [show (fun r : ℝ × (Fin 3 → ℝ) =>
        smoothVersionWindowCoefficientFormula Phi a b k (r.1, torusProj r.2)) =
        (fun r => smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k (r.1, torusProj r.2))) by
      funext r
      exact smoothVersionWindowCoefficientFormula_eq_amplitude_smul Phi a b k
        (r.1, torusProj r.2)]
    exact ContDiff.const_smul _ hconj
  have hconjbound : ∀ r : ℝ × (Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ q
        (fun s : ℝ × (Fin 3 → ℝ) =>
          conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r‖ ≤
        (q.factorial : ℝ) * 2 *
          (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q := by
    intro r
    have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_iteratedFDeriv_comp_left
      (x := r) (hchar.contDiffAt (x := r))
        (by exact_mod_cast le_top : q ≤ (∞ : ℕ∞ω))
    rw [Complex.conjCLE_norm] at hc
    have hc' : ‖iteratedFDeriv ℝ q
        (fun s : ℝ × (Fin 3 → ℝ) =>
          conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r‖ ≤
        ‖iteratedFDeriv ℝ q
          (fun s : ℝ × (Fin 3 → ℝ) =>
            globalWindowFourierMode (b - a) k (s.1, torusProj s.2)) r‖ := by
      simpa [Function.comp_def] using hc
    exact hc'.trans (norm_iteratedFDeriv_globalWindowFourierMode_le hL k q r)
  have hmul : ∀ r : ℝ × (Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ q
        (fun s : ℝ × (Fin 3 → ℝ) =>
          smoothVersionWindowCoefficientAmplitude Phi a b k •
            conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r‖ ≤
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
          ((q.factorial : ℝ) * 2 *
            (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q) := by
    intro r
    have hconjq : ContDiffAt ℝ (q : ℕ∞ω)
        (fun s : ℝ × (Fin 3 → ℝ) =>
          conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r :=
      (hconj.contDiffAt (x := r)).of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_const_smul_apply' hconjq]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hconjbound r) (norm_nonneg _)
  have hreal := Complex.reCLM.norm_iteratedFDeriv_comp_left
    (x := p) (hformula.contDiffAt (x := p))
      (by exact_mod_cast le_top : q ≤ (∞ : ℕ∞ω))
  rw [Complex.reCLM_norm] at hreal
  have hreal' : ‖iteratedFDeriv ℝ q
      (fun r : ℝ × (Fin 3 → ℝ) =>
        (smoothVersionWindowCoefficientFormula Phi a b k
          (r.1, torusProj r.2)).re) p‖ ≤
      ‖iteratedFDeriv ℝ q
        (fun r : ℝ × (Fin 3 → ℝ) =>
          smoothVersionWindowCoefficientFormula Phi a b k
            (r.1, torusProj r.2)) p‖ := by
    simpa [Function.comp_def] using hreal
  have hformula_mul :
      ‖iteratedFDeriv ℝ q
        (fun r : ℝ × (Fin 3 → ℝ) =>
          smoothVersionWindowCoefficientFormula Phi a b k
            (r.1, torusProj r.2)) p‖ ≤
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
          ((q.factorial : ℝ) * 2 *
            (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q) := by
    rw [show (fun r : ℝ × (Fin 3 → ℝ) =>
        smoothVersionWindowCoefficientFormula Phi a b k
          (r.1, torusProj r.2)) =
        (fun r => smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k (r.1, torusProj r.2))) by
      funext r
      exact smoothVersionWindowCoefficientFormula_eq_amplitude_smul Phi a b k
        (r.1, torusProj r.2)]
    exact hmul p
  simpa [mul_assoc] using hreal'.trans hformula_mul

theorem norm_iteratedFDeriv_smoothVersionWindowCoefficientFormula_im_le
    (Phi : SpaceTime → ℝ) (a b : ℝ) (k : WindowFrequency) (q : ℕ)
    (hL : 1 ≤ b - a) (p : ℝ × (Fin 3 → ℝ)) :
    ‖iteratedFDeriv ℝ q
        (fun r : ℝ × (Fin 3 → ℝ) =>
          (smoothVersionWindowCoefficientFormula Phi a b k
            (r.1, torusProj r.2)).im) p‖ ≤
      ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
        (q.factorial : ℝ) * 2 *
          (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q := by
  have hchar := contDiff_globalWindowFourierMode (b - a) k
  have hconj : ContDiff ℝ ∞ (fun r : ℝ × (Fin 3 → ℝ) =>
      conj (globalWindowFourierMode (b - a) k (r.1, torusProj r.2))) := by
    exact Complex.conjCLE.contDiff.comp hchar
  have hformula : ContDiff ℝ ∞ (fun r : ℝ × (Fin 3 → ℝ) =>
      smoothVersionWindowCoefficientFormula Phi a b k (r.1, torusProj r.2)) := by
    rw [show (fun r : ℝ × (Fin 3 → ℝ) =>
        smoothVersionWindowCoefficientFormula Phi a b k (r.1, torusProj r.2)) =
        (fun r => smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k (r.1, torusProj r.2))) by
      funext r
      exact smoothVersionWindowCoefficientFormula_eq_amplitude_smul Phi a b k
        (r.1, torusProj r.2)]
    exact ContDiff.const_smul _ hconj
  have hconjbound : ∀ r : ℝ × (Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ q
        (fun s : ℝ × (Fin 3 → ℝ) =>
          conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r‖ ≤
        (q.factorial : ℝ) * 2 *
          (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q := by
    intro r
    have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_iteratedFDeriv_comp_left
      (x := r) (hchar.contDiffAt (x := r))
        (by exact_mod_cast le_top : q ≤ (∞ : ℕ∞ω))
    rw [Complex.conjCLE_norm] at hc
    have hc' : ‖iteratedFDeriv ℝ q
        (fun s : ℝ × (Fin 3 → ℝ) =>
          conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r‖ ≤
        ‖iteratedFDeriv ℝ q
          (fun s : ℝ × (Fin 3 → ℝ) =>
            globalWindowFourierMode (b - a) k (s.1, torusProj s.2)) r‖ := by
      simpa [Function.comp_def] using hc
    exact hc'.trans (norm_iteratedFDeriv_globalWindowFourierMode_le hL k q r)
  have hmul : ∀ r : ℝ × (Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ q
        (fun s : ℝ × (Fin 3 → ℝ) =>
          smoothVersionWindowCoefficientAmplitude Phi a b k •
            conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r‖ ≤
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
          ((q.factorial : ℝ) * 2 *
            (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q) := by
    intro r
    have hconjq : ContDiffAt ℝ (q : ℕ∞ω)
        (fun s : ℝ × (Fin 3 → ℝ) =>
          conj (globalWindowFourierMode (b - a) k (s.1, torusProj s.2))) r :=
      (hconj.contDiffAt (x := r)).of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_const_smul_apply' hconjq]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hconjbound r) (norm_nonneg _)
  have him := Complex.imCLM.norm_iteratedFDeriv_comp_left
    (x := p) (hformula.contDiffAt (x := p))
      (by exact_mod_cast le_top : q ≤ (∞ : ℕ∞ω))
  rw [Complex.imCLM_norm] at him
  have him' : ‖iteratedFDeriv ℝ q
      (fun r : ℝ × (Fin 3 → ℝ) =>
        (smoothVersionWindowCoefficientFormula Phi a b k
          (r.1, torusProj r.2)).im) p‖ ≤
      ‖iteratedFDeriv ℝ q
        (fun r : ℝ × (Fin 3 → ℝ) =>
          smoothVersionWindowCoefficientFormula Phi a b k
            (r.1, torusProj r.2)) p‖ := by
    simpa [Function.comp_def] using him
  have hformula_mul :
      ‖iteratedFDeriv ℝ q
        (fun r : ℝ × (Fin 3 → ℝ) =>
          smoothVersionWindowCoefficientFormula Phi a b k
            (r.1, torusProj r.2)) p‖ ≤
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ *
          ((q.factorial : ℝ) * 2 *
            (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ q) := by
    rw [show (fun r : ℝ × (Fin 3 → ℝ) =>
        smoothVersionWindowCoefficientFormula Phi a b k
          (r.1, torusProj r.2)) =
        (fun r => smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k (r.1, torusProj r.2))) by
      funext r
      exact smoothVersionWindowCoefficientFormula_eq_amplitude_smul Phi a b k
        (r.1, torusProj r.2)]
    exact hmul p
  simpa [mul_assoc] using him'.trans hformula_mul

theorem smoothVersion_windowCoefficientAmplitude_decay
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) (hN : 0 < N) (a b : ℝ)
    (ha : a = -N - R - 1) (hb : b = N + R + 1) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : Fin 4, ∀ k : WindowFrequency, k i ≠ 0 →
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ ≤
          C * |(k i : ℝ)|⁻¹ ^ m := by
  intro m
  obtain ⟨C, hC0, hC⟩ := smoothVersion_windowKernel_mFourierCoeff_decay
    hPhi hR hR0 hN (0, fun _ : Fin 3 => 0) (by simpa using hN) m
  refine ⟨C, hC0, ?_⟩
  intro i k hki
  let z₀ : SpaceTime := (0, fun _ : Fin 3 => 0)
  have hz₀ : |z₀.1| < N := by simpa [z₀] using hN
  have hformula := smoothVersionWindowCoefficientFormula_eq_mFourierCoeff
    hPhi hR hR0 hz₀ ha hb k
  have hamp : smoothVersionWindowCoefficientFormula Phi a b k z₀ =
      smoothVersionWindowCoefficientAmplitude Phi a b k •
        conj (globalWindowFourierMode (b - a) k z₀) := by
    exact smoothVersionWindowCoefficientFormula_eq_amplitude_smul Phi a b k z₀
  have hchar : ‖globalWindowFourierMode (b - a) k z₀‖ = 1 := by
    unfold globalWindowFourierMode
    simp only [norm_mul, fourier_apply, Circle.norm_coe, norm_prod]
    simp
  calc
    ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ =
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k z₀)‖ := by
            rw [norm_smul, Complex.norm_conj, hchar, mul_one]
    _ = ‖smoothVersionWindowCoefficientFormula Phi a b k z₀‖ := by rw [hamp]
    _ = ‖UnitAddTorus.mFourierCoeff
          (fun y : UnitAddTorus (Fin 4) =>
            (Phi (z₀ - windowPoint a b y) : ℂ)) k‖ := by rw [hformula]
    _ ≤ C * |(k i : ℝ)|⁻¹ ^ m := by
      simpa [z₀, ha, hb] using hC i k hki

end RegularityStructures.Phi43

end

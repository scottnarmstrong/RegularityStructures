/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowLiftDecay
public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientTranslation
public import Phi43.RegularisedNoise.SmoothVersion.CoordinateDecay
public import Phi43.RegularisedNoise.SmoothVersion.PeriodicDerivative
public import Phi43.RegularisedNoise.SmoothVersion.TorusSeries

/-!
# Decay of translated finite-window coefficients

The finite-window lift has rapidly decaying torus Fourier coefficients.  This is the deterministic
coefficient estimate used by the smooth modification of a translated white noise.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace RegularityStructures.Phi43

private theorem iteratedDeriv_complex_ofReal {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (f t : ℂ)) =
      (fun t : ℝ => ((iteratedDeriv n f t : ℝ) : ℂ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have htop : (n : ℕ∞ω) < (∞ : ℕ∞ω) :=
        WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
      have hreal :=
        ((hf.differentiable_iteratedDeriv n htop).differentiableAt
          (x := t)).hasDerivAt
      have hcomplex := hreal.ofReal_comp
      simpa [iteratedDeriv_succ] using hcomplex.deriv

private theorem norm_iteratedDeriv_complex_ofReal {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n (fun s : ℝ => (f s : ℂ)) t‖ =
      ‖iteratedDeriv n f t‖ := by
  rw [iteratedDeriv_complex_ofReal hf n]
  simp

theorem smoothVersion_windowKernel_mFourierCoeff_decay
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) (_hN : 0 < N) (z : SpaceTime) (hz : |z.1| < N) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : Fin 4, ∀ k : Fin 4 → ℤ, k i ≠ 0 →
        ‖UnitAddTorus.mFourierCoeff
          (fun y : UnitAddTorus (Fin 4) =>
            (Phi (z - windowPoint (-N - R - 1) (N + R + 1) y) : ℂ)) k‖ ≤
          C * |(k i : ℝ)|⁻¹ ^ m := by
  intro m
  obtain ⟨hends, hcont, hpoint⟩ := continuous_windowKernelLift_eq_windowPoint
    hPhi hR hz (by rfl) (by rfl)
  obtain ⟨C, hC0, hC⟩ := smoothVersion_norm_iteratedDeriv_windowKernelLift_coordinateSlice_le
    hPhi hR hz hR0 (by rfl) (by rfl) hends m
  refine ⟨C * (2 * Real.pi)⁻¹ ^ m, mul_nonneg hC0 (by positivity), ?_⟩
  intro i k hki
  let fR : C(UnitAddTorus (Fin 4), ℝ) :=
    ⟨windowKernelLift Phi hPhi z (-N - R - 1) (N + R + 1) hends,
      hcont⟩
  let fC : UnitAddTorus (Fin 4) → ℂ := complexifyTorusContinuousMap fR
  have hfC : Continuous fC := (complexifyTorusContinuousMap fR).continuous
  have hslice : ∀ x : UnitAddTorus (Fin 3),
      ContDiff ℝ ∞ (fun t : ℝ =>
        fC (coordinateInsert i (t : UnitAddCircle) x)) := by
    intro x
    exact Complex.ofRealCLM.contDiff.comp
      (smoothVersion_contDiff_windowKernelLift_coordinateSlice hPhi hR hz hR0 (by rfl) (by rfl)
        hends i x)
  have hperiod : ∀ x : UnitAddTorus (Fin 3), ∀ j < m,
      iteratedDeriv j (fun t : ℝ =>
          fC (coordinateInsert i (t : UnitAddCircle) x)) 1 =
        iteratedDeriv j (fun t : ℝ =>
          fC (coordinateInsert i (t : UnitAddCircle) x)) 0 := by
    intro x j hj
    have hper := smoothVersion_periodic_windowKernelLift_coordinateSlice
      hPhi hR hz hR0 (by rfl) (by rfl) hends i x
    have hperC : Function.Periodic
        (fun t : ℝ => fC (coordinateInsert i (t : UnitAddCircle) x)) 1 := by
      intro t
      change (windowKernelLift Phi hPhi z (-N - R - 1) (N + R + 1) hends
          (coordinateInsert i ((t + (1 : ℝ)) : UnitAddCircle) x) : ℂ) =
        (windowKernelLift Phi hPhi z (-N - R - 1) (N + R + 1) hends
          (coordinateInsert i (t : UnitAddCircle) x) : ℂ)
      exact congrArg (fun r : ℝ => (r : ℂ)) (hper t)
    simpa only [zero_add] using (periodic_iteratedDeriv_one (hslice x) hperC j) 0
  let Cdec : ℝ := (C * (2 * Real.pi)⁻¹ ^ m) * |(k i : ℝ)|⁻¹ ^ m
  have hbound : ∀ x : UnitAddTorus (Fin 3),
      ((1 : ℝ) / (2 * Real.pi * |(k i : ℝ)|)) ^ m *
          ((1 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
            ‖iteratedDeriv m (fun s : ℝ =>
              fC (coordinateInsert i (s : UnitAddCircle) x)) t‖) ≤ Cdec := by
    intro x
    have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv m (fun s : ℝ =>
          fC (coordinateInsert i (s : UnitAddCircle) x)) t‖ ≤ C := by
      intro t ht
      rw [show (fun s : ℝ => fC (coordinateInsert i (s : UnitAddCircle) x)) =
          (fun s : ℝ =>
            (windowKernelLift Phi hPhi z (-N - R - 1) (N + R + 1) hends
              (coordinateInsert i (s : UnitAddCircle) x) : ℂ)) by
        funext s
        rfl]
      rw [norm_iteratedDeriv_complex_ofReal
        (smoothVersion_contDiff_windowKernelLift_coordinateSlice hPhi hR hz hR0 (by rfl) (by rfl)
          hends i x)]
      exact hC i x t ht
    have hint : IntervalIntegrable (fun t : ℝ =>
        ‖iteratedDeriv m (fun s : ℝ =>
          fC (coordinateInsert i (s : UnitAddCircle) x)) t‖) volume 0 1 := by
      exact ((hslice x).continuous_iteratedDeriv m
        (WithTop.coe_le_coe.mpr le_top)).norm.continuousOn.intervalIntegrable
    have hinter : (∫ t in (0 : ℝ)..1,
        ‖iteratedDeriv m (fun s : ℝ =>
          fC (coordinateInsert i (s : UnitAddCircle) x)) t‖) ≤ C := by
      calc
        _ ≤ ∫ t in (0 : ℝ)..1, C := by
          exact intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
            (by norm_num) hint intervalIntegrable_const hderiv
        _ = C := by simp
    have habs : 0 < |(k i : ℝ)| := by
      have hkabs : (1 : ℝ) ≤ |(k i : ℝ)| := by
        exact_mod_cast Int.one_le_abs hki
      linarith
    have hfactor :
        ((1 : ℝ) / (2 * Real.pi * |(k i : ℝ)|)) ^ m =
          (2 * Real.pi)⁻¹ ^ m * |(k i : ℝ)|⁻¹ ^ m := by
      have hbase : (1 : ℝ) / (2 * Real.pi * |(k i : ℝ)|) =
          (2 * Real.pi)⁻¹ * |(k i : ℝ)|⁻¹ := by
        field_simp [ne_of_gt Real.pi_pos, ne_of_gt habs]
      rw [hbase, mul_pow]
    calc
      _ = ((2 * Real.pi)⁻¹ ^ m * |(k i : ℝ)|⁻¹ ^ m) *
          ((1 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
            ‖iteratedDeriv m (fun s : ℝ =>
              fC (coordinateInsert i (s : UnitAddCircle) x)) t‖) := by
            rw [hfactor]
      _ ≤ ((2 * Real.pi)⁻¹ ^ m * |(k i : ℝ)|⁻¹ ^ m) * C := by
            apply mul_le_mul_of_nonneg_left
            · simpa using hinter
            · positivity
      _ = Cdec := by
            simp only [Cdec]
            ring
  have hdec := norm_mFourierCoeff_le_of_coordinate_decay_periodic i fC k hfC hki hslice
    hperiod (C := Cdec) hbound
  have hf_eq : fC = (fun y : UnitAddTorus (Fin 4) =>
      (Phi (z - windowPoint (-N - R - 1) (N + R + 1) y) : ℂ)) := by
    funext y
    simp [fC, fR, complexifyTorusContinuousMap, hpoint]
  rw [hf_eq] at hdec
  simpa [Cdec] using hdec

end RegularityStructures.Phi43

end

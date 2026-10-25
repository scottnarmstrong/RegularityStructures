/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Deterministic
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Compactly supported window Fourier modes

The Fourier modes on a finite time window are made into test functions on space-time by cutting
them off on the window.  Their compact support is the only fact needed by the white-noise
evaluation map; smoothness is retained by the coefficient functions, not by the cut-off modes.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Convolution

namespace RegularityStructures.Phi43

abbrev WindowFrequency := Fin 4 → ℤ

def windowFourierModeShift (a b : ℝ) (k : WindowFrequency) (z : SpaceTime) : ℂ :=
  fourier (k 0) (((b - a)⁻¹ * (z.1 - a) : ℝ) : UnitAddCircle) *
    ∏ i : Fin 3, fourier (k i.succ) (z.2 i)

def windowFourierRealModeShift (a b : ℝ) (k : WindowFrequency) (z : SpaceTime) : ℝ :=
  (windowFourierModeShift a b k z).re

def windowFourierImagModeShift (a b : ℝ) (k : WindowFrequency) (z : SpaceTime) : ℝ :=
  (windowFourierModeShift a b k z).im

def windowInterval (a b : ℝ) : Set SpaceTime := Ioc a b ×ˢ Set.univ

def windowFourierRealTestMode (a b : ℝ) (k : WindowFrequency) : SpaceTime → ℝ :=
  (windowInterval a b).indicator (windowFourierRealModeShift a b k)

def windowFourierImagTestMode (a b : ℝ) (k : WindowFrequency) : SpaceTime → ℝ :=
  (windowInterval a b).indicator (windowFourierImagModeShift a b k)

private theorem hasCompactSupport_windowInterval_indicator
    {a b : ℝ} (_hab : a < b) {f : SpaceTime → ℝ}
    (_hf : ∀ z, |f z| ≤ 1) : HasCompactSupport ((windowInterval a b).indicator f) := by
  apply HasCompactSupport.intro' ((isCompact_Icc : IsCompact (Icc a b)).prod isCompact_univ)
    ((isClosed_Icc : IsClosed (Icc a b)).prod isClosed_univ)
  intro z hz
  by_cases hwin : z ∈ windowInterval a b
  · exact False.elim (hz ⟨⟨le_of_lt hwin.1.1, hwin.1.2⟩, mem_univ z.2⟩)
  · simp [Set.indicator, hwin]

theorem measurable_windowFourierModeShift (a b : ℝ) (k : WindowFrequency) :
    Measurable (windowFourierModeShift a b k) := by
  unfold windowFourierModeShift
  fun_prop

theorem norm_windowFourierModeShift {a b : ℝ}
    (k : WindowFrequency) (z : SpaceTime) :
    ‖windowFourierModeShift a b k z‖ = 1 := by
  unfold windowFourierModeShift
  simp only [norm_mul, fourier_apply, Circle.norm_coe, norm_prod]
  simp

private theorem abs_windowFourierRealModeShift_le {a b : ℝ} (_hab : a < b)
    (k : WindowFrequency) (z : SpaceTime) :
    |windowFourierRealModeShift a b k z| ≤ 1 := by
  unfold windowFourierRealModeShift
  exact (Complex.abs_re_le_norm _).trans_eq (norm_windowFourierModeShift k z)

private theorem abs_windowFourierImagModeShift_le {a b : ℝ} (_hab : a < b)
    (k : WindowFrequency) (z : SpaceTime) :
    |windowFourierImagModeShift a b k z| ≤ 1 := by
  unfold windowFourierImagModeShift
  exact (Complex.abs_im_le_norm _).trans_eq (norm_windowFourierModeShift k z)

theorem measurable_windowFourierRealTestMode {a b : ℝ} (k : WindowFrequency) :
    Measurable (windowFourierRealTestMode a b k) := by
  unfold windowFourierRealTestMode windowInterval
  exact Measurable.indicator
    (Complex.continuous_re.measurable.comp (measurable_windowFourierModeShift a b k))
    (measurableSet_Ioc.prod MeasurableSet.univ)

theorem measurable_windowFourierImagTestMode {a b : ℝ} (k : WindowFrequency) :
    Measurable (windowFourierImagTestMode a b k) := by
  unfold windowFourierImagTestMode windowInterval
  exact Measurable.indicator
    (Complex.continuous_im.measurable.comp (measurable_windowFourierModeShift a b k))
    (measurableSet_Ioc.prod MeasurableSet.univ)

theorem hasCompactSupport_windowFourierRealTestMode {a b : ℝ} (hab : a < b)
    (k : WindowFrequency) :
    HasCompactSupport (windowFourierRealTestMode a b k) := by
  apply hasCompactSupport_windowInterval_indicator hab
  exact abs_windowFourierRealModeShift_le hab k

theorem hasCompactSupport_windowFourierImagTestMode {a b : ℝ} (hab : a < b)
    (k : WindowFrequency) :
    HasCompactSupport (windowFourierImagTestMode a b k) := by
  apply hasCompactSupport_windowInterval_indicator hab
  exact abs_windowFourierImagModeShift_le hab k

theorem memLp_windowFourierRealTestMode {a b : ℝ} (hab : a < b)
    (k : WindowFrequency) :
    MemLp (windowFourierRealTestMode a b k) 2 (volume : Measure SpaceTime) := by
  apply (hasCompactSupport_windowFourierRealTestMode hab k).memLp_of_bound
    (measurable_windowFourierRealTestMode k).aestronglyMeasurable 1
  filter_upwards [] with z
  by_cases hz : z ∈ windowInterval a b
  · change ‖(windowInterval a b).indicator (windowFourierRealModeShift a b k) z‖ ≤ 1
    rw [Set.indicator_of_mem hz]
    exact abs_windowFourierRealModeShift_le hab k z
  · simp [windowFourierRealTestMode, hz]

theorem memLp_windowFourierImagTestMode {a b : ℝ} (hab : a < b)
    (k : WindowFrequency) :
    MemLp (windowFourierImagTestMode a b k) 2 (volume : Measure SpaceTime) := by
  apply (hasCompactSupport_windowFourierImagTestMode hab k).memLp_of_bound
    (measurable_windowFourierImagTestMode k).aestronglyMeasurable 1
  filter_upwards [] with z
  by_cases hz : z ∈ windowInterval a b
  · change ‖(windowInterval a b).indicator (windowFourierImagModeShift a b k) z‖ ≤ 1
    rw [Set.indicator_of_mem hz]
    exact abs_windowFourierImagModeShift_le hab k z
  · simp [windowFourierImagTestMode, hz]

end RegularityStructures.Phi43

end

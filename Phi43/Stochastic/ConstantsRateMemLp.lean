/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateModulus

/-!
# Integrability from a global power bound

A measurable function on `ℝ × T³` bounded by `A size⁻ᵃ` lies in `Lᑫ` whenever `2 < a q < 5`:
the interior is controlled by the five-dimensional volume bound and the exterior by the
two-dimensional (time) volume bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem constantsRate_memLp_of_bound {f : SpaceTime → ℝ} (hmeas : Measurable f) {q a A : ℝ}
    (hq : 1 ≤ q) (hA : 0 ≤ A) (haq2 : 2 < a * q) (haq5 : a * q < 5)
    (hf : ∀ᵐ z : SpaceTime ∂volume,
      0 < torusParabolicSize z → |f z| ≤ A * torusParabolicSize z ^ (-a)) :
    MemLp f (ENNReal.ofReal q) := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < a := by
    by_contra h
    push Not at h
    nlinarith
  have hfin : ∫⁻ z, ‖f z‖ₑ ^ q < ⊤ := by
    let S : Set SpaceTime := {z | torusParabolicSize z ≤ 1}
    have hSm : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
    rw [← lintegral_add_compl (μ := volume) (fun z => ‖f z‖ₑ ^ q) hSm]
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · have := constantsRate_region_bound (f := f) (q := q) (a := a) (A := A) (R := 1) hq0 ha
        haq5 hA one_pos hf
      exact this.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    · have hSc : Sᶜ = {z : SpaceTime | 1 < torusParabolicSize z} := by
        ext z
        simp [S, not_le]
      calc
        ∫⁻ z in Sᶜ, ‖f z‖ₑ ^ q ≤
            ∫⁻ z in Sᶜ, ENNReal.ofReal (A ^ q) *
              ENNReal.ofReal (torusParabolicSize z ^ (-(a * q))) := by
          apply lintegral_mono_ae
          have hmem : ∀ᵐ z : SpaceTime ∂(volume.restrict Sᶜ), z ∈ Sᶜ :=
            ae_restrict_mem hSm.compl
          filter_upwards [ae_restrict_of_ae hf, hmem] with z hz hzm
          have hz1 : 0 < torusParabolicSize z := by
            have : ¬ torusParabolicSize z ≤ 1 := hzm
            linarith [not_le.mp this]
          exact constantsRate_enorm_rpow_le hA (torusParabolicSize_nonneg z) hq0.le (hz hz1)
        _ = ENNReal.ofReal (A ^ q) *
            ∫⁻ z in Sᶜ, ENNReal.ofReal (torusParabolicSize z ^ (-(a * q))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (A ^ q) *
            ENNReal.ofReal (2 * 2 ^ (2 : ℝ) / (1 - 2 ^ ((2 : ℝ) - a * q)) * 1 ^ ((2 : ℝ) - a * q)) := by
          rw [hSc]
          gcongr
          exact constantsRate_lintegral_size_tail_le (d := 2) (c := 2) (by norm_num)
            (by norm_num) haq2 one_pos (fun r hr => constantsRate_volume_ball_le_two_rpow hr)
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.mpr hq0).ne'
    ENNReal.ofReal_ne_top hmeas.aestronglyMeasurable]
  simpa [ENNReal.toReal_ofReal hq0.le] using hfin

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateWeights
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Translation moduli from pointwise increment bounds

A function on `ℝ × T³` with a pointwise singular bound `|f z| ≤ A size(z)⁻ᵃ` and a Hölder-type
increment bound `|f(z - h) - f(z)| ≤ B size(h)^θ size(z)⁻ᶜ` away from the origin has a power
translation modulus in `Lᑫ`: the near region `size z ≲ size h` is estimated by the singular bound,
the far region by the increment bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem constantsRate_ae_size_pos : ∀ᵐ z : SpaceTime ∂volume, 0 < torusParabolicSize z := by
  have h : volume {z : SpaceTime | torusParabolicSize z ≤ 0} = 0 := by
    have := constantsRate_volume_ball_le_five_rpow (le_refl (0 : ℝ))
    simpa using this
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with z hz
  exact lt_of_not_ge hz

theorem constantsRate_enorm_rpow_le {x A s a q : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (h : |x| ≤ A * s ^ (-a)) :
    ‖x‖ₑ ^ q ≤ ENNReal.ofReal (A ^ q) * ENNReal.ofReal (s ^ (-(a * q))) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    |x| ^ q ≤ (A * s ^ (-a)) ^ q := Real.rpow_le_rpow (abs_nonneg _) h hq
    _ = A ^ q * s ^ (-(a * q)) := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hs _), ← Real.rpow_mul hs, neg_mul]

theorem constantsRate_region_bound {f : SpaceTime → ℝ} {q a A R : ℝ} (hq0 : 0 < q) (ha : 0 < a)
    (haq : a * q < 5) (hA : 0 ≤ A) (hR : 0 < R)
    (hf : ∀ᵐ z : SpaceTime ∂volume,
      0 < torusParabolicSize z → |f z| ≤ A * torusParabolicSize z ^ (-a)) :
    ∫⁻ z in {z : SpaceTime | torusParabolicSize z ≤ R}, ‖f z‖ₑ ^ q ≤
      ENNReal.ofReal (A ^ q) *
        ENNReal.ofReal (16 * 2 ^ (a * q) / (1 - 2 ^ (a * q - 5)) * R ^ (5 - a * q)) := by
  have haq0 : 0 < a * q := mul_pos ha hq0
  have hae : {z : SpaceTime | torusParabolicSize z ≤ R} =ᵐ[volume]
      {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R} := by
    filter_upwards [constantsRate_ae_size_pos] with z hz
    exact propext ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  rw [setLIntegral_congr hae]
  calc
    ∫⁻ z in {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R},
        ‖f z‖ₑ ^ q ≤
        ∫⁻ z in {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R},
          ENNReal.ofReal (A ^ q) * ENNReal.ofReal (torusParabolicSize z ^ (-(a * q))) := by
      apply lintegral_mono_ae
      have hmem : ∀ᵐ z : SpaceTime ∂(volume.restrict
          {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R}),
          z ∈ {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R} :=
        ae_restrict_mem
          ((measurableSet_lt measurable_const measurable_torusParabolicSize).inter
            (measurableSet_le measurable_torusParabolicSize measurable_const))
      filter_upwards [ae_restrict_of_ae hf, hmem] with z hz hzm
      exact constantsRate_enorm_rpow_le hA (torusParabolicSize_nonneg z) hq0.le (hz hzm.1)
    _ = ENNReal.ofReal (A ^ q) *
        ∫⁻ z in {z : SpaceTime | 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ R},
          ENNReal.ofReal (torusParabolicSize z ^ (-(a * q))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      gcongr
      exact constantsRate_lintegral_size_head_le (d := 5) (c := 16) (by norm_num) haq0 haq hR
        (fun r hr => constantsRate_volume_ball_le_five_rpow hr)

private theorem size_neg_le (h : SpaceTime) :
    torusParabolicSize (-h) ≤ 2 * torusParabolicSize h := by
  unfold torusParabolicSize
  have h1 : (-h).1 = -h.1 := rfl
  have h2 : (-h).2 = -h.2 := rfl
  rw [h1, h2, abs_neg]
  have := torusSpatialNorm_neg_le h.2
  nlinarith [Real.sqrt_nonneg |h.1|, torusSpatialNorm_nonneg h.2]

private theorem rpow_two_le {q : ℝ} (_hq : 1 ≤ q) :
    (2 : ℝ≥0∞) ^ (q - 1) ≤ ENNReal.ofReal (2 ^ q) := by
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- A power translation modulus in `Lᑫ`. -/
theorem constantsRate_translation_modulus {f : SpaceTime → ℝ} (hmeas : Measurable f)
    {q a A c B θ κ r₀ : ℝ} (hq : 1 ≤ q) (ha : 0 < a) (haq : a * q < 5) (hA : 0 ≤ A)
    (hcq : 5 < c * q) (hB : 0 ≤ B) (hκ : 1 ≤ κ) (hr₀1 : r₀ ≤ 1)
    (hf : ∀ᵐ z : SpaceTime ∂volume,
      0 < torusParabolicSize z → |f z| ≤ A * torusParabolicSize z ^ (-a))
    (hinc : ∀ h : SpaceTime, torusParabolicSize h ≤ r₀ → ∀ᵐ z : SpaceTime ∂volume,
      κ * torusParabolicSize h ≤ torusParabolicSize z →
        |f (z - h) - f z| ≤ B * torusParabolicSize h ^ θ * torusParabolicSize z ^ (-c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : SpaceTime, 0 < torusParabolicSize h → torusParabolicSize h ≤ r₀ →
      ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ q ≤
        ENNReal.ofReal (C * torusParabolicSize h ^
          (min (5 - a * q) (θ * q + 5 - c * q))) := by
  have hq0 : 0 < q := by linarith
  have hκ0 : 0 < κ := by linarith
  have haq0 : 0 < a * q := mul_pos ha hq0
  have hden₁ : 0 < 1 - (2 : ℝ) ^ (a * q - 5) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (z := a * q - 5)
      (by norm_num) (by linarith)
    linarith
  have hden₂ : 0 < 1 - (2 : ℝ) ^ ((5 : ℝ) - c * q) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (z := (5 : ℝ) - c * q)
      (by norm_num) (by linarith)
    linarith
  let K₁ : ℝ := 16 * 2 ^ (a * q) / (1 - 2 ^ (a * q - 5))
  let K₂ : ℝ := 16 * 2 ^ (5 : ℝ) / (1 - 2 ^ ((5 : ℝ) - c * q))
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  let e₁ : ℝ := 5 - a * q
  let e₂ : ℝ := θ * q + 5 - c * q
  let C₁ : ℝ := 2 ^ q * 2 * (A ^ q * (K₁ * (4 * κ + 8) ^ e₁))
  let C₂ : ℝ := B ^ q * (K₂ * κ ^ ((5 : ℝ) - c * q))
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro h hr0 hr1
  set r : ℝ := torusParabolicSize h with hr
  let N : Set SpaceTime := {z | torusParabolicSize z ≤ κ * r}
  let M : Set SpaceTime := {z | torusParabolicSize z ≤ (4 * κ + 8) * r}
  have hNm : MeasurableSet N := measurableSet_le measurable_torusParabolicSize measurable_const
  have hMm : MeasurableSet M := measurableSet_le measurable_torusParabolicSize measurable_const
  have hPm : Measurable (fun w : SpaceTime => ‖f w‖ₑ ^ q) :=
    (hmeas.enorm).pow_const q
  -- near region
  have hshift : ∫⁻ z in N, ‖f (z - h)‖ₑ ^ q ≤ ∫⁻ z in M, ‖f z‖ₑ ^ q := by
    have h1 : ∫⁻ z in N, ‖f (z - h)‖ₑ ^ q ≤
        ∫⁻ z, M.indicator (fun w => ‖f w‖ₑ ^ q) (z - h) := by
      rw [← lintegral_indicator hNm]
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ N
      · rw [indicator_of_mem hz]
        have hzM : z - h ∈ M := by
          have h4 := torusParabolicSize_sub_le (z - h) (-h)
          rw [sub_neg_eq_add, sub_add_cancel] at h4
          have hn := size_neg_le h
          have hz' : torusParabolicSize z ≤ κ * r := hz
          change torusParabolicSize (z - h) ≤ (4 * κ + 8) * r
          linarith
        dsimp only
        rw [indicator_of_mem hzM]
      · rw [indicator_of_notMem hz]
        exact bot_le
    calc
      _ ≤ _ := h1
      _ = ∫⁻ w, M.indicator (fun w => ‖f w‖ₑ ^ q) w :=
        lintegral_sub_right_eq_self (fun w => M.indicator (fun w => ‖f w‖ₑ ^ q) w) h
      _ = _ := lintegral_indicator hMm _
  have hNM : ∫⁻ z in N, ‖f z‖ₑ ^ q ≤ ∫⁻ z in M, ‖f z‖ₑ ^ q := by
    apply lintegral_mono_set
    intro z hz
    change torusParabolicSize z ≤ (4 * κ + 8) * r
    have hz' : torusParabolicSize z ≤ κ * r := hz
    have hr0' : 0 ≤ r := hr0.le
    nlinarith [mul_nonneg hκ0.le hr0']
  have hMbound : ∫⁻ z in M, ‖f z‖ₑ ^ q ≤
      ENNReal.ofReal (A ^ q) * ENNReal.ofReal (K₁ * ((4 * κ + 8) * r) ^ e₁) := by
    have := constantsRate_region_bound (f := f) (q := q) (a := a) (A := A) (R := (4 * κ + 8) * r) hq0 ha haq hA
      (by positivity) hf
    simpa [K₁, e₁, mul_assoc] using this
  have hpt : ∀ z, ‖f (z - h) - f z‖ₑ ^ q ≤
      ENNReal.ofReal (2 ^ q) * (‖f (z - h)‖ₑ ^ q + ‖f z‖ₑ ^ q) := by
    intro z
    calc
      ‖f (z - h) - f z‖ₑ ^ q ≤ (‖f (z - h)‖ₑ + ‖f z‖ₑ) ^ q :=
        ENNReal.rpow_le_rpow enorm_sub_le hq0.le
      _ ≤ 2 ^ (q - 1) * (‖f (z - h)‖ₑ ^ q + ‖f z‖ₑ ^ q) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
      _ ≤ _ := by gcongr; exact rpow_two_le hq
  have hnear : ∫⁻ z in N, ‖f (z - h) - f z‖ₑ ^ q ≤
      ENNReal.ofReal (C₁ * r ^ e₁) := by
    calc
      ∫⁻ z in N, ‖f (z - h) - f z‖ₑ ^ q ≤
          ∫⁻ z in N, ENNReal.ofReal (2 ^ q) * (‖f (z - h)‖ₑ ^ q + ‖f z‖ₑ ^ q) :=
        lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ q) *
          ((∫⁻ z in N, ‖f (z - h)‖ₑ ^ q) + ∫⁻ z in N, ‖f z‖ₑ ^ q) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (f := fun z => ‖f (z - h)‖ₑ ^ q)
            ((hmeas.comp (measurable_id.sub_const h)).enorm.pow_const q)
            (fun z => ‖f z‖ₑ ^ q)]
      _ ≤ ENNReal.ofReal (2 ^ q) *
          ((ENNReal.ofReal (A ^ q) * ENNReal.ofReal (K₁ * ((4 * κ + 8) * r) ^ e₁)) +
            (ENNReal.ofReal (A ^ q) * ENNReal.ofReal (K₁ * ((4 * κ + 8) * r) ^ e₁))) := by
        exact mul_le_mul_right (add_le_add (hshift.trans hMbound) (hNM.trans hMbound)) _
      _ = ENNReal.ofReal (C₁ * r ^ e₁) := by
        rw [← two_mul]
        have hC : C₁ * r ^ e₁ = 2 ^ q * (2 * (A ^ q * (K₁ * ((4 * κ + 8) * r) ^ e₁))) := by
          simp only [C₁]
          rw [Real.mul_rpow (by positivity) hr0.le]
          ring
        rw [hC, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ q by positivity),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ A ^ q by positivity)]
  -- far region
  have hfar : ∫⁻ z in Nᶜ, ‖f (z - h) - f z‖ₑ ^ q ≤
      ENNReal.ofReal (C₂ * r ^ e₂) := by
    have hNc : Nᶜ = {z : SpaceTime | κ * r < torusParabolicSize z} := by
      ext z
      simp [N, not_le]
    calc
      ∫⁻ z in Nᶜ, ‖f (z - h) - f z‖ₑ ^ q ≤
          ∫⁻ z in Nᶜ, ENNReal.ofReal ((B * r ^ θ) ^ q) *
            ENNReal.ofReal (torusParabolicSize z ^ (-(c * q))) := by
        apply lintegral_mono_ae
        have hmem : ∀ᵐ z : SpaceTime ∂(volume.restrict Nᶜ), z ∈ Nᶜ :=
          ae_restrict_mem hNm.compl
        filter_upwards [ae_restrict_of_ae (hinc h hr1), hmem] with z hz hzm
        have hz8 : κ * r ≤ torusParabolicSize z := by
          have : ¬ torusParabolicSize z ≤ κ * r := hzm
          linarith [not_le.mp this]
        exact constantsRate_enorm_rpow_le (by positivity) (torusParabolicSize_nonneg z) hq0.le (hz hz8)
      _ = ENNReal.ofReal ((B * r ^ θ) ^ q) *
          ∫⁻ z in Nᶜ, ENNReal.ofReal (torusParabolicSize z ^ (-(c * q))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((B * r ^ θ) ^ q) *
          ENNReal.ofReal (16 * 2 ^ (5 : ℝ) / (1 - 2 ^ ((5 : ℝ) - c * q)) *
            (κ * r) ^ ((5 : ℝ) - c * q)) := by
        rw [hNc]
        gcongr
        exact constantsRate_lintegral_size_tail_le (d := 5) (c := 16) (by norm_num)
          (by norm_num) hcq (by positivity)
          (fun r hr => constantsRate_volume_ball_le_five_rpow hr)
      _ = ENNReal.ofReal (C₂ * r ^ e₂) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [C₂, K₂, e₂]
        rw [Real.mul_rpow hB (Real.rpow_nonneg hr0.le _), ← Real.rpow_mul hr0.le,
          Real.mul_rpow hκ0.le hr0.le]
        have : r ^ (θ * q + 5 - c * q) = r ^ (θ * q) * r ^ ((5 : ℝ) - c * q) := by
          rw [← Real.rpow_add hr0]
          ring_nf
        rw [this]
        ring
  have htot : ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ q =
      (∫⁻ z in N, ‖f (z - h) - f z‖ₑ ^ q) + ∫⁻ z in Nᶜ, ‖f (z - h) - f z‖ₑ ^ q :=
    (lintegral_add_compl (μ := volume) (fun z => ‖f (z - h) - f z‖ₑ ^ q) hNm).symm
  rw [htot]
  refine (add_le_add hnear hfar).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hg1 : r ^ e₁ ≤ r ^ (min (5 - a * q) (θ * q + 5 - c * q)) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 (hr1.trans hr₀1) (min_le_left _ _)
  have hg2 : r ^ e₂ ≤ r ^ (min (5 - a * q) (θ * q + 5 - c * q)) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 (hr1.trans hr₀1) (min_le_right _ _)
  nlinarith [mul_le_mul_of_nonneg_left hg1 hC₁, mul_le_mul_of_nonneg_left hg2 hC₂]

end RegularityStructures.Phi43

end

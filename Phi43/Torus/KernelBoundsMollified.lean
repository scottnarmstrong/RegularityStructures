/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGlobal
public import Phi43.Torus.KernelBoundsSupport
public import Phi43.Torus.KernelBoundsConvolution
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Uniform singular bound for the mollified massive heat kernel

The compact support of the periodised mollifier and the global singular majorant for the massive
heat kernel give the ε-uniform estimate for the mollified kernel.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

theorem integral_massiveHeatKernel_time_strip_le (a : ℝ) (ha : 0 ≤ a) (z : SpaceTime) :
    ∫ w : SpaceTime in Icc (-a) a ×ˢ (Set.univ : Set Torus3),
      massiveHeatKernel (z - w) ≤ 2 * a := by
  let K : Set SpaceTime := Icc (-a) a ×ˢ (Set.univ : Set Torus3)
  let _ : (volume : Measure Torus3).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have hK : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hG : Integrable (fun w : SpaceTime => massiveHeatKernel (z - w)) :=
    integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel z
  have hKG : Integrable (K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w))) :=
    hG.indicator hK
  have hprod := integral_prod _ hKG
  have hslice : ∀ t : ℝ,
      ∫ x : Torus3, K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w)) (t, x)
        ≤ (Icc (-a) a).indicator (fun _ : ℝ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ Icc (-a) a
    · have hsp : ∫ x : Torus3, massiveHeatKernel (z - (t, x)) ≤ 1 := by
        change ∫ x : Torus3, massiveHeatKernel (z.1 - t, z.2 - x) ≤ 1
        by_cases hzt : 0 < z.1 - t
        · simp only [massiveHeatKernel, hzt, ite_true]
          rw [integral_const_mul]
          · rw [integral_sub_left_eq_self (heatKernel (z.1 - t))
              (volume : Measure Torus3) z.2]
            rw [integral_heatKernel hzt]
            simp only [mul_one]
            rw [Real.exp_le_one_iff]
            linarith
        · simp only [massiveHeatKernel, hzt, ite_false]
          simp
      calc
        ∫ x : Torus3,
            K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w)) (t, x) =
            ∫ x : Torus3, massiveHeatKernel (z - (t, x)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                simp [K, ht]
        _ ≤ 1 := hsp
        _ = (Icc (-a) a).indicator (fun _ : ℝ => (1 : ℝ)) t := by
          simp [ht]
    · calc
        ∫ x : Torus3,
            K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w)) (t, x) = 0 := by
              rw [← integral_zero]
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                simp [K, ht]
        _ ≤ (Icc (-a) a).indicator (fun _ : ℝ => (1 : ℝ)) t := by
          simp [ht]
  calc
    ∫ w : SpaceTime in K, massiveHeatKernel (z - w) =
        ∫ t : ℝ, ∫ x : Torus3,
          K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w)) (t, x) := by
      rw [← integral_indicator hK]
      change ∫ w : SpaceTime,
          K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w)) w =
        ∫ t : ℝ, ∫ x : Torus3,
          K.indicator (fun w : SpaceTime => massiveHeatKernel (z - w)) (t, x)
      exact hprod
    _ ≤ ∫ t : ℝ, (Icc (-a) a).indicator (fun _ : ℝ => (1 : ℝ)) t := by
      apply integral_mono
      · exact hKG.integral_prod_left
      · exact ((integrableOn_const (s := Icc (-a) a)
          (hs := isCompact_Icc.measure_ne_top)) :
          IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-a) a) volume).integrable_indicator
            measurableSet_Icc
      · exact hslice
    _ = 2 * a := by
      rw [integral_indicator measurableSet_Icc]
      simp only [setIntegral_const, smul_eq_mul]
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring

theorem rpow_neg_three_le_mul (x y L : ℝ) (_hx : 0 < x) (hy : 0 < y) (hL : 0 < L)
    (hxy : y ≤ L * x) :
    x ^ (-(3 : ℝ)) ≤ L ^ (3 : ℝ) * y ^ (-(3 : ℝ)) := by
  have hyL : 0 < y / L := div_pos hy hL
  have hbase : y / L ≤ x := (div_le_iff₀ hL).2 (by simpa [mul_comm] using hxy)
  have hmono := Real.rpow_le_rpow_of_nonpos hyL hbase (by norm_num : -(3 : ℝ) ≤ 0)
  have hid : (y / L) ^ (-(3 : ℝ)) =
      L ^ (3 : ℝ) * y ^ (-(3 : ℝ)) := by
    rw [Real.div_rpow hy.le hL.le, Real.rpow_neg hy.le, Real.rpow_neg hL.le]
    field_simp
  exact hmono.trans_eq hid

theorem mollifiedKernel_singular_bound (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      |mollifiedKernel ρ ε z| ≤
        C * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
  obtain ⟨C₀, hC₀, hGbound⟩ := massiveHeatKernel_global_singular_bound
  obtain ⟨D, hD, hPbound⟩ := periodise_uniform_bound ρ hρ
  obtain ⟨B, hB, hsupport⟩ := periodise_support_parabolic_bound ρ hρ
  let N : ℝ := ∫ y, |ρ y|
  have hN : 0 ≤ N := by
    dsimp [N]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hPint : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∫ w, |periodise ρ ε w| ≤ N := by
    intro ε hε hε1
    calc
      ∫ w, |periodise ρ ε w| ≤ ∫ y, |rescale ρ ε y| :=
        integral_abs_periodise_le ρ hρ hε hε1
      _ = N := integral_abs_rescale_eq ρ hε
  let Lnear : ℝ := 8 * B + 1
  let Lfar : ℝ := 1 + (8 * B)⁻¹
  let Cnear : ℝ := 2 * B ^ 2 * D * Lnear ^ (3 : ℝ)
  let Cfar : ℝ := C₀ * 512 * N * Lfar ^ (3 : ℝ)
  have hLnear : 0 < Lnear := by
    dsimp [Lnear]
    nlinarith
  have hLfar : 0 < Lfar := by
    dsimp [Lfar]
    positivity
  have hCnear : 0 ≤ Cnear := by
    dsimp [Cnear]
    positivity
  have hCfar : 0 ≤ Cfar := by
    dsimp [Cfar]
    positivity
  refine ⟨Cnear + Cfar, add_nonneg hCnear hCfar, ?_⟩
  intro ε hε hε1 z
  let a : ℝ := (B * ε) ^ 2
  let K : Set SpaceTime := Icc (-a) a ×ˢ (Set.univ : Set Torus3)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hK : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hPzero : ∀ w ∉ K, periodise ρ ε w = 0 := by
    intro w hw
    have hwtime : w.1 ∉ Icc (-a) a := by
      intro hwt
      exact hw ⟨hwt, Set.mem_univ _⟩
    have hwout : a < |w.1| := by
      by_cases hleft : w.1 < -a
      · rw [abs_of_neg (lt_of_lt_of_le hleft (neg_nonpos.mpr ha))]
        linarith
      · have hright : a < w.1 := by
          by_contra hright
          exact hwtime ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
        rw [abs_of_nonneg (le_trans ha hright.le)]
        exact hright
    by_contra hPnz
    dsimp [a] at hwout
    have hsquare : (√|w.1|) ^ 2 = |w.1| := Real.sq_sqrt (abs_nonneg _)
    have hroot : B * ε < √|w.1| := by
      nlinarith [hsquare, Real.sqrt_nonneg |w.1|, mul_nonneg hB.le hε.le]
    have hsw := hsupport hε hε1 w hPnz
    unfold torusParabolicSize at hsw
    nlinarith [hsw, torusSpatialNorm_nonneg w.2]
  have hPabs : Integrable (fun w : SpaceTime => |periodise ρ ε w|) :=
    (integrable_periodise ρ hρ hε).norm
  have hscale : ε ^ (-5 : ℤ) * ε ^ (2 : ℕ) = ε ^ (-3 : ℤ) := by
    rw [show ε ^ 2 = ε ^ (2 : ℤ) by norm_num, ← zpow_add₀ (ne_of_gt hε)]
    norm_num
  have hnear : ∀ {z : SpaceTime},
      torusParabolicSize z ≤ 8 * B * ε →
        |mollifiedKernel ρ ε z| ≤ 2 * B ^ 2 * D * ε ^ (-3 : ℤ) := by
    intro z hsnear
    have hGz : Integrable (fun w : SpaceTime => massiveHeatKernel (z - w)) :=
      integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel z
    have hstrip : ∫ w : SpaceTime in K, massiveHeatKernel (z - w) ≤ 2 * a := by
      simpa [K] using integral_massiveHeatKernel_time_strip_le a ha z
    have htarget : Integrable (fun w : SpaceTime =>
        (D * ε ^ (-5 : ℤ)) *
          K.indicator (fun v : SpaceTime => massiveHeatKernel (z - v)) w) :=
      (hGz.indicator hK).const_mul (D * ε ^ (-5 : ℤ))
    have hnorm : ‖∫ w, massiveHeatKernel (z - w) * periodise ρ ε w‖ ≤
        ∫ w, (D * ε ^ (-5 : ℤ)) *
          K.indicator (fun v : SpaceTime => massiveHeatKernel (z - v)) w := by
      apply norm_integral_le_of_norm_le htarget
      filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg (z - w))]
      by_cases hw : w ∈ K
      · rw [Set.indicator_of_mem hw]
        calc
          massiveHeatKernel (z - w) * |periodise ρ ε w| ≤
              massiveHeatKernel (z - w) * (D * ε ^ (-5 : ℤ)) :=
            mul_le_mul_of_nonneg_left (hPbound hε hε1 w)
              (massiveHeatKernel_nonneg (z - w))
          _ = (D * ε ^ (-5 : ℤ)) * massiveHeatKernel (z - w) := by ring
      · rw [hPzero w hw]
        simp [hw]
    have hnear' : |mollifiedKernel ρ ε z| ≤
        (D * ε ^ (-5 : ℤ)) * (2 * a) := by
      change |∫ w, massiveHeatKernel (z - w) * periodise ρ ε w| ≤ _
      calc
        |∫ w, massiveHeatKernel (z - w) * periodise ρ ε w| ≤
            ∫ w, (D * ε ^ (-5 : ℤ)) *
              K.indicator (fun v : SpaceTime => massiveHeatKernel (z - v)) w := hnorm
        _ = (D * ε ^ (-5 : ℤ)) *
            ∫ w in K, massiveHeatKernel (z - w) := by
          rw [integral_const_mul, integral_indicator hK]
        _ ≤ (D * ε ^ (-5 : ℤ)) * (2 * a) :=
          mul_le_mul_of_nonneg_left hstrip (by positivity)
    calc
      |mollifiedKernel ρ ε z| ≤ (D * ε ^ (-5 : ℤ)) * (2 * a) := hnear'
      _ = 2 * B ^ 2 * D * ε ^ (-3 : ℤ) := by
        dsimp [a]
        calc
          (D * ε ^ (-5 : ℤ)) * (2 * ((B * ε) ^ 2)) =
              2 * B ^ 2 * D * (ε ^ (-5 : ℤ) * ε ^ (2 : ℕ)) := by ring
          _ = 2 * B ^ 2 * D * ε ^ (-3 : ℤ) := by rw [hscale]
  have hfar : ∀ {z : SpaceTime}, 8 * B * ε < torusParabolicSize z →
      |mollifiedKernel ρ ε z| ≤
        Cfar * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
    intro z hfarz
    have hz : 0 < torusParabolicSize z := by
      nlinarith [hB, hε]
    have hLfar' : torusParabolicSize z + ε ≤ Lfar * torusParabolicSize z := by
      have hden : 0 < 8 * B := by positivity
      have heps : ε ≤ torusParabolicSize z / (8 * B) := by
        apply (le_div_iff₀ hden).2
        linarith
      dsimp [Lfar]
      field_simp
      nlinarith
    have hratio : torusParabolicSize z ^ (-(3 : ℝ)) ≤
        Lfar ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) :=
      rpow_neg_three_le_mul (torusParabolicSize z) (torusParabolicSize z + ε) Lfar
        hz (by positivity) hLfar hLfar'
    let F : ℝ := C₀ * 512 * torusParabolicSize z ^ (-(3 : ℝ))
    have hF : 0 ≤ F := by
      dsimp [F]
      positivity
    have htarget : Integrable (fun w : SpaceTime => F * |periodise ρ ε w|) :=
      hPabs.const_mul F
    have hnorm : ‖∫ w, massiveHeatKernel (z - w) * periodise ρ ε w‖ ≤
        ∫ w, F * |periodise ρ ε w| := by
      apply norm_integral_le_of_norm_le htarget
      filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg (z - w))]
      by_cases hw : periodise ρ ε w = 0
      · rw [hw]
        simp
      · have hsw := hsupport hε hε1 w hw
        have htri := torusParabolicSize_sub_le z w
        have hsdiff : torusParabolicSize z / 8 ≤ torusParabolicSize (z - w) := by
          nlinarith [htri, hfarz, hsw]
        have hsdiffpos : 0 < torusParabolicSize (z - w) := by
          exact lt_of_lt_of_le (by positivity) hsdiff
        have hratio' : torusParabolicSize (z - w) ^ (-(3 : ℝ)) ≤
            8 ^ (3 : ℝ) * torusParabolicSize z ^ (-(3 : ℝ)) :=
          rpow_neg_three_le_mul (torusParabolicSize (z - w))
            (torusParabolicSize z) 8 hsdiffpos hz (by norm_num) (by nlinarith [hsdiff])
        have hGfar : massiveHeatKernel (z - w) ≤ F := by
          dsimp [F]
          calc
            massiveHeatKernel (z - w) ≤
                C₀ * torusParabolicSize (z - w) ^ (-(3 : ℝ)) :=
              hGbound (z - w) hsdiffpos
            _ ≤ C₀ * (8 ^ (3 : ℝ) *
                torusParabolicSize z ^ (-(3 : ℝ))) :=
              mul_le_mul_of_nonneg_left hratio' hC₀
            _ = C₀ * 512 * torusParabolicSize z ^ (-(3 : ℝ)) := by ring
        exact mul_le_mul_of_nonneg_right hGfar (abs_nonneg _)
    have hfar' : |mollifiedKernel ρ ε z| ≤ F * N := by
      change |∫ w, massiveHeatKernel (z - w) * periodise ρ ε w| ≤ _
      calc
        |∫ w, massiveHeatKernel (z - w) * periodise ρ ε w| ≤
            ∫ w, F * |periodise ρ ε w| := hnorm
        _ = F * ∫ w, |periodise ρ ε w| := integral_const_mul F _
        _ ≤ F * N := mul_le_mul_of_nonneg_left (hPint hε hε1) hF
    calc
      |mollifiedKernel ρ ε z| ≤ F * N := hfar'
      _ = C₀ * 512 * N * torusParabolicSize z ^ (-(3 : ℝ)) := by
        dsimp [F]
        ring
      _ ≤ C₀ * 512 * N * (Lfar ^ (3 : ℝ) *
          (torusParabolicSize z + ε) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = Cfar * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
        dsimp [Cfar]
        ring
  by_cases hs : torusParabolicSize z ≤ 8 * B * ε
  · have hnear' := hnear hs
    have hcomp : ε ^ (-(3 : ℝ)) ≤
        Lnear ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) :=
      rpow_neg_three_le_mul ε (torusParabolicSize z + ε) Lnear hε
        (add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg z) hε) hLnear (by
          dsimp [Lnear]
          nlinarith)
    calc
      |mollifiedKernel ρ ε z| ≤ 2 * B ^ 2 * D * ε ^ (-3 : ℤ) := hnear'
      _ ≤ 2 * B ^ 2 * D * ε ^ (-(3 : ℝ)) := by norm_num
      _ ≤ Cnear * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
        have hcoef : 0 ≤ 2 * B ^ 2 * D := by positivity
        calc
          2 * B ^ 2 * D * ε ^ (-(3 : ℝ)) ≤
              2 * B ^ 2 * D *
                (Lnear ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hcomp hcoef
          _ = Cnear * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
            dsimp [Cnear]
            ring
      _ ≤ (Cnear + Cfar) * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact Real.rpow_nonneg
            (add_nonneg (torusParabolicSize_nonneg z) hε.le) _
  · exact (hfar (lt_of_not_ge hs)).trans (by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact Real.rpow_nonneg
          (add_nonneg (torusParabolicSize_nonneg z) hε.le) _)

end Phi43

end RegularityStructures

end

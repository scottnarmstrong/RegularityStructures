/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonKernelLp
public import Phi43.Stochastic.ConstantsComparisonLocalSingular
public import Phi43.Torus.KernelBoundsMollifier
public import Phi43.Torus.KernelBoundsSupport
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import RegularityStructures.Analysis.Parabolic.SmoothNorm

/-!
# A singular bound for the mollified truncated kernel

This is the signed-kernel analogue of `mollifiedKernel_singular_bound`.  It is the
uniform estimate needed for the `K`-covariance.  The local part uses the order-three
singular integral from `ConstantsComparisonLocalSingular`; the far part uses the
pointwise Hairer bound and the `L¹` mass of the periodised mollifier.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem constantsComparison_torusParabolicSize_neg_le (w : SpaceTime) :
    torusParabolicSize (-w) ≤ 2 * torusParabolicSize w := by
  unfold torusParabolicSize
  change √|(-w.1)| + torusSpatialNorm (-w.2) ≤
    2 * (√|w.1| + torusSpatialNorm w.2)
  rw [abs_neg]
  calc
    √|w.1| + torusSpatialNorm (-w.2) ≤
        √|w.1| + 2 * torusSpatialNorm w.2 := by
      nlinarith [torusSpatialNorm_neg_le w.2]
    _ ≤ 2 * (√|w.1| + torusSpatialNorm w.2) := by
      nlinarith [Real.sqrt_nonneg |w.1|, torusSpatialNorm_nonneg w.2]

private theorem constantsComparison_hairer_torusParabolicSize_pos_of_ne {z : SpaceTime}
    (hz : z ≠ 0) : 0 < torusParabolicSize z := by
  by_contra hs
  have hs0 : torusParabolicSize z = 0 :=
    le_antisymm (le_of_not_gt hs) (torusParabolicSize_nonneg z)
  have htime : √|z.1| = 0 := by
    unfold torusParabolicSize at hs0
    linarith [Real.sqrt_nonneg |z.1|, torusSpatialNorm_nonneg z.2]
  have hsp : torusSpatialNorm z.2 = 0 := by
    unfold torusParabolicSize at hs0
    linarith [Real.sqrt_nonneg |z.1|, torusSpatialNorm_nonneg z.2]
  have htime' : z.1 = 0 := by
    have hsq := Real.sq_sqrt (abs_nonneg z.1)
    have habs : |z.1| = 0 := by
      calc
        |z.1| = √|z.1| ^ 2 := hsq.symm
        _ = 0 := by rw [htime]; norm_num
    exact abs_eq_zero.mp habs
  have hcenter : torusCenteredRep z.2 = 0 := by
    apply (sqNorm3_eq_zero_iff _).mp
    rw [← torusSpatialNorm_sq, hsp]
    norm_num
  have hrep : torusRep z.2 = 0 := by
    funext i
    have hi := congrFun hcenter i
    unfold torusCenteredRep at hi
    split_ifs at hi with hhalf
    · have hrepIco := torusRep_mem_Ico z.2 i
      simp only [Pi.zero_apply] at hi
      have hi' : torusRep z.2 i = 1 := by linarith
      have hrepIco' := hrepIco
      simp only [mem_Ico] at hrepIco'
      linarith
    · exact hi
  have htorus : z.2 = 0 := by
    rw [← RegularityStructures.PDE.torusProj_torusRep z.2, hrep,
      RegularityStructures.PDE.torusProj_zero]
  exact hz (Prod.ext htime' htorus)

private theorem constantsComparison_hairer_local_ball_integral_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ}, 0 < r → ∀ {z : SpaceTime},
      torusParabolicSize z ≤ r →
        ∫ w in {w : SpaceTime | torusParabolicSize w ≤ r},
          |hairerKernelTorus N (z - w)| ≤ C * r ^ 2 := by
  obtain ⟨C, hC, hK⟩ :=
    constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  let C' : ℝ := C * 40 * 12 ^ 2
  have hC' : 0 ≤ C' := by
    dsimp [C']
    positivity
  refine ⟨C', hC', ?_⟩
  intro r hr z hz
  let S : Set SpaceTime := {w : SpaceTime | torusParabolicSize w ≤ r}
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hKshift : Integrable (fun w : SpaceTime =>
      |hairerKernelTorus N (z - w)|) :=
    (integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N) z).norm
  have hleft : Integrable (S.indicator (fun w : SpaceTime =>
      |hairerKernelTorus N (z - w)|)) := hKshift.indicator hS
  have hweight : Integrable (fun w : SpaceTime =>
      constantsComparisonLocalSingularWeight (12 * r) (z - w)) := by
    exact integrable_comp_sub_left_spaceTime
      (integrable_constantsComparisonLocalSingularWeight (by positivity)).1 z
  have hright : Integrable (fun w : SpaceTime => C *
      constantsComparisonLocalSingularWeight (12 * r) (z - w)) := hweight.const_mul C
  have hne : ∀ᵐ w : SpaceTime ∂volume, z - w ≠ 0 := by
    filter_upwards [@Measure.ae_ne SpaceTime _ volume
      (Measure.IsAddHaarMeasure.nullSingletonClass volume) z] with w hw hzero
    apply hw
    exact (sub_eq_zero.mp hzero).symm
  have hpoint : ∀ᵐ w : SpaceTime ∂volume,
      S.indicator (fun w : SpaceTime => |hairerKernelTorus N (z - w)|) w ≤
        C * constantsComparisonLocalSingularWeight (12 * r) (z - w) := by
    filter_upwards [hne] with w hw
    by_cases hws : w ∈ S
    · have hzw : torusParabolicSize (z - w) ≤ 12 * r := by
        have htri := torusParabolicSize_sub_le (z - w) (-w)
        have hneg := constantsComparison_torusParabolicSize_neg_le w
        have htri' : torusParabolicSize (z - w) ≤
            4 * (torusParabolicSize z + 2 * torusParabolicSize w) := by
          calc
            torusParabolicSize (z - w) ≤
                4 * (torusParabolicSize ((z - w) - (-w)) +
                  torusParabolicSize (-w)) := htri
            _ = 4 * (torusParabolicSize z + torusParabolicSize (-w)) := by
              congr 1
              simp [sub_eq_add_neg]
            _ ≤ 4 * (torusParabolicSize z + 2 * torusParabolicSize w) := by
              gcongr
        dsimp [S] at hws
        nlinarith
      have hzpos : 0 < torusParabolicSize (z - w) := by
        exact constantsComparison_hairer_torusParabolicSize_pos_of_ne hw
      have hbound := hK hzpos
      rw [Set.indicator_of_mem hws]
      simpa [constantsComparisonLocalSingularWeight, hzpos, hzw] using hbound
    · rw [Set.indicator_of_notMem hws]
      exact mul_nonneg hC
        (nonneg_constantsComparisonLocalSingularWeight (12 * r) (z - w))
  have hmono := integral_mono_ae hleft hright hpoint
  calc
    ∫ w in S, |hairerKernelTorus N (z - w)| =
        ∫ w, S.indicator (fun w : SpaceTime =>
          |hairerKernelTorus N (z - w)|) w := by
      rw [integral_indicator hS]
    _ ≤ ∫ w, C * constantsComparisonLocalSingularWeight (12 * r) (z - w) := hmono
    _ = C * ∫ w, constantsComparisonLocalSingularWeight (12 * r) w := by
      rw [integral_const_mul, integral_comp_sub_left_spaceTime]
    _ ≤ C * (40 * (12 * r) ^ 2) := by
      gcongr
      exact integral_constantsComparisonLocalSingularWeight_le (by positivity)
    _ = C' * r ^ 2 := by
      dsimp [C']
      ring

theorem hairerMollifiedKernel_singular_bound
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      |hairerMollifiedKernel N ρ ε z| ≤
        C * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
  obtain ⟨CK, hCK, hK⟩ :=
    constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨D, hD, hPbound⟩ := periodise_uniform_bound ρ hρ
  obtain ⟨B, hB, hsupport⟩ := periodise_support_parabolic_bound ρ hρ
  let mass : ℝ := ∫ y, |ρ y|
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hPint : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∫ w, |periodise ρ ε w| ≤ mass := by
    intro ε hε hε1
    calc
      ∫ w, |periodise ρ ε w| ≤ ∫ y, |rescale ρ ε y| :=
        integral_abs_periodise_le ρ hρ hε hε1
      _ = mass := integral_abs_rescale_eq ρ hε
  obtain ⟨CB, hCB, hball⟩ := constantsComparison_hairer_local_ball_integral_le N
  let Lnear : ℝ := 12 * B + 1
  let Lfar : ℝ := 1 + (8 * B)⁻¹
  let Cnear : ℝ := CB * D * (8 * B) ^ 2 * Lnear ^ (3 : ℝ)
  let Cfar : ℝ := CK * 512 * mass * Lfar ^ (3 : ℝ)
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
  have hscale : ε ^ (-5 : ℤ) * ε ^ (2 : ℕ) = ε ^ (-3 : ℤ) := by
    rw [show ε ^ 2 = ε ^ (2 : ℤ) by norm_num, ← zpow_add₀ (ne_of_gt hε)]
    norm_num
  have hnear : torusParabolicSize z ≤ 8 * B * ε →
      |hairerMollifiedKernel N ρ ε z| ≤
        Cnear * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
    intro hz
    let S : Set SpaceTime := {w : SpaceTime | torusParabolicSize w ≤ 8 * B * ε}
    have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
    have hPabs : Integrable (fun w : SpaceTime => |periodise ρ ε w|) :=
      (integrable_periodise ρ hρ hε).norm
    have hKshift : Integrable (fun w : SpaceTime =>
        |hairerKernelTorus N (z - w)|) :=
      (integrable_comp_sub_left_spaceTime
        (integrable_constantsComparison_hairerKernelTorus N) z).norm
    have htarget : Integrable (fun w : SpaceTime =>
        (D * ε ^ (-5 : ℤ)) * S.indicator
          (fun v : SpaceTime => |hairerKernelTorus N (z - v)|) w) := by
      exact (hKshift.indicator hS).const_mul _
    have hnorm : ‖∫ w, hairerKernelTorus N (z - w) * periodise ρ ε w‖ ≤
        ∫ w, (D * ε ^ (-5 : ℤ)) * S.indicator
          (fun v : SpaceTime => |hairerKernelTorus N (z - v)|) w := by
      apply norm_integral_le_of_norm_le htarget
      filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hws : w ∈ S
      · rw [Set.indicator_of_mem hws]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hPbound hε hε1 w)
          (abs_nonneg (hairerKernelTorus N (z - w)))
      · rw [Set.indicator_of_notMem hws]
        have hpzero : periodise ρ ε w = 0 := by
          by_contra hp
          have hw := hsupport hε hε1 w hp
          apply hws
          dsimp [S]
          have hnonneg : 0 ≤ B * ε := mul_nonneg hB.le hε.le
          nlinarith
        simp [hpzero]
    have hball' := hball (r := 8 * B * ε) (by positivity) hz
    have hnear' : |hairerMollifiedKernel N ρ ε z| ≤
        (D * ε ^ (-5 : ℤ)) * (CB * (8 * B * ε) ^ 2) := by
      change |∫ w, hairerKernelTorus N (z - w) * periodise ρ ε w| ≤ _
      calc
        _ ≤ ∫ w, (D * ε ^ (-5 : ℤ)) * S.indicator
            (fun v : SpaceTime => |hairerKernelTorus N (z - v)|) w := hnorm
        _ = (D * ε ^ (-5 : ℤ)) *
            ∫ w in S, |hairerKernelTorus N (z - w)| := by
          rw [integral_const_mul, integral_indicator hS]
        _ ≤ (D * ε ^ (-5 : ℤ)) * (CB * (8 * B * ε) ^ 2) :=
          mul_le_mul_of_nonneg_left hball' (by positivity)
    have hratio : ε ^ (-(3 : ℝ)) ≤
        Lnear ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) :=
      rpow_neg_three_le_mul ε (torusParabolicSize z + ε) Lnear hε
        (add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg z) hε) hLnear (by
          dsimp [Lnear]
          nlinarith)
    calc
      |hairerMollifiedKernel N ρ ε z| ≤
          (D * ε ^ (-5 : ℤ)) * (CB * (8 * B * ε) ^ 2) := hnear'
      _ = CB * D * (8 * B) ^ 2 *
          (ε ^ (-5 : ℤ) * ε ^ (2 : ℕ)) := by ring
      _ = CB * D * (8 * B) ^ 2 * ε ^ (-3 : ℤ) := by rw [hscale]
      _ ≤ CB * D * (8 * B) ^ 2 * ε ^ (-(3 : ℝ)) := by norm_num
      _ ≤ Cnear * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
        have hcoef : 0 ≤ CB * D * (8 * B) ^ 2 := by positivity
        calc
          _ ≤ CB * D * (8 * B) ^ 2 *
              (Lnear ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hratio hcoef
          _ ≤ Cnear * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
            dsimp [Cnear]
            apply le_of_eq
            ring_nf
  have hfar : 8 * B * ε < torusParabolicSize z →
      |hairerMollifiedKernel N ρ ε z| ≤
        Cfar * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
    intro hz
    have hzpos : 0 < torusParabolicSize z := by nlinarith [hB, hε]
    have hratio : torusParabolicSize z ^ (-(3 : ℝ)) ≤
        Lfar ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
      have hsum : torusParabolicSize z + ε ≤ Lfar * torusParabolicSize z := by
        have hden : 0 < 8 * B := by positivity
        have heps : ε ≤ torusParabolicSize z / (8 * B) := by
          apply (le_div_iff₀ hden).2
          linarith
        dsimp [Lfar]
        field_simp
        nlinarith
      exact rpow_neg_three_le_mul (torusParabolicSize z)
        (torusParabolicSize z + ε) Lfar hzpos (by positivity) hLfar hsum
    let F : ℝ := CK * 512 * torusParabolicSize z ^ (-(3 : ℝ))
    have hF : 0 ≤ F := by
      dsimp [F]
      positivity
    have hPabs : Integrable (fun w : SpaceTime => |periodise ρ ε w|) :=
      (integrable_periodise ρ hρ hε).norm
    have htarget : Integrable (fun w : SpaceTime => F * |periodise ρ ε w|) :=
      hPabs.const_mul F
    have hnorm : ‖∫ w, hairerKernelTorus N (z - w) * periodise ρ ε w‖ ≤
        ∫ w, F * |periodise ρ ε w| := by
      apply norm_integral_le_of_norm_le htarget
      filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hp : periodise ρ ε w = 0
      · simp [hp]
      · have hw := hsupport hε hε1 w hp
        have htri := torusParabolicSize_sub_le z w
        have hdiff : torusParabolicSize z / 8 ≤ torusParabolicSize (z - w) := by
          nlinarith [hz, hw, htri]
        have hdiffpos : 0 < torusParabolicSize (z - w) :=
          lt_of_lt_of_le (by positivity) hdiff
        have hpow : torusParabolicSize (z - w) ^ (-(3 : ℝ)) ≤
            8 ^ (3 : ℝ) * torusParabolicSize z ^ (-(3 : ℝ)) :=
          rpow_neg_three_le_mul (torusParabolicSize (z - w))
            (torusParabolicSize z) 8 hdiffpos hzpos (by norm_num) (by nlinarith [hdiff])
        have hk' : |hairerKernelTorus N (z - w)| ≤ F := by
          dsimp [F]
          calc
            |hairerKernelTorus N (z - w)| ≤
                CK * torusParabolicSize (z - w) ^ (-(3 : ℝ)) := hK hdiffpos
            _ ≤ CK * (8 ^ (3 : ℝ) * torusParabolicSize z ^ (-(3 : ℝ))) :=
              mul_le_mul_of_nonneg_left hpow hCK
            _ = CK * 512 * torusParabolicSize z ^ (-(3 : ℝ)) := by norm_num; ring
        exact mul_le_mul_of_nonneg_right hk' (abs_nonneg _)
    calc
      |hairerMollifiedKernel N ρ ε z| ≤ F * mass := by
        change |∫ w, hairerKernelTorus N (z - w) * periodise ρ ε w| ≤ _
        calc
          _ ≤ ∫ w, F * |periodise ρ ε w| := hnorm
          _ = F * ∫ w, |periodise ρ ε w| := integral_const_mul F _
          _ ≤ F * mass := mul_le_mul_of_nonneg_left (hPint hε hε1) hF
      _ = CK * 512 * mass * torusParabolicSize z ^ (-(3 : ℝ)) := by
        dsimp [F]
        ring
      _ ≤ CK * 512 * mass *
          (Lfar ^ (3 : ℝ) * (torusParabolicSize z + ε) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = Cfar * (torusParabolicSize z + ε) ^ (-(3 : ℝ)) := by
        dsimp [Cfar]
        ring
  by_cases hs : torusParabolicSize z ≤ 8 * B * ε
  · exact (hnear hs).trans (by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact Real.rpow_nonneg
          (add_nonneg (torusParabolicSize_nonneg z) hε.le) _)
  · exact (hfar (lt_of_not_ge hs)).trans (by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact Real.rpow_nonneg
          (add_nonneg (torusParabolicSize_nonneg z) hε.le) _)

end RegularityStructures.Phi43

end

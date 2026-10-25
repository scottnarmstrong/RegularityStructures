/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGradBridge
public import Phi43.BPHZ.GammaMomentGrad
public import Phi43.BPHZ.PositiveTreeFormulasBridge
import Mathlib.Tactic

/-!
# `gammaGrad` and `gammaPsiTaylor` are the increments of the spatial gradient and of the Taylor remainder

* `hairerSpatialGradient_eq_integral_torusGrad`: for `g` smooth on `ℝ × T³`,
  `hairerSpatialGradient N (g ∘ proj) i x = ∫ G_i(proj x - u) g(u) du`;
* `hairerSpatialGradient_sub_eq_gammaGrad`: for the tree field `Ψ`, the difference of the spatial
  gradients at `y` and `x` is `gammaGrad N ξ i (proj x) (proj y) ω`;
* `hairerIPsiRecentred_eq_gammaPsiTaylor`: `hairerIPsiRecentred N ξ ω x y =
  gammaPsiTaylor N ξ (proj x) (y.1 - x.1) (y.2 - x.2) ω`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

local instance gbm_addLeftInv : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance gbm_negInv : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

open scoped ContDiff in
/-- **The spatial gradient of `K ∗ g` is the pairing with the gradient kernel.** -/
theorem hairerSpatialGradient_eq_integral_torusGrad (N : ℕ) (i : Fin 3) {g : SpaceTime → ℝ}
    (hg : IsSmoothOnSpaceTime g) (x : ParabolicSpace) :
    hairerSpatialGradient N (fun w => g (spaceTimeProj w)) i x =
      ∫ u, hairerKernelTorusGrad N i (spaceTimeProj x - u) * g u := by
  have hf : ContDiff ℝ ∞ (fun w : ParabolicSpace => g (spaceTimeProj w)) := hg
  have hfc : Continuous (fun w : ParabolicSpace => g (spaceTimeProj w)) := hf.continuous
  rw [hairerSpatialGradient_eq_tsum_shellPairing N hf i x,
    ← integral_hairerKernelGrad_comp_proj_eq N i (IsSmoothOnSpaceTime.continuous hg) x]
  have hcpt : IsCompact ((fun z : ParabolicSpace => x - z) ''
      {z : ParabolicSpace | parabolicNorm z ≤ 1}) :=
    (isCompact_parabolicNorm_le 1).image (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hfc.continuousOn
  have hD : ∀ n, Continuous (fun w : ParabolicSpace =>
      lineIter [spaceDir i] (annShellC N n) (x - w)) := fun n =>
    (contDiff_lineIter (contDiff_annShellC N n) _).continuous.comp
      (continuous_const.sub continuous_id)
  have hDc : ∀ n, HasCompactSupport (fun w : ParabolicSpace =>
      lineIter [spaceDir i] (annShellC N n) (x - w)) := fun n =>
    (hasCompactSupport_lineIter_annShellC N n i).comp_homeomorph (Homeomorph.subLeft x)
  have hFi : ∀ n, Integrable (fun w : ParabolicSpace =>
      (fun w => g (spaceTimeProj w)) w * lineIter [spaceDir i] (annShellC N n) (x - w)) :=
    fun n => (hfc.mul (hD n)).integrable_of_hasCompactSupport (hDc n).mul_left
  have hFs : Summable fun n : ℕ => ∫ w : ParabolicSpace,
      ‖(fun w => g (spaceTimeProj w)) w * lineIter [spaceDir i] (annShellC N n) (x - w)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun w => norm_nonneg _)
      (fun n => ?_) (((summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
          (|C| * ∫ w, |lineIter [spaceDir i] (annKernel0C N) w|)))
    have hint : Integrable (fun w : ParabolicSpace =>
        |lineIter [spaceDir i] (annShellC N n) (x - w)|) :=
      ((integrable_lineIter_annShellC N n i).comp_sub_left x).abs
    calc ∫ w : ParabolicSpace, ‖(fun w => g (spaceTimeProj w)) w *
            lineIter [spaceDir i] (annShellC N n) (x - w)‖
        ≤ ∫ w : ParabolicSpace, |C| * |lineIter [spaceDir i] (annShellC N n) (x - w)| := by
          refine integral_mono (hFi n).norm (hint.const_mul _) fun w => ?_
          simp only [norm_mul, Real.norm_eq_abs]
          by_cases hw : 1 < parabolicNorm (x - w)
          · rw [lineIter_spaceDir_annShellC_eq_zero N n i
              (lt_of_le_of_lt (pow_le_one₀ (by positivity) (by norm_num)) hw)]
            simp
          · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            have hmem : w ∈ (fun z : ParabolicSpace => x - z) ''
                {z : ParabolicSpace | parabolicNorm z ≤ 1} := ⟨x - w, not_lt.1 hw, by simp⟩
            have := hC w hmem
            simp only [Real.norm_eq_abs] at this
            exact this.trans (le_abs_self C)
      _ = |C| * ∫ w : ParabolicSpace, |lineIter [spaceDir i] (annShellC N n) w| := by
          rw [integral_const_mul, integral_sub_left_eq_self
            (fun w => |lineIter [spaceDir i] (annShellC N n) w|) volume x]
      _ = _ := by rw [integral_abs_lineIter_annShellC]; ring
  rw [integral_tsum_of_summable_integral_norm hFi hFs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  unfold hairerKernelGrad
  rw [tsum_mul_left, mul_comm]

variable {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ωx : Ω}

theorem hairerConvolution_xi_eq_hairerPsiField (N : ℕ) (hξ : IsSmoothOnSpaceTime (ξ ωx))
    (y : ParabolicSpace) :
    hairerConvolution N (fun w => ξ ωx (spaceTimeProj w)) y =
      hairerPsiField N ξ ωx (spaceTimeProj y) :=
  hairerConvolution_comp_proj_eq N (IsSmoothOnSpaceTime.continuous hξ) y

open scoped ContDiff in
/-- The pathwise field `Ψ` is smooth on `ℝ × T³` when the noise is. -/
theorem isSmoothOnSpaceTime_hairerPsiField (N : ℕ) (hξ : IsSmoothOnSpaceTime (ξ ωx)) :
    IsSmoothOnSpaceTime (hairerPsiField N ξ ωx) := by
  have h := contDiff_hairerConvolution N (f := fun w => ξ ωx (spaceTimeProj w)) hξ
  have e : (fun p : ParabolicSpace => hairerPsiField N ξ ωx (p.1, torusProj p.2)) =
      hairerConvolution N (fun w => ξ ωx (spaceTimeProj w)) :=
    funext fun p => (hairerConvolution_xi_eq_hairerPsiField N hξ p).symm
  unfold IsSmoothOnSpaceTime
  rw [e]
  exact h

/-- **The increment of the spatial gradient of `K ∗ Ψ` is `gammaGrad`.** -/
theorem hairerSpatialGradient_sub_eq_gammaGrad (N : ℕ) (hξ : IsSmoothOnSpaceTime (ξ ωx))
    (i : Fin 3) (x y : ParabolicSpace) :
    hairerSpatialGradient N (fun w => hairerPsiField N ξ ωx (spaceTimeProj w)) i y -
        hairerSpatialGradient N (fun w => hairerPsiField N ξ ωx (spaceTimeProj w)) i x =
      gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ωx := by
  have hψ := isSmoothOnSpaceTime_hairerPsiField N hξ
  have hc := IsSmoothOnSpaceTime.continuous hψ
  rw [hairerSpatialGradient_eq_integral_torusGrad N i hψ,
    hairerSpatialGradient_eq_integral_torusGrad N i hψ, gammaGrad, ← integral_sub
      (integrable_hairerKernelTorusGrad_sub_mul_continuous N i _ hc)
      (integrable_hairerKernelTorusGrad_sub_mul_continuous N i _ hc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hairerGradIncrementKernel]
  ring

/-- **`hairerIPsiRecentred` is `gammaPsiTaylor`.** -/
theorem hairerIPsiRecentred_eq_gammaPsiTaylor (N : ℕ) (hξ : IsSmoothOnSpaceTime (ξ ωx))
    (x y : ParabolicSpace) :
    hairerIPsiRecentred N ξ ωx x y =
      gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ωx := by
  have hψ := isSmoothOnSpaceTime_hairerPsiField N hξ
  have hc := IsSmoothOnSpaceTime.continuous hψ
  have hrel : ∀ i : Fin 3, CanonicalData.relCoord x y i.succ = (y.2 - x.2) i := by
    intro i
    have hc4 : ∀ (z : ParabolicSpace) (j : Fin 3), parabolicCoords z j.succ = z.2 j := by
      intro z j
      fin_cases j <;> rfl
    simp [CanonicalData.relCoord, hc4]
  have hy : spaceTimeProj x + (y.1 - x.1, torusProj (y.2 - x.2)) = spaceTimeProj y := by
    refine Prod.ext (by simp [spaceTimeProj]) ?_
    funext j
    simp [spaceTimeProj, torusProj]
  have e1 := hairerConvolution_xi_eq_hairerPsiField N hξ y
  have e0 := hairerConvolution_xi_eq_hairerPsiField N hξ x
  have eψ : ∀ z : ParabolicSpace, hairerConvolution N
      (fun w => hairerPsiField N ξ ωx (spaceTimeProj w)) z =
      ∫ u, hairerKernelTorus N (spaceTimeProj z - u) * hairerPsiField N ξ ωx u :=
    fun z => hairerConvolution_comp_proj_eq N hc z
  unfold hairerIPsiRecentred gammaPsiTaylor hairerTaylorKernel
  rw [eψ y, eψ x]
  simp only [hrel]
  simp_rw [hairerSpatialGradient_eq_integral_torusGrad N _ hψ x]
  rw [hy]
  have i1 := integrable_hairerKernelTorus_sub_mul_continuous N (spaceTimeProj y) hc
  have i2 := integrable_hairerKernelTorus_sub_mul_continuous N (spaceTimeProj x) hc
  have i3 : ∀ i : Fin 3, Integrable (fun u => (y.2 - x.2) i *
      (hairerKernelTorusGrad N i (spaceTimeProj x - u) * hairerPsiField N ξ ωx u)) := fun i =>
    (integrable_hairerKernelTorusGrad_sub_mul_continuous N i _ hc).const_mul _
  have e : ∀ u, (hairerKernelTorus N (spaceTimeProj y - u) -
        hairerKernelTorus N (spaceTimeProj x - u) -
        ∑ i : Fin 3, hairerKernelTorusGrad N i (spaceTimeProj x - u) * (y.2 - x.2) i) *
        hairerPsiField N ξ ωx u =
      hairerKernelTorus N (spaceTimeProj y - u) * hairerPsiField N ξ ωx u -
        hairerKernelTorus N (spaceTimeProj x - u) * hairerPsiField N ξ ωx u -
        ∑ i : Fin 3, (y.2 - x.2) i *
          (hairerKernelTorusGrad N i (spaceTimeProj x - u) * hairerPsiField N ξ ωx u) := by
    intro u
    rw [sub_mul, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [e]
  have iA : Integrable (fun u => hairerKernelTorus N (spaceTimeProj y - u) *
      hairerPsiField N ξ ωx u - hairerKernelTorus N (spaceTimeProj x - u) *
        hairerPsiField N ξ ωx u) := i1.sub i2
  have iS : Integrable (fun u => ∑ i : Fin 3, (y.2 - x.2) i *
      (hairerKernelTorusGrad N i (spaceTimeProj x - u) * hairerPsiField N ξ ωx u)) :=
    integrable_finsetSum _ fun i _ => i3 i
  rw [integral_sub iA iS, integral_sub i1 i2, integral_finsetSum _ fun i _ => i3 i]
  simp_rw [integral_const_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end RegularityStructures.Phi43

end

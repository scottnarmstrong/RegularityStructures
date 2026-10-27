module

public import GlobalPhi43.MW20.LocalAverageSecondDerivative
public import GlobalPhi43.MW20.HeatFrechet
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Commutation of the source heat operator with local finite-measure averages
-/

public noncomputable section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology Set


local instance : TopologicalSpace (ParabolicSpace →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (ParabolicSpace →L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance : TopologicalSpace (ParabolicSpace →L[ℝ] (ParabolicSpace →L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (ParabolicSpace →L[ℝ] (ParabolicSpace →L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace

local instance : ContinuousENorm (ParabolicSpace →L[ℝ] (ParabolicSpace →L[ℝ] ℝ)) :=
  SeminormedAddGroup.toContinuousENorm
    (E := ParabolicSpace →L[ℝ] (ParabolicSpace →L[ℝ] ℝ))

/-- Heat commutation follows from C² germs on a compact testing tube. No
operator-commutation or smoothness conclusion is assumed as data. -/
theorem sourceHeat_local_average (μ : Measure ParabolicSpace) [IsFiniteMeasure μ]
    (f : ParabolicSpace → ℝ) {K U : Set ParabolicSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hf : ∀ w ∈ K, ContDiffAt ℝ 2 f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : ParabolicSpace} (hx : x ∈ U) :
    sourceHeat (fun z => ∫ y, f (z + y) ∂μ) x = ∫ y, sourceHeat f (x + y) ∂μ := by
  have hf1 : ∀ w ∈ K, ContDiffAt ℝ 1 f w := fun w hw => (hf w hw).of_le (by norm_num)
  have hd1 : ∀ w ∈ K, ContDiffAt ℝ 1 (fderiv ℝ f) w := fun w hw =>
    (hf w hw).fderiv_right (m := 1) (by norm_num)
  have hdf := hasFDerivAt_average_on_open μ f hK hU hf1 htest hx
  have hdd := hasFDerivAt_fderiv_average_on_open μ f hK hU hf htest hx
  have hnear : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ (fun w => ∫ y, f (w + y) ∂μ) z := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hasFDerivAt_average_on_open μ f hK hU hf1 htest hz).differentiableAt
  have hmem : ∀ᵐ y ∂μ, x + y ∈ K := htest.mono fun y hy => hy x hx
  have hi1 : Integrable (fun y => fderiv ℝ f (x + y)) μ :=
    integrable_comp_of_ae_mem_compact μ _ hK
      (fun w hw => (hd1 w hw).continuousAt.continuousWithinAt)
      (fun y => x + y) (continuous_const.add continuous_id) hmem
  have hi2 : Integrable (fun y => fderiv ℝ (fderiv ℝ f) (x + y)) μ := by
    exact integrable_comp_of_ae_mem_compact
      (F := ParabolicSpace →L[ℝ] (ParabolicSpace →L[ℝ] ℝ)) μ _ hK
      (fun w hw => ((hd1 w hw).continuousAt_fderiv one_ne_zero).continuousWithinAt)
      (fun y => x + y) (continuous_const.add continuous_id) hmem
  have hi1t : Integrable (fun y => fderiv ℝ f (x + y) (1, 0)) μ := by
    simpa only using! (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ParabolicSpace)).integrable_comp hi1
  have hi2eval (i : Fin 3) : Integrable (fun y =>
      fderiv ℝ (fderiv ℝ f) (x + y) (0, Pi.single i 1)) μ := by
    exact integrable_comp_of_ae_mem_compact μ _ hK
      (fun w hw => (((hd1 w hw).continuousAt_fderiv one_ne_zero).clm_apply
        continuousAt_const).continuousWithinAt)
      (fun y => x + y) (continuous_const.add continuous_id) hmem
  have hi2s (i : Fin 3) : Integrable (fun y =>
      fderiv ℝ (fderiv ℝ f) (x + y) (0, Pi.single i 1) (0, Pi.single i 1)) μ := by
    exact integrable_comp_of_ae_mem_compact μ _ hK
      (fun w hw => ((((hd1 w hw).continuousAt_fderiv one_ne_zero).clm_apply
        continuousAt_const).clm_apply continuousAt_const).continuousWithinAt)
      (fun y => x + y) (continuous_const.add continuous_id) hmem
  have hisum : Integrable (fun y => ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) (x + y)
      (0, Pi.single i 1) (0, Pi.single i 1)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hi2s i)
  rw [sourceHeat_eq_fderiv _ x hnear hdd.differentiableAt, hdf.fderiv, hdd.fderiv]
  calc
    _ = ∫ y, fderiv ℝ f (x + y) (1, 0) -
        ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) (x + y)
          (0, Pi.single i 1) (0, Pi.single i 1) ∂μ := by
      rw [integral_sub hi1t hisum,
        integral_finsetSum Finset.univ (fun i _ => hi2s i), ContinuousLinearMap.integral_apply hi1]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [ContinuousLinearMap.integral_apply hi2,
        ContinuousLinearMap.integral_apply
          (hi2eval i)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hmem] with y hy
      exact (sourceHeat_eq_fderiv_of_contDiffAt f (x + y) (hf _ hy)).symm

end GlobalPhi43.MW20

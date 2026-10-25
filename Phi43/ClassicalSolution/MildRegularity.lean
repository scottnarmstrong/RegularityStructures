/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MildNonlinearity

/-!
# Finite-window regularity of cubic mild solutions

For the renormalised equation (3.1) of the statement, a continuous
finite-window mild solution with smooth forcing and datum is smooth in the interior and
satisfies the pointwise PDE. Continuity is assumed only on the given window.
The jet-system parabolic bootstrap proves the regularity; it is not a premise.
-/

public noncomputable section

open Set Filter Topology RegularityStructures.PDE

namespace RegularityStructures.Phi43

open scoped ContDiff in
theorem cubic_mildSolution_smooth_and_equation
    (c : ℝ) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (hu₀ : IsSmoothOnTorus u₀) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → C(Torus3, ℝ)}
    (hu : ContinuousOn (fun z : SpaceTime => u z.1 z.2) (Icc 0 T ×ˢ univ))
    (hmild : PDE.IsMildSolution (cubicHeatNonlinearity c hf) u₀ T u) :
    u 0 = u₀ ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
        (Ioo 0 T ×ˢ univ) ∧
      ∀ t ∈ Ioo 0 T, ∀ y : Fin 3 → ℝ,
        deriv (fun s => u s (torusProj y)) t =
          (∑ i, deriv (deriv fun r => u t (torusProj (Function.update y i r))) (y i)) -
            u t (torusProj y) ^ 3 + c * u t (torusProj y) + f (t, torusProj y) := by
  have huc : ContinuousOn u (Icc 0 T) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry u hu
  let U : C(Icc (0 : ℝ) T, C(Torus3, ℝ)) :=
    ⟨fun t => u t, continuousOn_iff_continuous_domRestrict.mp huc⟩
  let v : C(ℝ, C(Torus3, ℝ)) := ContinuousMap.IccExtend hT U
  have hv (t : ℝ) (ht : t ∈ Icc 0 T) : v t = u t := by
    change Set.IccExtend hT U t = u t
    rw [Set.IccExtend_of_mem hT U ht]
    rfl
  have hvm : IsMildSolution (cubicHeatNonlinearity c hf) u₀ T v := by
    intro t ht
    rw [hv t ht, hmild t ht]
    congr 1
    apply duhamel_congr ht.1
    intro s hs
    rw [hv s ⟨hs.1, hs.2.trans ht.2⟩]
  have hsmooth := contDiffOn_of_isMildSolution
    (contDiff_nonlinLift_cubicHeatNonlinearity c hf) hu₀ hT v.continuous hvm
  obtain ⟨w, w2, -, -, hdw, hdw2, hdt⟩ := hasDerivAt_of_isMildSolution
    (contDiff_nonlinLift_cubicHeatNonlinearity c hf) hu₀ hT v.continuous hvm
  refine ⟨?_, ?_, ?_⟩
  · rw [hmild 0 ⟨le_rfl, hT⟩, heatOp_zero_left, duhamel_zero, add_zero]
  · exact hsmooth.congr fun p hp =>
      congrArg (fun g : C(Torus3, ℝ) => g (torusProj p.2)) (hv p.1 (Ioo_subset_Icc_self hp.1)).symm
  · intro t ht y
    have he : (fun s => u s (torusProj y)) =ᶠ[𝓝 t] fun s => v s (torusProj y) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact congrArg (fun g : C(Torus3, ℝ) => g (torusProj y))
        (hv s (Ioo_subset_Icc_self hs)).symm
    rw [he.deriv_eq, (hdt t ht (torusProj y)).deriv, cubicHeatNonlinearity_apply,
      hv t (Ioo_subset_Icc_self ht), torusLap_apply]
    have hsum : (∑ i, w2 t (torusProj y) i i) =
        ∑ i, deriv (deriv fun r => u t (torusProj (Function.update y i r))) (y i) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (deriv_deriv_update_eq (hdw t (Ioo_subset_Icc_self ht))
        (hdw2 t (Ioo_subset_Icc_self ht)) y i).symm
      rwa [hv t (Ioo_subset_Icc_self ht)] at h
    rw [hsum]
    ring

end RegularityStructures.Phi43

end

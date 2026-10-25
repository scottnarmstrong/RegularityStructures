/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGradEuclid
public import Phi43.BPHZ.CanonicalBridgeConvolution
public import Phi43.Structure.CanonicalTaylorSpatial
import Mathlib.Tactic

/-!
# The spatial gradient of `K ∗ g` is the pairing with the gradient kernel

For `g` smooth on `ℝ × T³`, `hairerSpatialGradient N (g ∘ proj) i x = ∫ G_i(proj x - u) g(u) du`
with `G_i = hairerKernelTorusGrad N i` (`hairerSpatialGradient_eq_integral_torusGrad`).  The proof
combines the shell formula `hairerSpatialGradient_eq_tsum_shellPairing`, the exchange of sum and
integral (the shell `L¹` norms are summable), and the periodisation of the Euclidean gradient kernel
(`integral_hairerKernelGrad_comp_proj_eq`, the analogue of `hairerConvolution_comp_proj_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gbr_slice_tsum (N : ℕ) (i : Fin 3) {g : SpaceTime → ℝ} (y : ParabolicSpace)
    (t : ℝ) (u : Torus3) :
    ∑' k : Fin 3 → ℤ, hairerKernelGrad N i (y - (t, torusRep u + fun j => (k j : ℝ))) *
        g (spaceTimeProj (t, torusRep u + fun j => (k j : ℝ))) =
      hairerKernelTorusGrad N i (spaceTimeProj y - (t, u)) * g (t, u) := by
  have hproj : ∀ k : Fin 3 → ℤ, spaceTimeProj (t, torusRep u + fun j => (k j : ℝ)) = (t, u) := by
    intro k
    refine Prod.ext rfl ?_
    funext j
    have h := congrFun (show torusProj (torusRep u) = u by
      funext l; simp [torusProj, torusRep]) j
    simpa [spaceTimeProj, torusProj] using h
  simp_rw [hproj]
  rw [tsum_mul_right]
  congr 1
  set a : Fin 3 → ℝ := y.2 - torusRep u with ha
  have hsub : (spaceTimeProj y - (t, u)).2 = torusProj a := by
    have hu : torusProj (torusRep u) = u := by
      funext l; simp [torusProj, torusRep]
    funext j
    have := congrFun hu j
    simp only [spaceTimeProj, Prod.snd_sub, Pi.sub_apply, torusProj, ha] at this ⊢
    rw [← this]
    simp
  have hfst : (spaceTimeProj y - (t, u)).1 = y.1 - t := rfl
  unfold hairerKernelTorusGrad
  rw [hfst, hsub]
  have h1 := tsum_comp_torusRep_torusProj (fun v => hairerKernelGrad N i (y.1 - t, v)) a
  rw [h1]
  have h2 := (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun k : Fin 3 → ℤ => hairerKernelGrad N i (y.1 - t, a + fun j => (k j : ℝ)))
  rw [← h2]
  refine tsum_congr fun k => ?_
  congr 1
  refine Prod.ext rfl ?_
  funext j
  simp only [ha, Prod.snd_sub, Pi.sub_apply, Pi.add_apply, Equiv.neg_apply, Pi.neg_apply,
    Int.cast_neg]
  ring

/-- The reflected torus gradient kernel times a continuous function is integrable. -/
theorem integrable_hairerKernelTorusGrad_sub_mul_continuous (N : ℕ) (i : Fin 3) (z : SpaceTime)
    {g : SpaceTime → ℝ} (hg : Continuous g) :
    Integrable (fun u => hairerKernelTorusGrad N i (z - u) * g u) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := z.1 - 1)
    (b := z.1 + 1)).prod (isCompact_univ (X := Torus3)) |>.exists_bound_of_continuousOn
      hg.continuousOn
  have hK := integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i)
    z
  refine (hK.abs.mul_const C).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact (((measurable_hairerKernelTorusGrad N i).comp
      (measurable_const.sub measurable_id)).mul hg.measurable).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hw : 1 < |(z - w).1|
    · rw [hairerKernelTorusGrad_eq_zero_of_one_lt_time N i hw]
      simp
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hmem : w ∈ Set.Icc (z.1 - 1) (z.1 + 1) ×ˢ
          (Set.univ : Set Torus3) := by
        refine ⟨?_, Set.mem_univ _⟩
        have h2 := abs_le.1 (not_lt.1 hw)
        simp only [Set.mem_Icc, Prod.fst_sub] at h2 ⊢
        constructor <;> linarith [h2.1, h2.2]
      simpa using hC _ hmem

/-- **Periodisation of the gradient kernel.**  For continuous `g` on `ℝ × T³`,
`∫_{ℝ⁴} G_i(y - w) g(proj w) dw = ∫_{ℝ × T³} G♯_i(proj y - u) g(u) du`. -/
theorem integral_hairerKernelGrad_comp_proj_eq {g : SpaceTime → ℝ} (N : ℕ) (i : Fin 3)
    (hg : Continuous g) (y : ParabolicSpace) :
    ∫ w, hairerKernelGrad N i (y - w) * g (spaceTimeProj w) =
      ∫ u, hairerKernelTorusGrad N i (spaceTimeProj y - u) * g u := by
  have hF := integrable_hairerKernelGrad_sub_mul_continuous N i y
    (f := fun w => g (spaceTimeProj w)) (hg.comp continuous_spaceTimeProj)
  have hΦ := integrable_hairerKernelTorusGrad_sub_mul_continuous N i (spaceTimeProj y) hg
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod, integral_prod _ hF, integral_prod _ hΦ]
  have hFp : Integrable (fun w : ParabolicSpace => hairerKernelGrad N i (y - w) *
      g (spaceTimeProj w)) (volume.prod volume) := by
    rwa [← Measure.volume_eq_prod]
  refine integral_congr_ae ?_
  filter_upwards [hFp.prod_right_ae] with t ht
  rw [integral_eq_integral_torus_tsum (H := fun x => hairerKernelGrad N i (y - (t, x)) *
    g (spaceTimeProj (t, x))) ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact gbr_slice_tsum N i y t u

end RegularityStructures.Phi43

end

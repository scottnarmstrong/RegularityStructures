/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeKernel
public import Phi43.BPHZ.CanonicalBridgePeriodise
public import Phi43.BPHZ.PsiGaussianVectorContinuous
public import Phi43.BPHZ.TreeI3PsiField

/-!
# Periodisation of the Hairer convolution

Let `proj y = (y.1, torusProj y.2)` be the projection `ℝ × ℝ³ → ℝ × T³`.  For a continuous
`g : ℝ × T³ → ℝ` with periodic lift `g ∘ proj`, convolution with the Euclidean kernel
`hairerKernel N` on `ℝ⁴` agrees with convolution with the periodised kernel `hairerKernelTorus N`
on `ℝ × T³`:
`∫_{ℝ⁴} K(y - w) g(proj w) dw = ∫_{ℝ × T³} K^♯(proj y - u) g(u) du`.
Hence `hairerConvolution N (ξ ∘ proj) y = hairerPsiField N ξ ω (proj y)`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The projection `ℝ × ℝ³ → ℝ × T³`, `y ↦ (y.1, torusProj y.2)`. -/
def spaceTimeProj (y : ParabolicSpace) : SpaceTime := (y.1, torusProj y.2)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem continuous_spaceTimeProj : Continuous spaceTimeProj :=
  isOpenQuotientMap_spaceTimeProj.continuous

/-- `proj` is additive. -/
theorem spaceTimeProj_sub (y w : ParabolicSpace) :
    spaceTimeProj (y - w) = spaceTimeProj y - spaceTimeProj w := by
  refine Prod.ext rfl ?_
  funext i
  simp [spaceTimeProj, torusProj]

/-- The time slice of the unfolding identity: for fixed `t`, the sum of the lattice translates of
the kernel against the periodic lift equals the torus convolution. -/
private theorem bridge_slice_tsum (N : ℕ) {g : SpaceTime → ℝ} (y : ParabolicSpace) (t : ℝ)
    (u : Torus3) :
    ∑' k : Fin 3 → ℤ, hairerKernel N (y - (t, torusRep u + fun i => (k i : ℝ))) *
        g (spaceTimeProj (t, torusRep u + fun i => (k i : ℝ))) =
      hairerKernelTorus N (spaceTimeProj y - (t, u)) * g (t, u) := by
  have hproj : ∀ k : Fin 3 → ℤ, spaceTimeProj (t, torusRep u + fun i => (k i : ℝ)) = (t, u) := by
    intro k
    refine Prod.ext rfl ?_
    funext i
    have h := congrFun (show torusProj (torusRep u) = u by
      funext j; simp [torusProj, torusRep]) i
    simpa [spaceTimeProj, torusProj] using h
  simp_rw [hproj]
  rw [tsum_mul_right]
  congr 1
  set a : Fin 3 → ℝ := y.2 - torusRep u with ha
  have hsub : (spaceTimeProj y - (t, u)).2 = torusProj a := by
    have hu : torusProj (torusRep u) = u := by
      funext j; simp [torusProj, torusRep]
    funext i
    have := congrFun hu i
    simp only [spaceTimeProj, Prod.snd_sub, Pi.sub_apply, torusProj, ha] at this ⊢
    rw [← this]
    simp
  have hfst : (spaceTimeProj y - (t, u)).1 = y.1 - t := rfl
  unfold hairerKernelTorus
  rw [hfst, hsub]
  have h1 := tsum_comp_torusRep_torusProj (fun v => hairerKernel N (y.1 - t, v)) a
  rw [h1]
  have h2 := (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun k : Fin 3 → ℤ => hairerKernel N (y.1 - t, a + fun i => (k i : ℝ)))
  rw [← h2]
  refine tsum_congr fun k => ?_
  congr 1
  refine Prod.ext rfl ?_
  funext i
  simp only [ha, Prod.snd_sub, Pi.sub_apply, Pi.add_apply, Equiv.neg_apply, Pi.neg_apply, Int.cast_neg]
  ring

/-- **Periodisation identity.**  For continuous `g` on `ℝ × T³`,
`∫_{ℝ⁴} K(y - w) g(proj w) dw = ∫_{ℝ × T³} K^♯(proj y - u) g(u) du`. -/
theorem hairerConvolution_comp_proj_eq {g : SpaceTime → ℝ} (N : ℕ) (hg : Continuous g)
    (y : ParabolicSpace) :
    hairerConvolution N (fun w => g (spaceTimeProj w)) y =
      ∫ u, hairerKernelTorus N (spaceTimeProj y - u) * g u := by
  have hF := integrable_hairerKernel_sub_mul_continuous N y
    (f := fun w => g (spaceTimeProj w)) (hg.comp continuous_spaceTimeProj)
  have hΦ := integrable_hairerKernelTorus_sub_mul_continuous N (spaceTimeProj y) hg
  unfold hairerConvolution
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod, integral_prod _ hF, integral_prod _ hΦ]
  have hFp : Integrable (fun w : ParabolicSpace => hairerKernel N (y - w) *
      g (spaceTimeProj w)) (volume.prod volume) := by
    rwa [← Measure.volume_eq_prod]
  refine integral_congr_ae ?_
  filter_upwards [hFp.prod_right_ae] with t ht
  rw [integral_eq_integral_torus_tsum (H := fun x => hairerKernel N (y - (t, x)) *
    g (spaceTimeProj (t, x))) ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact bridge_slice_tsum N y t u

end RegularityStructures.Phi43

end

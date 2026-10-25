/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiMoment
public import Phi43.Stochastic.ConstantsComparisonKernelLp

/-!
# Continuity of the tree `Ψ` in space-time

A smooth function on `ℝ × T³` is continuous, the kernel `K` vanishes for `|t| > 1`, and so
`z ↦ ∫ K(z - w) ξ(w) dw` is continuous whenever `ξ` is.  Together with
`measurable_hairerPsiField_uncurry` this gives a jointly measurable field with continuous paths.
-/

public section

open MeasureTheory Topology

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The projection `ℝ × ℝ³ → ℝ × T³` is an open quotient map. -/
theorem isOpenQuotientMap_spaceTimeProj :
    IsOpenQuotientMap (fun p : ℝ × (Fin 3 → ℝ) => ((p.1, torusProj p.2) : SpaceTime)) := by
  have h : IsOpenQuotientMap (Pi.map fun _ : Fin 3 =>
      (fun y : ℝ => ((y : ℝ) : UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact IsOpenQuotientMap.id.prodMap h

/-- A smooth function on space-time is continuous. -/
theorem IsSmoothOnSpaceTime.continuous {g : SpaceTime → ℝ} (hg : IsSmoothOnSpaceTime g) :
    Continuous g := by
  have h := isOpenQuotientMap_spaceTimeProj
  exact h.isQuotientMap.continuous_iff.2 hg.continuous

/-- The torus kernel vanishes for time displacement larger than one. -/
theorem hairerKernelTorus_eq_zero_of_one_lt_time (N : ℕ) {z : SpaceTime} (hz : 1 < |z.1|) :
    hairerKernelTorus N z = 0 := by
  unfold hairerKernelTorus
  have hk : ∀ k : Fin 3 → ℤ, hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
    intro k
    unfold hairerKernel
    have hnorm : 1 < parabolicNorm (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
      unfold parabolicNorm
      have h1 : 1 < √|z.1| := by
        rw [Real.lt_sqrt zero_le_one]
        simpa using hz
      have h2 : 0 ≤ ∑ i, |(torusRep z.2 + fun i => (k i : ℝ)) i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      simp only
      linarith
    have hzero : ∀ n, annShellC N n (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
      intro n
      apply annShellC_eq_zero
      exact lt_of_le_of_lt (pow_le_one₀ (by positivity) (by norm_num)) hnorm
    rw [tsum_eq_sum (s := (∅ : Finset ℕ)) (fun n _ => hzero n)]
    simp
  simp only [hk]
  exact tsum_zero

/-- The kernel convolution `z ↦ ∫ K(z - w) g(w) dw` of a continuous `g` is continuous. -/
theorem continuous_hairerKernelTorus_convolution (N : ℕ) {g : SpaceTime → ℝ}
    (hg : Continuous g) : Continuous (fun z => ∫ w, hairerKernelTorus N (z - w) * g w) := by
  have hrw : ∀ z : SpaceTime, ∫ w, hairerKernelTorus N (z - w) * g w =
      ∫ w, hairerKernelTorus N w * g (z - w) := by
    intro z
    have h := integral_comp_sub_left_spaceTime
      (fun v => hairerKernelTorus N v * g (z - v)) z
    simp only [sub_sub_cancel] at h
    exact h
  simp_rw [hrw]
  refine continuous_iff_continuousAt.2 fun z0 => ?_
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := z0.1 - 2) (b := z0.1 + 2)).prod
    (isCompact_univ (X := Torus3)) |>.exists_bound_of_continuousOn hg.continuousOn
  have hnhd : ∀ᶠ z in 𝓝 z0, |z.1 - z0.1| < 1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  have hK := integrable_constantsComparison_hairerKernelTorus N
  refine continuousAt_of_dominated (bound := fun w => |hairerKernelTorus N w| * C) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      (measurable_constantsComparison_hairerKernelTorus N |>.mul
        (hg.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · filter_upwards [hnhd] with z hz
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hw : 1 < |w.1|
    · rw [hairerKernelTorus_eq_zero_of_one_lt_time N hw]
      simp
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hmem : z - w ∈ Set.Icc (z0.1 - 2) (z0.1 + 2) ×ˢ (Set.univ : Set Torus3) := by
        refine ⟨?_, Set.mem_univ _⟩
        have h1 := abs_lt.1 hz
        have h2 := abs_le.1 (not_lt.1 hw)
        simp only [Set.mem_Icc, Prod.fst_sub]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      simpa using hC _ hmem
  · exact hK.abs.mul_const C
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (continuous_const.mul (hg.comp (continuous_id.sub continuous_const))).continuousAt

/-- **Continuous paths of `Ψ`.** If `ξ ω` is smooth then `z ↦ Ψ(ω, z)` is continuous. -/
theorem continuous_hairerPsiField {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} (N : ℕ)
    (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) :
    Continuous (hairerPsiField N ξ ω) :=
  continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous (hξ ω))

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelRegularity
import RegularityStructures.Torus.KernelBoundsDerivative

/-!
# Joint continuity away from the initial-time singularity

The periodised Gaussian is jointly continuous for positive time. Uniform convergence on
compact positive-time cylinders follows from the Gaussian lattice majorant. Consequently the
massive kernel of equation (2.2) of the statement is continuous off the time-zero slice.
These are analytic inputs for the pathwise construction of the stationary linear field.
-/

public section

open Real Set
open scoped Topology

namespace RegularityStructures

private theorem joint_gaussian_continuousAt {z : ℝ × (Fin 3 → ℝ)} (hz : 0 < z.1) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => gaussKernel p.1 p.2) z := by
  exact contDiffOn_gaussKernelSpaceTime.continuousOn.continuousAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)

private theorem gaussian_cylinder_majorant {a b t : ℝ} (ha : 0 < a)
    (ht : t ∈ Icc a b) {y : Fin 3 → ℝ} (hy : ∀ i, y i ∈ Icc (-1 : ℝ) 2)
    (k : Fin 3 → ℤ) :
    ‖gaussKernel t (y + fun i => (k i : ℝ))‖ ≤
      (4 * π * a) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * b)⁻¹) (k i) := by
  have ht0 := ha.trans_le ht.1
  have hb0 := ht0.trans_le ht.2
  rw [Real.norm_of_nonneg (gaussKernel_nonneg ht0 _), gaussKernel_eq_prod]
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left ht.1 (by positivity)) (by norm_num)
  · apply Finset.prod_le_prod₀ (fun i _ => exp_nonneg _)
    intro i _
    apply le_trans _ (gaussian_exp_shift_le_majorant (by positivity) (hy i) (k i))
    apply exp_le_exp.mpr
    have hinv : (4 * b)⁻¹ ≤ (4 * t)⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left ht.2 (by norm_num))
    exact mul_le_mul_of_nonneg_right (neg_le_neg hinv) (sq_nonneg _)
  · exact Finset.prod_nonneg fun _ _ => exp_nonneg _
  · exact rpow_nonneg (by positivity) _

private theorem joint_lift_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => heatKernelLift p.1 p.2)
      (Icc a b ×ˢ pi univ (fun _ : Fin 3 => Icc (-1 : ℝ) 2)) := by
  by_cases hab : a ≤ b
  · have hb := ha.trans_le hab
    apply continuousOn_tsum (u := fun k : Fin 3 → ℤ =>
      (4 * π * a) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * b)⁻¹) (k i))
    · intro k p hp
      have hc : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) =>
          (q.1, q.2 + fun i => (k i : ℝ))) p :=
        continuousAt_fst.prodMk (continuousAt_snd.add continuousAt_const)
      exact ((joint_gaussian_continuousAt (z := (p.1, p.2 + fun i => (k i : ℝ)))
        (ha.trans_le hp.1.1)).comp (f := fun q : ℝ × (Fin 3 → ℝ) =>
          (q.1, q.2 + fun i => (k i : ℝ))) hc).continuousWithinAt
    · exact (summable_pi_fin3_prod
        (summable_gaussianOneDimMajorant (by positivity))
        gaussianOneDimMajorant_nonneg).mul_left ((4 * π * a) ^ (-(3 : ℝ) / 2))
    · intro k p hp
      exact gaussian_cylinder_majorant ha hp.1
        (fun i => mem_pi.mp hp.2 i (mem_univ i)) k
  · have he : Icc a b = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp only [he, empty_prod, continuousOn_empty]

private theorem joint_lift_continuousAt_cube {t : ℝ} (ht : 0 < t)
    {y : Fin 3 → ℝ} (hy : ∀ i, y i ∈ Ico (0 : ℝ) 1) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => heatKernelLift p.1 p.2) (t, y) := by
  apply (joint_lift_continuousOn (b := 2 * t) (show 0 < t / 2 by linarith)).continuousAt
  have htI : Icc (t / 2) (2 * t) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hyI : pi univ (fun _ : Fin 3 => Icc (-1 : ℝ) 2) ∈ 𝓝 y := by
    apply Filter.mem_of_superset
      ((isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)).mem_nhds
        (show y ∈ pi univ (fun _ : Fin 3 => Ioo (-1 : ℝ) 2) from
          mem_pi.mpr fun i _ => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩))
    exact pi_mono fun _ _ _ hz => ⟨hz.1.le, hz.2.le⟩
  rw [nhds_prod_eq]
  exact Filter.prod_mem_prod htI hyI

private theorem joint_lift_continuousAt {z : ℝ × (Fin 3 → ℝ)} (hz : 0 < z.1) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => heatKernelLift p.1 p.2) z := by
  let m : Fin 3 → ℤ := fun i => ⌊z.2 i⌋
  let r : Fin 3 → ℝ := z.2 - fun i => (m i : ℝ)
  have hr : ∀ i, r i ∈ Ico (0 : ℝ) 1 := by
    intro i
    exact ⟨sub_nonneg.mpr (Int.floor_le _), by
      change z.2 i - (⌊z.2 i⌋ : ℝ) < 1
      linarith [Int.lt_floor_add_one (z.2 i)]⟩
  have hshift : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      (p.1, p.2 - fun i => (m i : ℝ))) z :=
    continuousAt_fst.prodMk (continuousAt_snd.sub continuousAt_const)
  have hc := (joint_lift_continuousAt_cube hz hr).comp
    (f := fun p : ℝ × (Fin 3 → ℝ) => (p.1, p.2 - fun i => (m i : ℝ))) hshift
  apply hc.congr
  apply Filter.Eventually.of_forall
  intro p
  change heatKernelLift p.1 (p.2 - fun i => (m i : ℝ)) = heatKernelLift p.1 p.2
  have he := heatKernelLift_add_integer (t := p.1) m (p.2 - fun i => (m i : ℝ))
  simpa only [sub_add_cancel] using he.symm

/-- Joint continuity of the torus heat kernel on strictly positive times. -/
theorem continuousAt_heatKernel_positive {z : SpaceTime} (hz : 0 < z.1) :
    ContinuousAt (fun p : SpaceTime => heatKernel p.1 p.2) z := by
  have hq : IsOpenQuotientMap torusProj := by
    change IsOpenQuotientMap (Pi.map (fun _ : Fin 3 => QuotientAddGroup.mk))
    exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have hprod : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) torusProj) :=
    IsOpenQuotientMap.id.prodMap hq
  have hc : ContinuousAt ((fun p : SpaceTime => heatKernel p.1 p.2) ∘
      Prod.map id torusProj) (z.1, torusRep z.2) := by
    change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => heatKernel p.1 (torusProj p.2)) _
    simp_rw [heatKernel_comp_torusProj_eq_lift]
    exact joint_lift_continuousAt hz
  have he : torusProj (torusRep z.2) = z.2 := by
    funext i
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := z.2 i)
  simpa only [Prod.map_apply, id_eq, he, Prod.eta] using hprod.continuousAt_comp_iff.mp hc

/-- The massive heat kernel is jointly continuous off the time-zero slice. -/
theorem continuousAt_massiveHeatKernel_time_ne_zero {z : SpaceTime} (hz : z.1 ≠ 0) :
    ContinuousAt massiveHeatKernel z := by
  classical
  rcases hz.lt_or_gt with hneg | hpos
  · apply (continuousAt_const : ContinuousAt (fun _ : SpaceTime => (0 : ℝ)) z).congr
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Iio_mem_nhds hneg)] with p hp
    simp only [massiveHeatKernel, not_lt.mpr hp.le, ↓reduceIte]
  · have hexp : ContinuousAt (fun p : SpaceTime => exp (-p.1)) z :=
      continuous_exp.continuousAt.comp continuousAt_fst.neg
    have hc : ContinuousAt (fun p : SpaceTime => exp (-p.1) * heatKernel p.1 p.2) z :=
      hexp.mul (continuousAt_heatKernel_positive hpos)
    apply hc.congr
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds hpos)] with p hp
    have hp' : 0 < p.1 := hp
    simp only [massiveHeatKernel, hp', ↓reduceIte]

end RegularityStructures

end

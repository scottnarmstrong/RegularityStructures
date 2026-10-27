module

public import GlobalPhi43.MW20.SourceHolder
public import GlobalPhi43.MW20.CubicRegularity
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Finiteness of the actual source Hölder seminorm from local regularity
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The closed inset cylinder used only for compact derivative bounds. -/
@[expose] def sourceClosedInset (R : ℝ) : Set ParabolicSpace :=
  Icc ((R ^ 2 : ℝ), fun _ => -1 + R) ((1 : ℝ), fun _ => 1 - R)

/-- Every open source inset lies in its compact closure. -/
theorem sourceCylinder_subset_closedInset (R : ℝ) :
    sourceCylinder R ⊆ sourceClosedInset R := by
  intro z hz
  exact ⟨⟨hz.1.le, fun i => by linarith [(abs_lt.mp (hz.2.2 i)).1]⟩,
    ⟨hz.2.1.le, fun i => (abs_lt.mp (hz.2.2 i)).2.le⟩⟩

/-- The source C² germs apply throughout every strictly positive closed inset. -/
theorem SourceCubicRegularity.contDiffAt_closedInset {v : ParabolicSpace → ℝ}
    (hv : SourceCubicRegularity v) {R : ℝ} (hR : 0 < R)
    {z : ParabolicSpace} (hz : z ∈ sourceClosedInset R) : ContDiffAt ℝ 2 v z := by
  apply hv.twice z
  · exact (sq_pos_of_pos hR).trans_le hz.1.1
  · exact hz.2.1
  · intro i
    exact ⟨by linarith [hz.1.2 i], by linarith [hz.2.2 i]⟩

/-- Local classical regularity implies an ordinary Lipschitz bound on each
closed inset, by compact derivative control and the mean value theorem. -/
theorem SourceCubicRegularity.exists_inset_lipschitz {v : ParabolicSpace → ℝ}
    (hv : SourceCubicRegularity v) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ sourceClosedInset R, ∀ y ∈ sourceClosedInset R,
      |v y - v x| ≤ C * ‖y - x‖ := by
  have hc : ContinuousOn (fun z => ‖fderiv ℝ v z‖) (sourceClosedInset R) := by
    intro z hz
    exact ((hv.contDiffAt_closedInset hR hz).continuousAt_fderiv (by norm_num)).norm.continuousWithinAt
  have hb : BddAbove ((fun z => ‖fderiv ℝ v z‖) '' sourceClosedInset R) :=
    (isCompact_Icc.image_of_continuousOn hc).bddAbove
  obtain ⟨B, hB⟩ := hb
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hd : ∀ z ∈ sourceClosedInset R, DifferentiableAt ℝ v z := fun z hz =>
    (hv.contDiffAt_closedInset hR hz).differentiableAt (by norm_num)
  have hbound : ∀ z ∈ sourceClosedInset R, ‖fderiv ℝ v z‖ ≤ max B 0 :=
    fun z hz => (hB ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hconv : Convex ℝ (sourceClosedInset R) := by
    intro p hp q hq a b ha hb hab
    have ht := (convex_Icc (R ^ 2) (1 : ℝ))
      ⟨hp.1.1, hp.2.1⟩ ⟨hq.1.1, hq.2.1⟩ ha hb hab
    have hs := fun i : Fin 3 => (convex_Icc (-1 + R) (1 - R))
      ⟨hp.1.2 i, hp.2.2 i⟩ ⟨hq.1.2 i, hq.2.2 i⟩ ha hb hab
    exact ⟨⟨ht.1, fun i => (hs i).1⟩, ⟨ht.2, fun i => (hs i).2⟩⟩
  simpa only [Real.norm_eq_abs] using
    hconv.norm_image_sub_le_of_norm_fderiv_le hd hbound hx hy

/-- The literal source seminorm is finite on every strictly positive inset
at exponent α≤1 and radius at most one. -/
theorem sourceHolder_bddAbove_of_regularity {v : ParabolicSpace → ℝ}
    (hv : SourceCubicRegularity v) {α R L : ℝ}
    (hR : 0 < R) (hα1 : α ≤ 1) (hL : L ≤ 1) :
    BddAbove (sourceHolderValues v α R L) := by
  obtain ⟨C, hC, hLip⟩ := hv.exists_inset_lipschitz hR
  refine ⟨C, ?_⟩
  rintro q (hq | ⟨x, hx, y, hy, hp, hxy, rfl⟩)
  · simpa only [Set.mem_singleton_iff.mp hq] using hC
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos hp α)).2
    have hl := hLip x (sourceCylinder_subset_closedInset R hx)
      y (sourceCylinder_subset_closedInset R hy)
    have hn : ‖y - x‖ ≤ Local.pdist x y := by
      rw [norm_sub_rev]
      exact norm_sub_le_pdist (hxy.trans hL)
    have hr : Local.pdist x y ≤ Local.pdist x y ^ α := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hp (hxy.trans hL) hα1
    exact hl.trans ((mul_le_mul_of_nonneg_left hn hC).trans
      (mul_le_mul_of_nonneg_left hr hC))

end GlobalPhi43.MW20

module

public import GlobalPhi43.MW20.CubicRegularity
public import GlobalPhi43.MW20.LocalComparison

/-!
# Cubic comparison with the explicit boundary barrier
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- On a finite truncation, the reciprocal barrier dominates every cubic
subsolution whose parabolic boundary values lie below it. -/
theorem le_cubicBarrier_on_truncation {u : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u)
    {δ T G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G) (hT : T ≤ 1)
    (hbd : ∀ z ∈ truncatedCylinder δ T,
      (z.1 = δ ^ 2 ∨ ∃ i, z.2 i = -1 + δ ∨ z.2 i = 1 - δ) → u z ≤ cubicBarrier G z)
    (hpde : ∀ z ∈ truncatedCylinder δ T, sourceHeat u z + u z ^ 3 ≤ G ^ 3) :
    ∀ z ∈ truncatedCylinder δ T, u z ≤ cubicBarrier G z := by
  have hc : ContinuousOn (fun z => u z - cubicBarrier G z) (truncatedCylinder δ T) := by
    intro z hz
    have hi := truncatedCylinder_interior hδ hz
    exact ((hu.twice z hi.1 (hz.2.1.trans hT) hi.2).sub (cubicBarrier_contDiffAt G z hi.1 hi.2)).continuousAt.continuousWithinAt
  have hnonpos := nonpos_of_sourceHeat_neg hc
    (fun z hz hb => sub_nonpos.mpr (hbd z hz hb))
    (fun z hz _ _ => time_differentiable_of_contDiffAt
      ((hu.twice z (truncatedCylinder_interior hδ hz).1 (hz.2.1.trans hT)
        (truncatedCylinder_interior hδ hz).2).sub (cubicBarrier_contDiffAt G z
        (truncatedCylinder_interior hδ hz).1 (truncatedCylinder_interior hδ hz).2))) ?_
  · intro z hz
    exact sub_nonpos.mp (hnonpos z hz)
  · intro z hz _ _ hp
    have hi := truncatedCylinder_interior hδ hz
    rw [sourceHeat_sub_of_contDiffAt z (hu.twice z hi.1 (hz.2.1.trans hT) hi.2) (cubicBarrier_contDiffAt G z hi.1 hi.2)]
    have hsup := cubicBarrier_supersolution G hG z hi.1 hi.2
    have hB := cubicBarrier_nonneg hG z hi.2
    have hcube : cubicBarrier G z ^ 3 < u z ^ 3 :=
      pow_lt_pow_left₀ (sub_pos.mp hp) hB (by norm_num : (3 : ℕ) ≠ 0)
    linarith [hpde z hz]

/-- Positive-part version of Lemma 2.7 below the terminal time. The boundary
values of u enter only the choice of finite truncation, not the bound. -/
theorem le_cubicBarrier_of_source_cubic {u : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u)
    {G : ℝ} (hG : 0 ≤ G)
    (hpde : ∀ z ∈ sourceCylinder 0, sourceHeat u z + u z ^ 3 ≤ G ^ 3)
    (z : ParabolicSpace) {ρ : ℝ} (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ z.1) (ht1 : z.1 < 1)
    (hx : ∀ i, ρ ≤ 1 - z.2 i ∧ ρ ≤ 1 + z.2 i) : u z ≤ cubicBarrier G z := by
  have hb : BddAbove ((fun y => |u y|) '' sourceClosedCylinder) :=
    (isCompact_Icc.image_of_continuousOn hu.continuous.abs).bddAbove
  obtain ⟨M, hM⟩ := hb
  obtain ⟨δ, hδ, hδρ, hMδ⟩ := exists_barrier_inset M hρ
  have hzK : z ∈ truncatedCylinder δ z.1 := by
    refine ⟨⟨by nlinarith, ?_⟩, ⟨le_rfl, ?_⟩⟩
    · intro i; linarith [(hx i).2]
    · intro i; linarith [(hx i).1]
  have hK (y : ParabolicSpace) (hy : y ∈ truncatedCylinder δ z.1) : y ∈ sourceCylinder 0 := by
    have hi := truncatedCylinder_interior hδ hy
    refine ⟨by simpa using hi.1, hy.2.1.trans_lt ht1, ?_⟩
    intro i
    simpa only [sub_zero] using abs_lt.mpr (hi.2 i)
  apply le_cubicBarrier_on_truncation hu hδ hG ht1.le ?_ (fun y hy => hpde y (hK y hy)) z hzK
  intro y hy hbd
  have hyclosed := sourceCylinder_subset_closed (by norm_num : (0 : ℝ) ≤ 0) (hK y hy)
  exact (le_abs_self (u y)).trans ((hM ⟨y, hyclosed, rfl⟩).trans
    (hMδ.trans (cubicBarrier_ge_boundary hδ hG hy hbd)))

end GlobalPhi43.MW20

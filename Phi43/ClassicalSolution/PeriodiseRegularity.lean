/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.Periodise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

/-!
# Regularity of the periodised mollifier

The compact support of a mollifier makes its spatial lattice sum locally finite.  We first prove
this as a statement about a function on `ℝ × ℝ³`; the periodic lift of `periodise` is then a
locally finite sum of smooth functions.  The support and boundedness statements are the analytic
facts used for the mollified covariance (item (W3) of Lemma 4.1 of the statement).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff
open scoped Topology

namespace RegularityStructures

namespace Phi43

/-- The spatial lattice sum of a function on space-time, before passing to the torus quotient. -/
def latticePeriodise (f : (ℝ × (Fin 3 → ℝ)) → ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ∑' k : Fin 3 → ℤ, f (z.1, z.2 + fun i => (k i : ℝ))

theorem latticePeriodise_add_integer (f : (ℝ × (Fin 3 → ℝ)) → ℝ) (m : Fin 3 → ℤ)
    (z : ℝ × (Fin 3 → ℝ)) :
    latticePeriodise f (z.1, z.2 + fun i => (m i : ℝ)) = latticePeriodise f z := by
  unfold latticePeriodise
  calc
    (∑' k : Fin 3 → ℤ,
        f (z.1, (z.2 + fun i => (m i : ℝ)) + fun i => (k i : ℝ))) =
        ∑' k : Fin 3 → ℤ,
          f (z.1, z.2 + fun i => (m i : ℝ) + (k i : ℝ)) := by
      apply tsum_congr
      intro k
      congr 2
      funext i
      simp only [Pi.add_apply]
      ring
    _ = ∑' k : Fin 3 → ℤ, f (z.1, z.2 + fun i => (k i : ℝ)) := by
      simpa [Equiv.addRight, Int.cast_add, add_comm, add_left_comm, add_assoc] using
        (Equiv.addRight m).tsum_eq
          (fun k : Fin 3 → ℤ => f (z.1, z.2 + fun i => (k i : ℝ)))

theorem periodise_comp_torusProj_eq_latticePeriodise
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    periodise ρ ε (z.1, torusProj z.2) = latticePeriodise (rescale ρ ε) z := by
  let r := torusRep (torusProj z.2)
  have hcoord : ∀ i, ∃ m : ℤ, z.2 i = r i + (m : ℝ) := by
    intro i
    have hi : ((r i : ℝ) : UnitAddCircle) = (z.2 i : UnitAddCircle) := by
      dsimp [r, torusRep, torusProj]
      exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
        (y := (z.2 i : UnitAddCircle))
    have himem : r i - z.2 i ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem.mp hi)
    rcases AddSubgroup.mem_zmultiples_iff.mp himem with ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    have hm' : (m : ℝ) = r i - z.2 i := by simpa using hm
    rw [Int.cast_neg]
    linarith
  choose m hm using hcoord
  have hym : z.2 = r + fun i => (m i : ℝ) := by
    funext i
    exact hm i
  unfold periodise
  rw [show torusRep (torusProj z.2) = r by rfl]
  calc
    (∑' k : Fin 3 → ℤ,
        rescale ρ ε (z.1, r + fun i => (k i : ℝ))) =
        latticePeriodise (rescale ρ ε) (z.1, r) := by rfl
    _ = latticePeriodise (rescale ρ ε)
        (z.1, r + fun i => (m i : ℝ)) :=
      (latticePeriodise_add_integer (rescale ρ ε) m (z.1, r)).symm
    _ = latticePeriodise (rescale ρ ε) z := by
      congr 1
      rw [← Prod.eta z, hym]

theorem latticePeriodise_eq_finset_sum_on_nhds
    (f : (ℝ × (Fin 3 → ℝ)) → ℝ)
    (hf : IsCompact (tsupport f)) (z : ℝ × (Fin 3 → ℝ)) :
    ∃ U ∈ 𝓝 z, ∃ s : Finset (Fin 3 → ℤ),
      ∀ p ∈ U, latticePeriodise f p =
        ∑ k ∈ s, f (p.1, p.2 + fun i => (k i : ℝ)) := by
  classical
  let K := tsupport f
  choose A hA using fun i : Fin 3 =>
    (hf.image ((continuous_apply i).comp continuous_snd)).bddBelow
  choose B hB using fun i : Fin 3 =>
    (hf.image ((continuous_apply i).comp continuous_snd)).bddAbove
  let lo : Fin 3 → ℤ := fun i => ⌈A i - z.2 i - 1⌉
  let hi : Fin 3 → ℤ := fun i => ⌊B i - z.2 i + 1⌋
  let Sset : Set (Fin 3 → ℤ) :=
    Set.pi Set.univ (fun i => (Finset.Icc (lo i) (hi i) : Set ℤ))
  have hSfinite : Sset.Finite := by
    apply Set.Finite.pi
    intro i
    exact (Finset.Icc (lo i) (hi i)).finite_toSet
  let s : Finset (Fin 3 → ℤ) := hSfinite.toFinset
  let U : Set (ℝ × (Fin 3 → ℝ)) :=
    Set.univ.prod (Set.pi Set.univ (fun i => Set.Ioo (z.2 i - 1) (z.2 i + 1)))
  have hUopen : IsOpen U := by
    exact isOpen_univ.prod (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))
  have hzU : z ∈ U := by
    apply Set.mem_prod.mpr
    constructor
    · exact mem_univ _
    · apply Set.mem_pi.mpr
      intro i hi
      simp
  have hUnhds : U ∈ 𝓝 z := hUopen.mem_nhds hzU
  refine ⟨U, hUnhds, s, ?_⟩
  intro p hp
  apply tsum_eq_sum
  intro k hk
  by_contra hterm
  have harg : (p.1, p.2 + fun i => (k i : ℝ)) ∈ K := by
    by_contra harg
    exact hterm (image_eq_zero_of_notMem_tsupport harg)
  have hkmem : k ∈ Sset := by
    apply Set.mem_pi.mpr
    intro i hi_mem
    apply Finset.mem_Icc.mpr
    have hpi : p.2 i ∈ Set.Ioo (z.2 i - 1) (z.2 i + 1) :=
      (Set.mem_pi.mp hp.2) i (Set.mem_univ i)
    have hlower : A i ≤ p.2 i + (k i : ℝ) := by
      exact hA i ⟨(p.1, p.2 + fun j => (k j : ℝ)), harg, rfl⟩
    have hupper : p.2 i + (k i : ℝ) ≤ B i := by
      exact hB i ⟨(p.1, p.2 + fun j => (k j : ℝ)), harg, rfl⟩
    constructor
    · dsimp [lo]
      apply Int.ceil_le.mpr
      linarith [hpi.2]
    · dsimp [hi]
      apply Int.le_floor.mpr
      linarith [hpi.1]
  apply hk
  exact hSfinite.mem_toFinset.mpr hkmem

theorem contDiff_rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (_hε : 0 < ε) : ContDiff ℝ ∞ (rescale ρ ε) := by
  unfold rescale
  have hmap : ContDiff ℝ ∞
      (fun z : ℝ × (Fin 3 → ℝ) =>
        (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • z.2)) := by
    fun_prop
  exact ContDiff.const_smul (ε ^ (-5 : ℤ)) (hρ.contDiff.comp hmap)

theorem contDiff_latticePeriodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (latticePeriodise (rescale ρ ε)) := by
  let f : (ℝ × (Fin 3 → ℝ)) → ℝ := rescale ρ ε
  have hf : ContDiff ℝ ∞ f := contDiff_rescale ρ hρ hε
  have hrescale : HasCompactSupport f := by
    let a : ℝ := ε ^ (-2 : ℤ)
    let b : ℝ := ε⁻¹
    let e : (ℝ × (Fin 3 → ℝ)) ≃ₜ (ℝ × (Fin 3 → ℝ)) :=
      Homeomorph.prodCongr (Homeomorph.mulRight₀ a (by
        dsimp [a]
        exact zpow_ne_zero _ (ne_of_gt hε)))
        (Homeomorph.smulOfNeZero b (by
          dsimp [b]
          exact inv_ne_zero (ne_of_gt hε)))
    have he := hρ.hasCompactSupport.comp_homeomorph e
    have hm := he.mul_left (f := fun _ : ℝ × (Fin 3 → ℝ) => ε ^ (-5 : ℤ))
    convert hm using 1
    funext q
    simp [f, e, a, b, rescale, Function.comp_def, zpow_neg, Prod.map, ne_of_gt hε]; ring_nf
  apply contDiff_iff_contDiffAt.mpr
  intro z
  rcases latticePeriodise_eq_finset_sum_on_nhds f hrescale z with
    ⟨U, hUnhds, s, hs⟩
  have hsum : ContDiff ℝ ∞
      (fun p : ℝ × (Fin 3 → ℝ) =>
        ∑ k ∈ s, f (p.1, p.2 + fun i => (k i : ℝ))) := by
    apply ContDiff.sum
    intro k hk
    exact hf.comp (by fun_prop)
  apply hsum.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hUnhds] with p hp
  exact hs p hp

theorem isSmoothOnSpaceTime_periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    IsSmoothOnSpaceTime (periodise ρ ε) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
    periodise ρ ε (p.1, torusProj p.2))
  rw [show (fun p : ℝ × (Fin 3 → ℝ) => periodise ρ ε (p.1, torusProj p.2)) =
      latticePeriodise (rescale ρ ε) by
    funext p; exact periodise_comp_torusProj_eq_latticePeriodise ρ ε p]
  exact contDiff_latticePeriodise ρ hρ hε

theorem continuous_periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (periodise ρ ε) := by
  have ht : IsOpenQuotientMap torusProj := by
    change IsOpenQuotientMap (Pi.map (fun _ : Fin 3 => QuotientAddGroup.mk))
    exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have hq : IsOpenQuotientMap
      (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) := by
    change IsOpenQuotientMap (Prod.map id torusProj)
    exact IsOpenQuotientMap.id.prodMap ht
  apply (hq.continuous_comp_iff).mp
  rw [show (periodise ρ ε) ∘ (fun p : ℝ × (Fin 3 → ℝ) =>
      (p.1, torusProj p.2)) = latticePeriodise (rescale ρ ε) by
    funext p
    exact periodise_comp_torusProj_eq_latticePeriodise ρ ε p]
  exact (contDiff_latticePeriodise ρ hρ hε).continuous

theorem bounded_periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ z : SpaceTime, |periodise ρ ε z| ≤ C := by
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval ρ hρ hε
  let F : (ℝ × (Fin 3 → ℝ)) → ℝ := latticePeriodise (rescale ρ ε)
  have hFcont : Continuous F :=
    (contDiff_latticePeriodise ρ hρ hε).continuous
  let K : Set (ℝ × (Fin 3 → ℝ)) :=
    Set.Icc a b ×ˢ Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) 1)
  have hKcompact : IsCompact K := by
    exact isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.bddAbove_image hFcont.norm.continuousOn
  refine ⟨max C 0, ?_⟩
  intro z
  by_cases hzout : z.1 < a ∨ b < z.1
  · rw [hab z hzout]
    simp
  · have hztime : z.1 ∈ Set.Icc a b := by
      exact ⟨le_of_not_gt (fun h => hzout (Or.inl h)),
        le_of_not_gt (fun h => hzout (Or.inr h))⟩
    let r : Fin 3 → ℝ := torusRep z.2
    have hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      change (AddCircle.equivIco (1 : ℝ) 0 (z.2 i) : ℝ) ∈ Set.Icc 0 1
      have hi := (AddCircle.equivIco (1 : ℝ) 0 (z.2 i)).property
      exact ⟨hi.1, by simpa using hi.2.le⟩
    have hrep : torusProj r = z.2 := by
      funext i
      dsimp [r, torusProj, torusRep]
      exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
        (y := z.2 i)
    have hzrep : z = (z.1, torusProj r) := by
      calc
        z = (z.1, z.2) := (Prod.eta z).symm
        _ = (z.1, torusProj r) := by rw [hrep]
    have hrK : (z.1, r) ∈ K := by
      exact ⟨hztime, Set.mem_pi.mpr fun i _ => hr i⟩
    have hbound : ‖F (z.1, r)‖ ≤ C :=
      hC ⟨(z.1, r), hrK, rfl⟩
    rw [hzrep]
    have heq : periodise ρ ε (z.1, torusProj r) =
        latticePeriodise (rescale ρ ε) (z.1, r) :=
      periodise_comp_torusProj_eq_latticePeriodise ρ ε (z.1, r)
    rw [heq]
    change ‖F (z.1, r)‖ ≤ max C 0
    exact hbound.trans (le_max_left C 0)

end Phi43

end RegularityStructures

end

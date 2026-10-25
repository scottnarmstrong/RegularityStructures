/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Series
public import Phi43.RegularisedNoise.Properties

/-!
# Local smooth-series certificates and patching

The finite-window Fourier argument proves the white-noise identification only on the interior of
the window.  This module separates that local statement from the countable patching argument: a
series may be smooth everywhere while its almost-sure identification is required only on a set of
space-time points, and a countable family of such local versions can be patched on one full-measure
event.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures.Phi43

theorem exists_smooth_series_version_on {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {X : ι → Ω → ℝ} {f : ι → SpaceTime → ℝ}
    {Y : SpaceTime → Ω → ℝ} {G : Set Ω} {D : Set SpaceTime}
    (hG : MeasurableSet G)
    (hGae : Filter.Eventually (fun w => w ∈ G) (MeasureTheory.ae P))
    (hX : ∀ i : ι, Measurable (X i))
    (hSmooth : ∀ (w : Ω), w ∈ G → IsSmoothOnSpaceTime
      (fun z => ∑' i, X i w * f i z))
    (hEq : ∀ z ∈ D, (fun w => ∑' i, X i w * f i z) =ᵐ[P] Y z) :
    ∃ xi : Ω → SpaceTime → ℝ,
      (∀ w : Ω, IsSmoothOnSpaceTime (xi w)) ∧
        ∀ z ∈ D, Measurable (fun w => xi w z) ∧
          (fun w => xi w z) =ᵐ[P] Y z := by
  classical
  let S : Ω → SpaceTime → ℝ := fun w z => ∑' i, X i w * f i z
  let xi : Ω → SpaceTime → ℝ := fun w z => if w ∈ G then S w z else 0
  have hSmeas (z : SpaceTime) : Measurable (fun w => S w z) := by
    apply Measurable.tsum
    intro i
    exact (hX i).mul measurable_const
  refine ⟨xi, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ G
    · simpa [xi, S, hw] using hSmooth w hw
    · have hzero : xi w = (fun _ : SpaceTime => 0) := by
        funext z
        simp [xi, hw]
      rw [hzero]
      unfold IsSmoothOnSpaceTime
      fun_prop
  · intro z hz
    constructor
    · exact Measurable.ite hG (hSmeas z) measurable_const
    · filter_upwards [hGae, hEq z hz] with w hw hweq
      simp only [xi, hw, ite_true, S]
      exact hweq

theorem smoothVersion_patch_of_countable_dense
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : SpaceTime → Ω → ℝ} {U : ℕ → Set SpaceTime}
    {xi : ℕ → Ω → SpaceTime → ℝ} {G : Set Ω}
    (hG : MeasurableSet G) (hGae : ∀ᵐ w ∂P, w ∈ G)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_cover : ⋃ n, U n = Set.univ)
    (hxi_smooth : ∀ n w, IsSmoothOnSpaceTime (xi n w))
    (hxi_meas : ∀ n z, z ∈ U n → Measurable (fun w => xi n w z))
    (hxi_eq : ∀ n z, z ∈ U n → (fun w => xi n w z) =ᵐ[P] Y z)
    (hxi_overlap : ∀ n m z, z ∈ U n → z ∈ U m →
      (fun w => xi n w z) =ᵐ[P] (fun w => xi m w z)) :
    ∃ ξ : Ω → SpaceTime → ℝ,
      (∀ w, IsSmoothOnSpaceTime (ξ w)) ∧
        (∀ z, Measurable (fun w => ξ w z) ∧ (fun w => ξ w z) =ᵐ[P] Y z) := by
  classical
  choose D hD_countable hD_dense using
    fun n m => TopologicalSpace.exists_countable_dense
      {z : SpaceTime // z ∈ U n ∩ U m}
  let E : Set Ω := {w | ∀ n m, ∀ z : D n m,
    xi n w z.1.1 = xi m w z.1.1}
  let G' : Set Ω := G ∩ E
  have hE_meas : MeasurableSet E := by
    rw [show E = ⋂ n, ⋂ m, ⋂ z : D n m,
        {w | xi n w z.1.1 = xi m w z.1.1} by
      ext w
      simp only [E, mem_ofPred_eq, mem_iInter]]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => ?_
    let _ : Countable (D n m) := hD_countable n m |>.to_subtype
    refine MeasurableSet.iInter fun z => ?_
    exact measurableSet_eq_fun (hxi_meas n z.1.1 z.1.2.1)
      (hxi_meas m z.1.1 z.1.2.2)
  have hG'_meas : MeasurableSet G' := hG.inter hE_meas
  have hE_ae : ∀ᵐ w ∂P, w ∈ E := by
    have h : ∀ᵐ w ∂P, ∀ n m, ∀ z : D n m,
        xi n w z.1.1 = xi m w z.1.1 := by
      rw [ae_all_iff]
      intro n
      rw [ae_all_iff]
      intro m
      let _ : Countable (D n m) := hD_countable n m |>.to_subtype
      rw [ae_all_iff]
      intro z
      exact hxi_overlap n m z.1.1 z.1.2.1 z.1.2.2
    change ∀ᵐ w ∂P, ∀ n m, ∀ z : D n m,
      xi n w z.1.1 = xi m w z.1.1
    exact h
  have hG'_ae : ∀ᵐ w ∂P, w ∈ G' := hGae.and hE_ae
  have h_overlap_on_G (w : Ω) (hw : w ∈ G') (n m : ℕ) {z : SpaceTime}
      (hzn : z ∈ U n) (hzm : z ∈ U m) : xi n w z = xi m w z := by
    let S : Set SpaceTime := U n ∩ U m
    let _ : Countable (D n m) := hD_countable n m |>.to_subtype
    have hwE : w ∈ E := hw.2
    have hw_all : ∀ n m, ∀ q : D n m,
        xi n w q.1.1 = xi m w q.1.1 := by
      dsimp [E] at hwE
      exact hwE
    have heqD : ∀ q : D n m, xi n w q.1.1 = xi m w q.1.1 := by
      intro q
      exact hw_all n m q
    have hcont_n : Continuous (fun q : S => xi n w q.1) :=
      (Continuous.continuous_of_isSmoothOnSpaceTime (hxi_smooth n w)).comp
        continuous_subtype_val
    have hcont_m : Continuous (fun q : S => xi m w q.1) :=
      (Continuous.continuous_of_isSmoothOnSpaceTime (hxi_smooth m w)).comp
        continuous_subtype_val
    have heq_sub : (fun q : S => xi n w q.1) = (fun q : S => xi m w q.1) := by
      apply hD_dense n m |>.denseRange_val.equalizer hcont_n hcont_m
      funext q
      exact heqD q
    exact congrFun heq_sub ⟨z, ⟨hzn, hzm⟩⟩
  have hproj : Continuous
      (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) := by
    have htorus : Continuous (torusProj : (Fin 3 → ℝ) → Torus3) := by
      apply continuous_pi
      intro i
      change Continuous (fun y : Fin 3 → ℝ => ((y i : ℝ) : UnitAddCircle))
      exact continuous_quotient_mk'.comp (continuous_apply i)
    exact continuous_fst.prodMk (htorus.comp continuous_snd)
  let chooseIndex : SpaceTime → ℕ := fun z =>
    Classical.choose (show ∃ n, z ∈ U n by
      have hz : z ∈ ⋃ n, U n := by rw [hU_cover]; exact mem_univ z
      exact Set.mem_iUnion.mp hz)
  have chooseIndex_mem (z : SpaceTime) : z ∈ U (chooseIndex z) := by
    exact Classical.choose_spec (show ∃ n, z ∈ U n by
      have hz : z ∈ ⋃ n, U n := by rw [hU_cover]; exact mem_univ z
      exact Set.mem_iUnion.mp hz)
  let ξ₀ : Ω → SpaceTime → ℝ := fun w z => xi (chooseIndex z) w z
  let ξ : Ω → SpaceTime → ℝ := fun w z => if w ∈ G' then ξ₀ w z else 0
  refine ⟨ξ, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ G'
    · let F : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => ξ w (p.1, torusProj p.2)
      have hF : ContDiff ℝ ∞ F := by
        rw [← contDiffOn_univ]
        apply contDiffOn_of_locally_contDiffOn (s := Set.univ)
        intro p hp
        let z : SpaceTime := (p.1, torusProj p.2)
        let n : ℕ := chooseIndex z
        let V : Set (ℝ × (Fin 3 → ℝ)) :=
          (fun q : ℝ × (Fin 3 → ℝ) => (q.1, torusProj q.2)) ⁻¹' U n
        have hV_open : IsOpen V := (hU_open n).preimage hproj
        have hpV : p ∈ V := chooseIndex_mem z
        have hFV : ContDiffOn ℝ ∞ F V := by
          have hbase_full : ContDiff ℝ ∞
              (fun q : ℝ × (Fin 3 → ℝ) => xi n w (q.1, torusProj q.2)) :=
            hxi_smooth n w
          have hbase : ContDiffOn ℝ ∞
              (fun q : ℝ × (Fin 3 → ℝ) => xi n w (q.1, torusProj q.2)) V :=
            hbase_full.contDiffOn.mono (subset_univ V)
          apply hbase.congr
          intro q hq
          let zq : SpaceTime := (q.1, torusProj q.2)
          have hzn : zq ∈ U n := hq
          have hzk : zq ∈ U (chooseIndex zq) := chooseIndex_mem zq
          simp only [F, ξ, ξ₀, hw, ite_true]
          exact (h_overlap_on_G w hw n (chooseIndex zq) hzn hzk).symm
        refine ⟨V, hV_open, hpV, ?_⟩
        exact hFV.mono (inter_subset_right)
      simpa [IsSmoothOnSpaceTime, F] using hF
    · have hzero : ξ w = (fun _ : SpaceTime => 0) := by
        funext z
        simp [ξ, hw]
      rw [hzero]
      unfold IsSmoothOnSpaceTime
      fun_prop
  · intro z
    constructor
    · exact Measurable.ite hG'_meas
        (hxi_meas (chooseIndex z) z (chooseIndex_mem z)) measurable_const
    · filter_upwards [hG'_ae, hxi_eq (chooseIndex z) z (chooseIndex_mem z)] with w hw hEq
      simpa [ξ, ξ₀, hw] using hEq

end RegularityStructures.Phi43

end

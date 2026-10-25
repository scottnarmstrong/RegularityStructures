/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import RegularityStructures.Analysis.Parabolic.TestFunction

/-!
# Uniform L¹ control of a periodised mollifier

The spatial periodisation is controlled by unfolding the torus into a unit fundamental cell and
then partitioning the universal cover into integer translates.  The parabolic rescaling preserves
the L¹ norm, which is the deterministic input for a uniform Young estimate on mollified tests.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

theorem integral_norm_rescale_eq (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z, |rescale ρ ε z| = ∫ z, |ρ z| := by
  have hρi : Integrable ρ := hρ.contDiff.continuous.integrable_of_hasCompactSupport
    hρ.hasCompactSupport
  have hρabs : Integrable (fun z => |ρ z|) := hρi.norm
  have hcomp := integral_comp_parabolicDilate (fun z : ℝ × (Fin 3 → ℝ) => |ρ z|)
    (inv_pos.mpr hε)
  have hscale : 0 < ε ^ (-5 : ℤ) := zpow_pos hε _
  calc
    ∫ z, |rescale ρ ε z| =
        ∫ z, ε ^ (-5 : ℤ) * |ρ (parabolicDilate ε⁻¹ z)| := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [rescale, abs_mul, abs_of_pos hscale]
      congr 2
      simp [parabolicDilate, inv_pow]
    _ = ε ^ (-5 : ℤ) * ∫ z, |ρ (parabolicDilate ε⁻¹ z)| :=
      integral_const_mul _ _
    _ = ε ^ (-5 : ℤ) * ((ε⁻¹) ^ 5)⁻¹ * ∫ z, |ρ z| := by
      rw [hcomp]
      ring
    _ = ∫ z, |ρ z| := by
      rw [inv_pow]
      field_simp

theorem integral_norm_periodise_le (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z : SpaceTime, |periodise ρ ε z| ≤
      ∫ z : ParabolicSpace, |rescale ρ ε z| := by
  let unitCell : Set (Fin 3 → ℝ) :=
    Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1)
  let integerCell : (Fin 3 → ℤ) → Set (Fin 3 → ℝ) := fun k =>
    Set.pi Set.univ (fun i => Set.Ioc (k i : ℝ) ((k i : ℝ) + 1))
  have hunit_meas : MeasurableSet unitCell := by
    dsimp [unitCell]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl fun _ _ => measurableSet_Ioc)
  have hcell_meas (k : Fin 3 → ℤ) : MeasurableSet (integerCell k) := by
    dsimp [integerCell]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl fun _ _ => measurableSet_Ioc)
  have hcell_cover : ⋃ k : Fin 3 → ℤ, integerCell k = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    choose k hk using fun i : Fin 3 => by
      have hi : x i ∈ ⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1) := by
        rw [iUnion_Ioc_intCast]
        trivial
      exact Set.mem_iUnion.mp hi
    apply Set.mem_iUnion.mpr
    refine ⟨k, Set.mem_pi.mpr (fun i _ => ?_)⟩
    simpa [integerCell] using hk i
  have hcell_disjoint : Pairwise (Function.onFun Disjoint integerCell) := by
    intro k l hkl
    change Disjoint (integerCell k) (integerCell l)
    rw [Set.disjoint_left]
    intro x hxk hxl
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, k i ≠ l i := by
      by_contra h
      apply hkl
      funext i
      by_contra hi'
      exact h ⟨i, hi'⟩
    have hki : x i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1) :=
      hxk i (Set.mem_univ i)
    have hli : x i ∈ Set.Ioc (l i : ℝ) ((l i : ℝ) + 1) :=
      hxl i (Set.mem_univ i)
    have h1d : Disjoint (Set.Ioc (k i : ℝ) ((k i : ℝ) + 1))
        (Set.Ioc (l i : ℝ) ((l i : ℝ) + 1)) := by
      rcases lt_or_gt_of_ne hi with hkl' | hlk'
      · have hcast : (k i : ℝ) + 1 ≤ (l i : ℝ) := by
          exact_mod_cast (Int.add_one_le_iff.mpr hkl')
        exact Set.disjoint_left.2 fun y hyk hyl => by
          linarith [hyk.2, hyl.1, hcast]
      · have hcast : (l i : ℝ) + 1 ≤ (k i : ℝ) := by
          exact_mod_cast (Int.add_one_le_iff.mpr hlk')
        exact Set.disjoint_left.2 fun y hyk hyl => by
          linarith [hyk.1, hyl.2, hcast]
    exact Set.disjoint_left.1 h1d hki hli
  have hterm (t : ℝ) (k : Fin 3 → ℤ) :
      ∫⁻ x in unitCell,
          ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ =
        ∫⁻ x in integerCell k, ‖rescale ρ ε (t, x)‖ₑ := by
    let kR : Fin 3 → ℝ := fun i => (k i : ℝ)
    let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.addRight kR
    have he : MeasurePreserving (e : (Fin 3 → ℝ) → (Fin 3 → ℝ))
        (volume : Measure (Fin 3 → ℝ)) volume :=
      measurePreserving_add_right volume kR
    have hpre : e ⁻¹' integerCell k = unitCell := by
      ext x
      constructor
      · intro hx
        refine Set.mem_pi.mpr (fun i _ => ?_)
        have hi := hx i (Set.mem_univ i)
        change x i ∈ Set.Ioc (0 : ℝ) 1
        change x i + kR i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1) at hi
        dsimp [kR] at hi
        constructor <;> linarith [hi.1, hi.2]
      · intro hx
        refine Set.mem_pi.mpr (fun i _ => ?_)
        have hi := hx i (Set.mem_univ i)
        change x i + kR i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1)
        dsimp [kR]
        constructor <;> linarith [hi.1, hi.2]
    have he_restrict := he.restrict_preimage (hcell_meas k)
    have hf : Measurable (fun x : Fin 3 → ℝ =>
        ‖rescale ρ ε (t, x)‖ₑ) := by
      exact ((contDiff_rescale ρ hρ hε).continuous.measurable.comp
        (measurable_const.prodMk measurable_id)).enorm
    have hchange := he_restrict.lintegral_comp hf
    rw [hpre] at hchange
    change (∫⁻ x in unitCell,
        ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ) = _ at hchange
    exact hchange
  have hfixed (t : ℝ) :
      ∫⁻ x : Torus3, ‖periodise ρ ε (t, x)‖ₑ ≤
        ∫⁻ x : Fin 3 → ℝ, ‖rescale ρ ε (t, x)‖ₑ := by
    calc
      ∫⁻ x : Torus3, ‖periodise ρ ε (t, x)‖ₑ =
          ∫⁻ x in unitCell, ‖periodise ρ ε (t, fun i => (x i : UnitAddCircle))‖ₑ := by
        have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
          rw [AddCircle.volume_eq_smul_haarAddCircle]
          simp
        have htorus : (volume : Measure Torus3) =
            Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle) := by
          change Measure.pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle)) = _
          rw [hcircle]
        rw [htorus]
        have hD : {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc
            ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)} = unitCell := by
          ext x
          simp [unitCell]
        have hpre := UnitAddTorus.lintegral_preimage
          (fun x : Torus3 => ‖periodise ρ ε (t, x)‖ₑ) 0
        rw [hD] at hpre
        exact hpre
      _ ≤ ∫⁻ x in unitCell, ∑' k : Fin 3 → ℤ,
          ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ := by
        apply lintegral_mono
        intro x
        have hp := periodise_comp_torusProj_eq_latticePeriodise ρ ε
          (t, (x : Fin 3 → ℝ))
        have hp' : periodise ρ ε (t, fun i => (x i : UnitAddCircle)) =
            latticePeriodise (rescale ρ ε) (t, (x : Fin 3 → ℝ)) := by
          change periodise ρ ε (t, torusProj (x : Fin 3 → ℝ)) = _
          exact hp
        change ‖periodise ρ ε (t, fun i => (x i : UnitAddCircle))‖ₑ ≤ _
        calc
          _ = ‖latticePeriodise (rescale ρ ε) (t, x)‖ₑ := by rw [hp']
          _ ≤ ∑' k : Fin 3 → ℤ,
              ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ := by
            exact enorm_tsum_le_tsum_enorm
      _ = ∑' k : Fin 3 → ℤ, ∫⁻ x in unitCell,
          ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ := by
        rw [lintegral_tsum]
        intro k
        exact (((contDiff_rescale ρ hρ hε).continuous.measurable.comp
          (measurable_const.prodMk (measurable_id.add measurable_const))).enorm).aemeasurable
          |>.restrict
      _ = ∑' k : Fin 3 → ℤ, ∫⁻ x in integerCell k,
          ‖rescale ρ ε (t, x)‖ₑ := by
        apply tsum_congr
        intro k
        exact hterm t k
      _ = ∫⁻ x : Fin 3 → ℝ, ‖rescale ρ ε (t, x)‖ₑ := by
        calc
          _ = ∫⁻ x in ⋃ k : Fin 3 → ℤ, integerCell k,
              ‖rescale ρ ε (t, x)‖ₑ :=
            (lintegral_iUnion (fun k => hcell_meas k) hcell_disjoint _).symm
          _ = ∫⁻ x : Fin 3 → ℝ, ‖rescale ρ ε (t, x)‖ₑ := by
            rw [hcell_cover, Measure.restrict_univ]
  have hperiod : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hrescale : Integrable (rescale ρ ε) := by
    have hsupp : HasCompactSupport (rescale ρ ε) := by
      let a : ℝ := ε ^ (-2 : ℤ)
      let b : ℝ := ε⁻¹
      let e : (ℝ × (Fin 3 → ℝ)) ≃ₜ (ℝ × (Fin 3 → ℝ)) :=
        Homeomorph.prodCongr (Homeomorph.mulRight₀ a (by
          dsimp [a]
          exact zpow_ne_zero _ (ne_of_gt hε)))
          (Homeomorph.smulOfNeZero b (by
            dsimp [b]
            exact inv_ne_zero (ne_of_gt hε)))
      have hm := hρ.hasCompactSupport.comp_homeomorph e
      have hm' := hm.mul_left (f := fun _ : ℝ × (Fin 3 → ℝ) => ε ^ (-5 : ℤ))
      convert hm' using 1
      funext q
      simp [e, a, b, rescale, Function.comp_def, zpow_neg, Prod.map, ne_of_gt hε]
      ring_nf
    exact (contDiff_rescale ρ hρ hε).continuous.integrable_of_hasCompactSupport hsupp
  have hleft :
      ∫⁻ z : SpaceTime, ‖periodise ρ ε z‖ₑ ≤
        ∫⁻ z : ParabolicSpace, ‖rescale ρ ε z‖ₑ := by
    rw [Measure.volume_eq_prod, lintegral_prod]
    · calc
        ∫⁻ t, ∫⁻ x : Torus3, ‖periodise ρ ε (t, x)‖ₑ ≤
            ∫⁻ t, ∫⁻ x : Fin 3 → ℝ, ‖rescale ρ ε (t, x)‖ₑ := by
          exact lintegral_mono fun t => hfixed t
        _ = ∫⁻ z : ParabolicSpace, ‖rescale ρ ε z‖ₑ := by
          rw [Measure.volume_eq_prod]
          symm
          exact lintegral_prod _
            ((contDiff_rescale ρ hρ hε).continuous.measurable.enorm).aemeasurable
    · exact ((measurable_periodise ρ hρ).enorm).aemeasurable
  change (∫ z : SpaceTime, ‖periodise ρ ε z‖) ≤
    ∫ z : ParabolicSpace, ‖rescale ρ ε z‖
  rw [integral_norm_eq_lintegral_enorm hperiod.aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm hrescale.aestronglyMeasurable]
  exact (ENNReal.toReal_le_toReal
    (lt_top_iff_ne_top.mp hperiod.hasFiniteIntegral)
    (lt_top_iff_ne_top.mp hrescale.hasFiniteIntegral)).2 hleft

end Phi43

end RegularityStructures

end

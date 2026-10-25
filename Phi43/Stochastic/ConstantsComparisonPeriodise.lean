/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.MollifierL1
public import Phi43.Torus.KernelBoundsL1
public import Phi43.Torus.KernelBoundsMollifier
public import Phi43.ClassicalSolution.PeriodiseRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mass of the spatially periodised mollifier

This is the signed counterpart of the absolute-value estimate in
`Phi43.Stochastic.MollifierL1`.  It is the normalization input for the
signed approximate-identity argument in the Section 7 comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private def comparisonUnitCell : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1)

private def comparisonIntegerCell (k : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (k i : ℝ) ((k i : ℝ) + 1))

private theorem comparisonIntegerCell_measurable (k : Fin 3 → ℤ) :
    MeasurableSet (comparisonIntegerCell k) := by
  unfold comparisonIntegerCell
  exact (measurableSet_pi Set.countable_univ).2
    (Or.inl fun _ _ => measurableSet_Ioc)

private theorem comparisonIntegerCell_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint comparisonIntegerCell) := by
  intro k l hkl
  change Disjoint (comparisonIntegerCell k) (comparisonIntegerCell l)
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
  rcases lt_or_gt_of_ne hi with hkl' | hlk'
  · have hcast : (k i : ℝ) + 1 ≤ (l i : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hkl')
    linarith [hki.2, hli.1]
  · have hcast : (l i : ℝ) + 1 ≤ (k i : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlk')
    linarith [hki.1, hli.2]

private theorem comparisonIntegerCell_cover :
    ⋃ k : Fin 3 → ℤ, comparisonIntegerCell k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  choose k hk using fun i : Fin 3 => by
    have hi : x i ∈ ⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1) := by
      rw [iUnion_Ioc_intCast]
      trivial
    exact Set.mem_iUnion.mp hi
  apply Set.mem_iUnion.mpr
  refine ⟨k, Set.mem_pi.mpr (fun i _ => ?_)⟩
  simpa [comparisonIntegerCell] using hk i

private theorem comparison_cell_change (F : ℝ × (Fin 3 → ℝ) → ℝ)
    (t : ℝ) (k : Fin 3 → ℤ) :
    ∫ x in comparisonUnitCell,
        F (t, x + fun i => (k i : ℝ)) =
      ∫ x in comparisonIntegerCell k, F (t, x) := by
  let kR : Fin 3 → ℝ := fun i => (k i : ℝ)
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.addRight kR
  have he : MeasurePreserving (e : (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (volume : Measure (Fin 3 → ℝ)) volume :=
    measurePreserving_add_right volume kR
  have hpre : e ⁻¹' comparisonIntegerCell k = comparisonUnitCell := by
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
  have he_restrict := he.restrict_preimage (comparisonIntegerCell_measurable k)
  have hchange := he_restrict.integral_comp' (fun x : Fin 3 → ℝ => F (t, x))
  rw [hpre] at hchange
  change (∫ x in comparisonUnitCell,
      F (t, x + fun i => (k i : ℝ))) = _ at hchange
  exact hchange

private theorem comparison_slice_integrable (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : Fin 3 → ℝ => rescale ρ ε (t, x)) := by
  obtain ⟨R, hR, hbox⟩ := rescale_support_box ρ hρ hε
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-(R * ε)) (R * ε))
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hs : HasCompactSupport (fun x : Fin 3 → ℝ => rescale ρ ε (t, x)) := by
    apply HasCompactSupport.intro hK
    intro x hx
    by_contra hzero
    apply hx
    refine Set.mem_pi.mpr (fun i _ => ?_)
    have hi := (hbox (t, x) hzero).2 i
    have hnonneg : 0 ≤ R * ε := mul_nonneg hR hε.le
    exact abs_le.mp hi
  exact ((contDiff_rescale ρ hρ hε).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hs

private theorem comparison_shift_integrable (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (k : Fin 3 → ℤ) :
    Integrable (fun x : Fin 3 → ℝ => rescale ρ ε (t, x + fun i => (k i : ℝ))) := by
  let kR : Fin 3 → ℝ := fun i => (k i : ℝ)
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.addRight kR
  have he : MeasurePreserving (e : (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (volume : Measure (Fin 3 → ℝ)) volume :=
    measurePreserving_add_right volume kR
  have hi := he.integrable_comp_of_integrable
    (comparison_slice_integrable ρ hρ hε t)
  simpa [e, kR, Function.comp_def] using hi

private theorem comparison_fixed_mass (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ x : Torus3, periodise ρ ε (t, x) =
      ∫ x : Fin 3 → ℝ, rescale ρ ε (t, x) := by
  have hsum_norm : Summable (fun k : Fin 3 → ℤ =>
      ∫ x in comparisonUnitCell,
        ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖) := by
    have hsum_cell : HasSum (fun k : Fin 3 → ℤ =>
        ∫ x in comparisonIntegerCell k, |rescale ρ ε (t, x)|)
        (∫ x : Fin 3 → ℝ, |rescale ρ ε (t, x)|) := by
      have hi := hasSum_integral_iUnion (f := fun x : Fin 3 → ℝ =>
          |rescale ρ ε (t, x)|) (fun k => comparisonIntegerCell_measurable k)
          comparisonIntegerCell_pairwise_disjoint
          ((comparison_slice_integrable ρ hρ hε t).norm.integrableOn)
      rw [comparisonIntegerCell_cover, Measure.restrict_univ] at hi
      exact hi
    have hcell_eq : ∀ k : Fin 3 → ℤ,
        ∫ x in comparisonUnitCell,
            ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ =
          ∫ x in comparisonIntegerCell k, |rescale ρ ε (t, x)| := by
      intro k
      exact comparison_cell_change (fun z => |rescale ρ ε z|) t k
    rw [show (fun k : Fin 3 → ℤ =>
        ∫ x in comparisonUnitCell,
          ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖) =
        (fun k => ∫ x in comparisonIntegerCell k, |rescale ρ ε (t, x)|) by
      funext k; exact hcell_eq k]
    exact hsum_cell.summable
  have hsum : HasSum (fun k : Fin 3 → ℤ =>
      ∫ x in comparisonUnitCell,
        rescale ρ ε (t, x + fun i => (k i : ℝ)))
      (∫ x : Fin 3 → ℝ, rescale ρ ε (t, x)) := by
    have hi := hasSum_integral_iUnion (f := fun x : Fin 3 → ℝ => rescale ρ ε (t, x))
      (fun k => comparisonIntegerCell_measurable k)
      comparisonIntegerCell_pairwise_disjoint
      (comparison_slice_integrable ρ hρ hε t).integrableOn
    rw [comparisonIntegerCell_cover, Measure.restrict_univ] at hi
    exact hi.congr_fun (fun k =>
      comparison_cell_change (fun z => rescale ρ ε z) t k)
  have hperiod : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have htorus : (volume : Measure Torus3) =
      Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle) := by
    change Measure.pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle)) = _
    rw [hcircle]
  have hpre := UnitAddTorus.integral_preimage
    (fun x : Torus3 => periodise ρ ε (t, x)) (0 : Fin 3 → ℝ)
  have hD : {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc
      ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)} = comparisonUnitCell := by
    ext x
    simp [comparisonUnitCell]
  rw [hD] at hpre
  have hunit : ∫ x in comparisonUnitCell,
      periodise ρ ε (t, fun i => (x i : UnitAddCircle)) =
      ∫ x : Torus3, periodise ρ ε (t, x) := by
    rw [htorus]
    simpa only [MeasureSpace.volume, instMeasureSpaceUnitAddCircle, AddCircle.measureSpace]
      using hpre.symm
  rw [← hunit]
  have hperiod_eq : ∀ x : Fin 3 → ℝ,
      periodise ρ ε (t, torusProj x) =
        ∑' k : Fin 3 → ℤ, rescale ρ ε (t, x + fun i => (k i : ℝ)) := by
    intro x
    exact periodise_comp_torusProj_eq_latticePeriodise ρ ε (t, x)
  have htsum : ∫ x in comparisonUnitCell,
      ∑' k : Fin 3 → ℤ, rescale ρ ε (t, x + fun i => (k i : ℝ)) =
      ∑' k : Fin 3 → ℤ, ∫ x in comparisonUnitCell,
        rescale ρ ε (t, x + fun i => (k i : ℝ)) := by
    have hmeas : ∀ k : Fin 3 → ℤ,
        AEStronglyMeasurable
          (fun x : Fin 3 → ℝ => rescale ρ ε (t, x + fun i => (k i : ℝ)))
          (volume.restrict comparisonUnitCell) := by
      intro k
      exact (((contDiff_rescale ρ hρ hε).continuous.measurable.comp
        (measurable_const.prodMk (measurable_id.add measurable_const))).aestronglyMeasurable).restrict
    have hterm : ∀ k : Fin 3 → ℤ,
        ∫⁻ x in comparisonUnitCell,
            ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ =
          ‖∫ x in comparisonUnitCell,
            ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖‖ₑ := by
      intro k
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _
          (comparison_shift_integrable ρ hρ hε t k).integrableOn.norm]
      simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
      rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))]
    have hnorm : (∑' k : Fin 3 → ℤ, ∫⁻ x in comparisonUnitCell,
        ‖rescale ρ ε (t, x + fun i => (k i : ℝ))‖ₑ) ≠ (⊤ : ENNReal) := by
      rw [funext hterm]
      exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hsum_norm.abs
    exact integral_tsum hmeas hnorm
  calc
    ∫ x in comparisonUnitCell,
        periodise ρ ε (t, fun i => (x i : UnitAddCircle)) =
        ∫ x in comparisonUnitCell,
          ∑' k : Fin 3 → ℤ, rescale ρ ε (t, x + fun i => (k i : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change periodise ρ ε (t, torusProj x) = _
      exact hperiod_eq x
    _ = ∑' k : Fin 3 → ℤ, ∫ x in comparisonUnitCell,
        rescale ρ ε (t, x + fun i => (k i : ℝ)) := htsum
    _ = ∫ x : Fin 3 → ℝ, rescale ρ ε (t, x) := hsum.tsum_eq

theorem integral_periodise_eq_integral_rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∫ z : SpaceTime, periodise ρ ε z = ∫ z : ParabolicSpace, rescale ρ ε z := by
  have hperiod : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hrescale : Integrable (rescale ρ ε) := by
    apply (integrable_norm_iff ?_).1
    simpa only [Real.norm_eq_abs] using integrable_abs_rescale ρ hρ hε
    exact ((contDiff_rescale ρ hρ hε).continuous.measurable).aestronglyMeasurable
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  rw [integral_prod _ hperiod, integral_prod _ hrescale]
  apply integral_congr_ae
  filter_upwards [] with t
  exact comparison_fixed_mass ρ hρ hε t

private theorem comparison_integral_rescale_eq_integral (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, rescale ρ ε z = ∫ z, ρ z := by
  have hρi : Integrable ρ := hρ.contDiff.continuous.integrable_of_hasCompactSupport
    hρ.hasCompactSupport
  have hcomp := integral_comp_parabolicDilate (fun z : ParabolicSpace => ρ z)
    (inv_pos.mpr hε)
  have hscale : ε ^ (-5 : ℤ) * (ε⁻¹ ^ 5)⁻¹ = 1 := by
    rw [inv_pow, inv_inv]
    rw [show ε ^ 5 = ε ^ (5 : ℤ) by norm_num]
    rw [← zpow_add₀ (ne_of_gt hε)]
    norm_num
  calc
    ∫ z, rescale ρ ε z =
        ∫ z, ε ^ (-5 : ℤ) * ρ (parabolicDilate ε⁻¹ z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [rescale]
      congr 2
      simp [parabolicDilate, inv_pow]
    _ = ε ^ (-5 : ℤ) * ∫ z, ρ (parabolicDilate ε⁻¹ z) :=
      integral_const_mul _ _
    _ = ε ^ (-5 : ℤ) * ((ε⁻¹ ^ 5)⁻¹ * ∫ z, ρ z) := by
      rw [hcomp]
    _ = ∫ z, ρ z := by
      rw [← mul_assoc, hscale, one_mul]

theorem integral_periodise_eq_one (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : ∫ z, periodise ρ ε z = 1 := by
  rw [integral_periodise_eq_integral_rescale ρ hρ hε]
  rw [comparison_integral_rescale_eq_integral ρ hρ hε, hρ.integral_eq_one]

end RegularityStructures.Phi43

end

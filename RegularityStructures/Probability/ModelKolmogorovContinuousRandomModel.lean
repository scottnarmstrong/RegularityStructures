/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSDiagonal
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.CompletePartialOrder

/-!
# Continuity and measurability of the actual model norms

The continuity predicate is `IsContinuousRandomModelOn`: every realisation of the random model is
continuous. Continuous realisations make the uncountable suprema defining the model norms
measurable. This proves the measurability part of the Kolmogorov criterion for models [Hai14,
Theorem 10.7], not its moment estimate. The proof uses separability and closed inequalities, not a
random pathwise bound or a modification of the given model. No compactness is needed.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace RegularityStructures

private theorem measurableSet_forall_le_continuous
    {Ω A : Type*} [MeasurableSpace Ω] [TopologicalSpace A] [SeparableSpace A]
    {f : Ω → A → ℝ} {g : A → ℝ}
    (hm : ∀ a, Measurable (fun ω => f ω a))
    (hf : ∀ ω, Continuous (f ω)) (hg : Continuous g) :
    MeasurableSet {ω | ∀ a, f ω a ≤ g a} := by
  have hm' : Measurable (fun ω => ⨆ a, ENNReal.ofReal (f ω a - g a)) := by
    have h : Measurable (⨆ a, fun ω => ENNReal.ofReal (f ω a - g a)) :=
      measurable_iSup_of_lowerSemicontinuous
        (f := fun a ω => ENNReal.ofReal (f ω a - g a))
        (fun a => ((hm a).sub measurable_const).ennreal_ofReal)
        (fun ω => (ENNReal.continuous_ofReal.comp ((hf ω).sub hg)).lowerSemicontinuous)
    have he : (⨆ a, fun ω => ENNReal.ofReal (f ω a - g a)) =
        (fun ω => ⨆ a, ENNReal.ofReal (f ω a - g a)) := by
      funext ω
      exact iSup_apply
    exact he ▸ h
  have he : {ω | ∀ a, f ω a ≤ g a} =
      {ω | (⨆ a, ENNReal.ofReal (f ω a - g a)) ≤ 0} := by
    ext ω
    change (∀ a, f ω a ≤ g a) ↔ (⨆ a, ENNReal.ofReal (f ω a - g a)) ≤ 0
    rw [iSup_le_iff]
    simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, sub_nonpos]
  rw [he]
  exact measurableSet_le hm' measurable_const

private theorem measurable_of_nnreal_sublevels
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ≥0∞}
    (h : ∀ c : ℝ≥0, MeasurableSet {ω | f ω ≤ c}) : Measurable f := by
  apply measurable_of_Iic
  intro c
  by_cases hc : c = ⊤
  · simp [hc]
  · lift c to ℝ≥0 using hc
    exact h c

private theorem measurable_family_bestConstant
    {Ω I A : Type*} [MeasurableSpace Ω] [Countable I]
    [TopologicalSpace A] [SeparableSpace A]
    {F : Ω → I → A → ℝ} {g : I → A → ℝ} {N : Ω → ℝ≥0∞} {active : I → Prop}
    (hm : ∀ i a, Measurable (fun ω => F ω i a))
    (hf : ∀ ω i, Continuous (F ω i))
    (hg : ∀ i, active i → Continuous (g i))
    (hN : ∀ ω (c : ℝ≥0), N ω ≤ c ↔
      ∀ i, active i → ∀ a, F ω i a ≤ c * g i a) : Measurable N := by
  apply measurable_of_nnreal_sublevels
  intro c
  have he : {ω | N ω ≤ c} =
      ⋂ i : I, ⋂ (hi : active i), {ω | ∀ a, F ω i a ≤ c * g i a} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, hN]
  rw [he]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
    measurableSet_forall_le_continuous (hm i) (fun ω => hf ω i)
      (continuous_const.mul (hg i hi))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι} {Ω : Type*} [MeasurableSpace Ω]
  {Z Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup} {S : Set ParabolicSpace}

private theorem continuous_pi_restrict
    (hZ : RegularityStructures.IsContinuousRandomModelOn Z S) (ω : Ω) (i : ι) :
    Continuous (fun w : Ioc (0 : ℝ) 1 × S =>
      (Z ω).regPi w.2 (Pi.single i 1) w.1 w.2) := by
  exact (hZ.2.2.1 ω i).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
    (fun w => ⟨w.1.property, w.2.property⟩)

private theorem continuous_gamma_restrict
    (hZ : RegularityStructures.IsContinuousRandomModelOn Z S) (ω : Ω) (i j : ι) :
    Continuous (fun w : S × S => (Z ω).gammaMap w.2 w.1 (Pi.single i 1) j) := by
  exact (hZ.2.2.2 ω i j).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
    (fun w => ⟨w.1.property, w.2.property⟩)

private theorem continuous_pi_weight (a : ℝ) :
    Continuous (fun w : Ioc (0 : ℝ) 1 × S => (w.1 : ℝ) ^ a) :=
  (continuous_subtype_val.comp continuous_fst).rpow_const
    (fun w => Or.inl (ne_of_gt w.1.property.1))

private theorem continuous_gamma_weight {a : ℝ} (ha : 0 ≤ a) :
    Continuous (fun w : S × S => parabolicSemigroup.scaleDist w.2 w.1 ^ a) := by
  exact (continuous_parabolicNorm.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))).rpow_const (fun _ => Or.inr ha)

/-- The actual Pi norm of a random model with continuous realisations is measurable. -/
theorem IsContinuousRandomModelOn.measurable_piNormOn
    (hZ : RegularityStructures.IsContinuousRandomModelOn Z S) (γ : ℝ) :
    Measurable (fun ω => (Z ω).piNormOn γ S) := by
  apply measurable_family_bestConstant
    (F := fun ω i (w : Ioc (0 : ℝ) 1 × S) =>
      |(Z ω).regPi w.2 (Pi.single i 1) w.1 w.2|)
    (g := fun i w => (w.1 : ℝ) ^ (𝒯.deg i / parabolicSemigroup.order))
    (active := fun i => 𝒯.deg i < γ)
  · exact fun i w => continuous_abs.measurable.comp (hZ.1 i w.2 w.1 w.1.property.1)
  · exact fun ω i => (continuous_pi_restrict hZ ω i).abs
  · exact fun i _ => continuous_pi_weight _
  · intro ω c
    rw [Model.piNormOn_le_iff]
    exact ⟨fun hh i hi w => hh i hi _ w.1.property _ w.2.property,
      fun hh i hi t ht x hx => hh i hi (⟨t, ht⟩, ⟨x, hx⟩)⟩

/-- The actual Gamma norm is measurable, including at coincident base points. -/
theorem IsContinuousRandomModelOn.measurable_gammaNormOn
    (hZ : RegularityStructures.IsContinuousRandomModelOn Z S) (γ : ℝ) :
    Measurable (fun ω => (Z ω).gammaNormOn γ S) := by
  apply measurable_family_bestConstant
    (F := fun ω (ij : ι × ι) (w : S × S) =>
      |(Z ω).gammaMap w.2 w.1 (Pi.single ij.1 1) ij.2|)
    (g := fun ij w => parabolicSemigroup.scaleDist w.2 w.1 ^ (𝒯.deg ij.1 - 𝒯.deg ij.2))
    (active := fun ij => 𝒯.deg ij.1 < γ ∧ 𝒯.deg ij.2 < 𝒯.deg ij.1)
  · exact fun ij w => continuous_abs.measurable.comp (hZ.2.1 ij.1 ij.2 w.1 w.2)
  · exact fun ω ij => (continuous_gamma_restrict hZ ω ij.1 ij.2).abs
  · exact fun _ hi => continuous_gamma_weight (sub_nonneg.mpr hi.2.le)
  · intro ω c
    rw [Model.gammaNormOn_le_iff]
    exact ⟨fun hh ij hi w => hh ij.1 ij.2 hi.1 hi.2 _ w.1.property _ w.2.property,
      fun hh i j hi hj x hx y hy => hh (i, j) ⟨hi, hj⟩ (⟨x, hx⟩, ⟨y, hy⟩)⟩

/-- Measurability of the actual Pi difference norm, without replacing either model. -/
theorem IsContinuousRandomModelOn.measurable_piDiffNormOn
    (hZ₁ : RegularityStructures.IsContinuousRandomModelOn Z₁ S)
    (hZ₂ : RegularityStructures.IsContinuousRandomModelOn Z₂ S) (γ : ℝ) :
    Measurable (fun ω => (Z₁ ω).piDiffNormOn (Z₂ ω) γ S) := by
  apply measurable_family_bestConstant
    (F := fun ω i (w : Ioc (0 : ℝ) 1 × S) =>
      |(Z₁ ω).regPi w.2 (Pi.single i 1) w.1 w.2 -
        (Z₂ ω).regPi w.2 (Pi.single i 1) w.1 w.2|)
    (g := fun i w => (w.1 : ℝ) ^ (𝒯.deg i / parabolicSemigroup.order))
    (active := fun i => 𝒯.deg i < γ)
  · exact fun i w =>
      continuous_abs.measurable.comp
        ((hZ₁.1 i w.2 w.1 w.1.property.1).sub (hZ₂.1 i w.2 w.1 w.1.property.1))
  · exact fun ω i => ((continuous_pi_restrict hZ₁ ω i).sub
      (continuous_pi_restrict hZ₂ ω i)).abs
  · exact fun i _ => continuous_pi_weight _
  · intro ω c
    rw [Model.piDiffNormOn_le_iff]
    exact ⟨fun hh i hi w => hh i hi _ w.1.property _ w.2.property,
      fun hh i hi t ht x hx => hh i hi (⟨t, ht⟩, ⟨x, hx⟩)⟩

/-- Measurability of the actual Gamma difference norm, including its diagonal. -/
theorem IsContinuousRandomModelOn.measurable_gammaDiffNormOn
    (hZ₁ : RegularityStructures.IsContinuousRandomModelOn Z₁ S)
    (hZ₂ : RegularityStructures.IsContinuousRandomModelOn Z₂ S) (γ : ℝ) :
    Measurable (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S) := by
  apply measurable_family_bestConstant
    (F := fun ω (ij : ι × ι) (w : S × S) =>
      |(Z₁ ω).gammaMap w.2 w.1 (Pi.single ij.1 1) ij.2 -
        (Z₂ ω).gammaMap w.2 w.1 (Pi.single ij.1 1) ij.2|)
    (g := fun ij w => parabolicSemigroup.scaleDist w.2 w.1 ^ (𝒯.deg ij.1 - 𝒯.deg ij.2))
    (active := fun ij => 𝒯.deg ij.1 < γ ∧ 𝒯.deg ij.2 < 𝒯.deg ij.1)
  · exact fun ij w => continuous_abs.measurable.comp ((hZ₁.2.1 ij.1 ij.2 w.1 w.2).sub
      (hZ₂.2.1 ij.1 ij.2 w.1 w.2))
  · exact fun ω ij => ((continuous_gamma_restrict hZ₁ ω ij.1 ij.2).sub
      (continuous_gamma_restrict hZ₂ ω ij.1 ij.2)).abs
  · exact fun _ hi => continuous_gamma_weight (sub_nonneg.mpr hi.2.le)
  · intro ω c
    rw [Model.gammaDiffNormOn_le_iff]
    exact ⟨fun hh ij hi w => hh ij.1 ij.2 hi.1 hi.2 _ w.1.property _ w.2.property,
      fun hh i j hi hj x hx y hy => hh (i, j) ⟨hi, hj⟩ (⟨x, hx⟩, ⟨y, hy⟩)⟩

end RegularityStructures

end


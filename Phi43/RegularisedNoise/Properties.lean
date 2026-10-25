/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Elementary properties of regularised noises

This module isolates the topological and measurability consequences of the definition of a
regularised noise.  The existence of the smooth modification itself is kept separate: it requires
the stochastic regularity argument for the mollifier family.  These consequences correspond to
Definition 2.4 and the uniqueness/measurability clauses of item (W2) of Lemma 4.1 of the statement.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj := by
  apply IsOpenQuotientMap.piMap
  intro i
  change IsOpenQuotientMap (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
  exact QuotientAddGroup.isOpenQuotientMap_mk

private theorem isOpenQuotientMap_spaceTimeProj :
    IsOpenQuotientMap (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) := by
  have hfun :
      (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) = Prod.map id torusProj := by
    funext p
    apply Prod.ext
    · rfl
    · funext i
      rfl
  rw [hfun]
  exact IsOpenQuotientMap.id.prodMap isOpenQuotientMap_torusProj

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem Continuous.continuous_of_isSmoothOnSpaceTime {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) : Continuous f := by
  rw [isOpenQuotientMap_spaceTimeProj.isQuotientMap.continuous_iff]
  exact hf.continuous

theorem regularisedNoise_indistinguishable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ ξ' : Ω → SpaceTime → ℝ)
    (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ ε ξ') :
    ∀ᵐ ω ∂P, ξ ω = ξ' ω := by
  obtain ⟨D, hD_countable, hD_dense⟩ := TopologicalSpace.exists_countable_dense SpaceTime
  let _ : Countable D := hD_countable.to_subtype
  have h_eq (z : SpaceTime) : (fun ω => ξ ω z) =ᵐ[P] (fun ω => ξ' ω z) :=
    (hξ.2 z).2.trans (hξ'.2 z).2.symm
  have h_eq_D : ∀ᵐ ω ∂P, ∀ z : D, ξ ω z = ξ' ω z :=
    ae_all_iff.2 fun z => h_eq z
  filter_upwards [h_eq_D] with ω hω
  apply hD_dense.denseRange_val.equalizer
    (Continuous.continuous_of_isSmoothOnSpaceTime (hξ.1 ω))
    (Continuous.continuous_of_isSmoothOnSpaceTime (hξ'.1 ω))
  funext z
  exact hω z

theorem regularisedNoise_measurable_uncurry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ : Ω → SpaceTime → ℝ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable fun p : Ω × SpaceTime => ξ p.1 p.2 := by
  have hmeas :
      Measurable (Function.uncurry (fun z : SpaceTime => fun ω : Ω => ξ ω z)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => Continuous.continuous_of_isSmoothOnSpaceTime (hξ.1 ω))
      (fun z => (hξ.2 z).1)
  change Measurable
    (Function.uncurry (fun z : SpaceTime => fun ω : Ω => ξ ω z) ∘ Prod.swap)
  exact hmeas.comp measurable_swap

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Translate.Model
public import RegularityStructures.Probability.ModelKolmogorovHSDiagonal
public import RegularityStructures.Probability.ModelKolmogorovFieldNormMeasurable
public import Mathlib.Order.CompletePartialOrder

/-!
# Translation and finite covers for the `Π`-norm

* `Model.piNormOn_translate`, `Model.piDiffNormOn_translate`: the `Π`-norms of a translated model
  on `T` are the norms of the original model on `T + a`.
* `Model.piNormOn_biUnion_le`, `Model.piDiffNormOn_biUnion_le`: the norm on a finite union is at
  most the maximum (`Finset.sup`) of the norms on the pieces.
* `IsContinuousRandomModelWithFieldsOn.mono` and `IsContinuousRandomModelWithFieldsOn.translate`:
  the continuity predicate passes to subsets and to translates.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem piNormOn_translate (M : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace) (γ : ℝ)
    (T : Set ParabolicSpace) :
    (M.translate a).piNormOn γ T = M.piNormOn γ ((· + a) '' T) := by
  simp only [piNormOn, piBoundOn_translate_iff]

theorem piDiffNormOn_translate (M M₂ : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace)
    (γ : ℝ) (T : Set ParabolicSpace) :
    (M.translate a).piDiffNormOn (M₂.translate a) γ T =
      M.piDiffNormOn M₂ γ ((· + a) '' T) := by
  simp only [piDiffNormOn, piDiffBoundOn_translate_iff]

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem piNormOn_biUnion_le {κ : Type*} (M : Model 𝒯 K) (γ : ℝ) (s : Finset κ)
    (T : κ → Set E) :
    M.piNormOn γ (⋃ i ∈ s, T i) ≤ s.sup fun i => M.piNormOn γ (T i) := by
  by_cases h : (s.sup fun i => M.piNormOn γ (T i)) = ⊤
  · rw [h]; exact le_top
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ≥0∞) = _ := ⟨_, ENNReal.coe_toNNReal h⟩
  rw [← hc, M.piNormOn_le_iff]
  intro i hi t ht x hx
  simp only [mem_iUnion] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  have : M.piNormOn γ (T j) ≤ c := hc ▸ Finset.le_sup (f := fun i => M.piNormOn γ (T i)) hj
  exact (M.piNormOn_le_iff c).1 this i hi t ht x hxj

theorem piDiffNormOn_biUnion_le {κ : Type*} (M M₂ : Model 𝒯 K) (γ : ℝ) (s : Finset κ)
    (T : κ → Set E) :
    M.piDiffNormOn M₂ γ (⋃ i ∈ s, T i) ≤ s.sup fun i => M.piDiffNormOn M₂ γ (T i) := by
  by_cases h : (s.sup fun i => M.piDiffNormOn M₂ γ (T i)) = ⊤
  · rw [h]; exact le_top
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ≥0∞) = _ := ⟨_, ENNReal.coe_toNNReal h⟩
  rw [← hc, M.piDiffNormOn_le_iff]
  intro i hi t ht x hx
  simp only [mem_iUnion] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  have : M.piDiffNormOn M₂ γ (T j) ≤ c :=
    hc ▸ Finset.le_sup (f := fun i => M.piDiffNormOn M₂ γ (T i)) hj
  exact (M.piDiffNormOn_le_iff M₂ γ _ c).1 this i hi t ht x hxj

end Model

end RegularityStructures

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {𝒯 : RegularityStructure ι} {Z : Ω → Model 𝒯 parabolicSemigroup}

theorem IsContinuousRandomModelWithFieldsOn.mono {S S' : Set ParabolicSpace}
    (hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z S) (h : S' ⊆ S) :
    RegularityStructures.IsContinuousRandomModelWithFieldsOn Z S' :=
  ⟨⟨hZ.1.1, hZ.1.2.1, fun ω i => (hZ.1.2.2.1 ω i).mono (prod_mono subset_rfl h),
    fun ω i j => (hZ.1.2.2.2 ω i j).mono (prod_mono h h)⟩, hZ.2⟩

theorem IsContinuousRandomModelWithFieldsOn.translate {T : Set ParabolicSpace} (a : ParabolicSpace)
    (hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z ((· + a) '' T)) :
    RegularityStructures.IsContinuousRandomModelWithFieldsOn (fun ω => (Z ω).translate a) T := by
  have hadd : Continuous fun w : ℝ × ParabolicSpace => (w.1, w.2 + a) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  have hadd2 : Continuous fun w : ParabolicSpace × ParabolicSpace => (w.1 + a, w.2 + a) :=
    (continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)
  refine ⟨⟨fun i x t ht => ?_, fun i j x y => ?_, fun ω i => ?_, fun ω i j => ?_⟩,
    fun ω i x => ?_⟩
  · exact hZ.1.1 i (x + a) t ht
  · simpa using hZ.1.2.1 i j (x + a) (y + a)
  · have := (hZ.1.2.2.1 ω i).comp hadd.continuousOn (s := Ioc (0 : ℝ) 1 ×ˢ T) ?_
    · simpa [Function.comp_def] using this
    · rintro ⟨t, y⟩ ⟨ht, hy⟩
      exact ⟨ht, y, hy, rfl⟩
  · have := (hZ.1.2.2.2 ω i j).comp hadd2.continuousOn (s := T ×ˢ T) ?_
    · simpa [Function.comp_def] using this
    · rintro ⟨y, z⟩ ⟨hy, hz⟩
      exact ⟨⟨y, hy, rfl⟩, z, hz, rfl⟩
  · have := (hZ.2 ω i (x + a)).comp hadd.continuousOn (s := Ioc (0 : ℝ) 1 ×ˢ univ) ?_
    · simpa [Function.comp_def] using this
    · rintro ⟨t, y⟩ ⟨ht, -⟩
      exact ⟨ht, mem_univ _⟩

end RegularityStructures

end

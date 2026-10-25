/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyStatement
public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments

/-!
# Lowering the moment order of the `Π` half premises

`PiHalfPrem.lower`: the moment premises of order `qPi` imply those of every order `1 ≤ m ≤ qPi`,
for random models satisfying the measurability part of `IsContinuousRandomModelWithFieldsOn`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem PiHalfPrem.lower {𝒯 : RegularityStructure ι} {γ κbar θ : ℝ} {Dπ : Set ι}
    {DΓ : Set (ι × ι)} {qPi : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup} {C ε : ℝ}
    {S : Set ParabolicSpace}
    (h : PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε)
    (hV₁ : IsContinuousRandomModelWithFieldsOn Z₁ S)
    (hV₂ : IsContinuousRandomModelWithFieldsOn Z₂ S) {m : ℕ} (hm : 1 ≤ m) (hmq : m ≤ qPi) :
    PiHalfPrem 𝒯 γ κbar θ Dπ DΓ m P Z₁ Z₂ C ε := by
  have hV : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      IsContinuousRandomModelWithFieldsOn Z S := by
    intro Z hZ
    rcases hZ with rfl | hZ
    · exact hV₁
    · rw [mem_singleton_iff] at hZ; exact hZ ▸ hV₂
  exact
    { detPi := h.detPi
      detPiDiff := h.detPiDiff
      detGamma := h.detGamma
      detGammaDiff := h.detGammaDiff
      momPi := fun Z hZ i hi hγ t ht x =>
        probability_natMoment_le_of_higher ((hV Z hZ).1.1 i x t ht.1).aemeasurable hm hmq _
          (h.momPi Z hZ i hi hγ t ht x)
      momPiDiff := fun i hi hγ t ht x =>
        probability_natMoment_le_of_higher
          (((hV₁.1.1 i x t ht.1).sub (hV₂.1.1 i x t ht.1)).aemeasurable) hm hmq _
          (h.momPiDiff i hi hγ t ht x)
      momGamma := fun Z hZ i j hij hγ hj x y =>
        probability_natMoment_le_of_higher ((hV Z hZ).1.2.1 i j x y).aemeasurable hm hmq _
          (h.momGamma Z hZ i j hij hγ hj x y)
      momGammaDiff := fun i j hij hγ hj x y =>
        probability_natMoment_le_of_higher
          (((hV₁.1.2.1 i j x y).sub (hV₂.1.2.1 i j x y)).aemeasurable) hm hmq _
          (h.momGammaDiff i j hij hγ hj x y) }

end RegularityStructures

end

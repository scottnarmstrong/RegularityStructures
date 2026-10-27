module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace GlobalPhi43.Markov

/-- A set measurable after adjoining ambient null events has a representative in the original
sigma-algebra. No completeness assumption is needed on the ambient probability space. -/
theorem ae_representative_adjoin_null {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.generateFrom {A | MeasurableSet A ∧ P A = 0} ⊔ m] s) :
    ∃ t, MeasurableSet[m] t ∧ s =ᵐ[P] t := by
  classical
  let mAE : MeasurableSpace Ω :=
    { MeasurableSet' := fun s => ∃ t, MeasurableSet[m] t ∧ s =ᵐ[P] t
      measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, Filter.EventuallyEq.rfl⟩
      measurableSet_compl := by
        rintro s ⟨t, ht, he⟩
        exact ⟨tᶜ, ht.compl, he.compl⟩
      measurableSet_iUnion := by
        intro s hs
        choose t ht he using hs
        exact ⟨⋃ n, t n, MeasurableSet.iUnion ht, EventuallyEqSet.countable_iUnion he⟩ }
  have hle : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ⊔ m ≤ mAE := by
    apply sup_le
    · apply MeasurableSpace.generateFrom_le
      rintro A ⟨_, hnull⟩
      exact ⟨∅, @MeasurableSet.empty Ω m, ae_eq_empty.mpr hnull⟩
    · intro A hA
      exact ⟨A, hA, Filter.EventuallyEq.rfl⟩
  exact hle s hs

/-- Independence survives adjoining the same ambient null events to both sigma-algebras. -/
theorem indep_adjoin_null {Ω : Type*} {m n : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (hInd : Indep m n P) :
    Indep (MeasurableSpace.generateFrom {A | MeasurableSet A ∧ P A = 0} ⊔ m)
      (MeasurableSpace.generateFrom {A | MeasurableSet A ∧ P A = 0} ⊔ n) P := by
  rw [Indep_iff] at hInd ⊢
  intro s t hs ht
  obtain ⟨s', hs', hes⟩ := ae_representative_adjoin_null P hs
  obtain ⟨t', ht', het⟩ := ae_representative_adjoin_null P ht
  rw [measure_congr (hes.inter het), measure_congr hes, measure_congr het]
  exact hInd s' t' hs' ht'

end GlobalPhi43.Markov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Markov.WindowIndependentParameter
public import GlobalPhi43.Flow.NoiseWindowRestriction
public import Mathlib.Probability.Independence.Basic

/-! Descent from an independent complement. The ambient probability space may
carry extra randomness; only the event being descended belongs to the joined
information field. No regular conditional probability kernel is used. -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace GlobalPhi43.Probability

/-- An event in `J` and `X ∨ O` belongs to the completed `X` field when
`X ≤ J` and all of `J` is independent of `O`. -/
theorem measurableSet_of_independent_complement {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X J O : MeasurableSpace Ω}
    (hX : X ≤ mΩ) (hJ : J ≤ mΩ) (hO : O ≤ mΩ) (hXJ : X ≤ J)
    (hInd : Indep J O P)
    (hnull : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ X)
    {A : Set Ω} (hAJ : MeasurableSet[J] A) (hjoin : MeasurableSet[X ⊔ O] A) :
    MeasurableSet[X] A := by
  classical
  let d : Ω → Ω × Ω := fun ω => (ω, ω)
  have hd : MeasurableSpace.comap d (X.prod O) = X ⊔ O := by
    simp only [MeasurableSpace.prod, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
    change MeasurableSpace.comap id X ⊔ MeasurableSpace.comap id O = X ⊔ O
    simp only [MeasurableSpace.comap_id]
  have hA' : MeasurableSet[MeasurableSpace.comap d (X.prod O)] A := hd.symm ▸ hjoin
  obtain ⟨B, hB, hBA⟩ := hA'
  let Φ : Ω × Ω → ℝ := B.indicator (fun _ => 1)
  have hΦ : @Measurable (Ω × Ω) ℝ (X.prod O) inferInstance Φ :=
    (@measurable_const ℝ (Ω × Ω) inferInstance (X.prod O) (1 : ℝ)).indicator hB
  have hb (p : Ω × Ω) : |Φ p| ≤ 1 := by
    by_cases hp : p ∈ B <;> simp only [Φ, Set.indicator_apply, hp, ite_true, ite_false,
      abs_one, abs_zero, zero_le_one, le_refl]
  have hphi : (fun ω => Φ (ω, ω)) = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hp : (ω, ω) ∈ B <;> simp [Φ, ← hBA, d, hp]
  have hiJ : @Measurable Ω Ω J X id := fun S hS => hXJ S hS
  have hiX : @Measurable Ω Ω X X id := @measurable_id Ω X
  have hIndX : Indep X O P := indep_of_indep_of_le hInd hXJ le_rfl
  have hj := Markov.condExp_of_indep_param_window (mΩ := mΩ) (mE := X) P hJ hO hInd
    (X := id) hiJ (Φ := Φ) hΦ hb
  have hx := Markov.condExp_of_indep_param_window (mΩ := mΩ) (mE := X) P hX hO hIndX
    (X := id) hiX (Φ := Φ) hΦ hb
  have hfi : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (hJ _ hAJ)
  have hself := condExp_of_stronglyMeasurable hJ
    ((@stronglyMeasurable_const Ω ℝ J _ (1 : ℝ)).indicator hAJ) hfi
  have he : A.indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      P[A.indicator (fun _ => (1 : ℝ)) | X] := by
    simpa only [id_eq, hphi, hself] using hj.trans hx.symm
  have hlocal := Flow.measurable_of_ae_eq_of_null_le (mΩ := mΩ) P hX hnull
    ((@measurable_const ℝ Ω _ mΩ (1 : ℝ)).indicator (hJ _ hAJ))
    (show Measurable[X] (P[A.indicator (fun _ => (1 : ℝ)) | X]) from
      stronglyMeasurable_condExp.measurable) he
  convert hlocal (measurableSet_singleton (1 : ℝ)) using 1
  ext ω
  by_cases hω : ω ∈ A <;> simp [hω]

/-- Completed independent-complement descent. Every displayed information-field
hypothesis is internal infrastructure to be proved in the white-noise application. -/
theorem independent_complement_descent {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : MeasurableSpace Ω)
    (H O : ℕ → MeasurableSpace Ω) (hH : ∀ n, H n ≤ mΩ) (hO : ∀ n, O n ≤ mΩ)
    (hXH : ∀ n, X ≤ H n) (hmono : Monotone O) (hInd : ∀ n, Indep (H n) (O n) P)
    (hjoin : H 0 ≤ X ⊔ ⨆ n, O n)
    (hnull : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ X) :
    (⨅ n, H n) = X := by
  let J := ⨅ n, H n
  have hJ : J ≤ mΩ := (iInf_le H 0).trans (hH 0)
  have hX : X ≤ mΩ := (hXH 0).trans (hH 0)
  have hXJ : X ≤ J := le_iInf hXH
  have hJO : J ≤ X ⊔ ⨆ n, O n := (iInf_le H 0).trans hjoin
  have hind : Indep J (⨆ n, O n) P :=
    (indep_iSup_of_monotone
      (fun n => (indep_of_indep_of_le (hInd n) (iInf_le H n) le_rfl).symm)
      hO hJ hmono).symm
  apply le_antisymm _ hXJ
  intro A hA
  exact measurableSet_of_independent_complement (mΩ := mΩ) P hX hJ (iSup_le hO) hXJ hind hnull hA
    (hJO _ hA)

end GlobalPhi43.Probability

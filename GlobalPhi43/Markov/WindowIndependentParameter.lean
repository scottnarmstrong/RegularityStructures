module

public import GlobalPhi43.Markov.IndependentParameter

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace GlobalPhi43.Markov


/-- Conditioning with independent information from a future window.
The independent sigma-algebra may live on the original sample space, with no countability or standard-Borel assumption. -/
theorem condExp_of_indep_param_window {Ω E : Type*} {m n : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ) (hn : n ≤ mΩ)
    (hInd : Indep m n P) {X : Ω → E} (hX : Measurable[m] X)
    {Φ : E × Ω → ℝ} (hΦ : @Measurable (E × Ω) ℝ (mE.prod n) inferInstance Φ)
    {C : ℝ} (hb : ∀ p, |Φ p| ≤ C) :
    P[fun ω => Φ (X ω, ω) | m] =ᵐ[P] fun ω => ∫ ω', Φ (X ω, ω') ∂P := by
  have hId : @Measurable Ω Ω mΩ n id := fun s hs => hn s hs
  have hi : Indep m (MeasurableSpace.comap (id : Ω → Ω) n) P := by
    simpa only [MeasurableSpace.comap_id] using hInd
  have he := @condExp_of_indep_param Ω E Ω m mΩ mE n P _ hm X id hX hId hi Φ hΦ C hb
  refine he.trans ?_
  apply ae_of_all
  intro ω
  have hsec : @Measurable Ω ℝ n inferInstance (fun ω' => Φ (X ω, ω')) :=
    hΦ.comp (@measurable_prodMk_left E Ω mE n (X ω))
  exact @integral_map_of_stronglyMeasurable Ω ℝ _ _ mΩ P Ω n id hId _ hsec.stronglyMeasurable

end GlobalPhi43.Markov

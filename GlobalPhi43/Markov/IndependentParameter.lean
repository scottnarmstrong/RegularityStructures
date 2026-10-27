module

public import GlobalPhi43.Markov.IndependentIntegral
public import Mathlib.Probability.ConditionalExpectation

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace GlobalPhi43.Markov

/-- Conditioning with an independent parameter for a bounded product-measurable integrand.
The independent carrier need not be standard Borel. The conditioning sigma-algebra can contain
more information than the initial datum alone. -/
theorem condExp_of_indep_param {Ω E Z : Type*}
    {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} {Y : Ω → Z} (hX : Measurable[m] X) (hY : Measurable Y)
    (hInd : Indep m (MeasurableSpace.comap Y inferInstance) P)
    {Φ : E × Z → ℝ} (hΦ : Measurable Φ) {C : ℝ} (hb : ∀ p, |Φ p| ≤ C) :
    P[fun ω => Φ (X ω, Y ω) | m] =ᵐ[P]
      fun ω => ∫ y, Φ (X ω, y) ∂P.map Y := by
  classical
  let G : E → ℝ := fun x => ∫ y, Φ (x, y) ∂P.map Y
  have hG : Measurable G := hΦ.stronglyMeasurable.integral_prod_right'.measurable
  have hGb (x : E) : |G x| ≤ max C 0 := by
    have hh := norm_integral_le_of_norm_le_const (μ := P.map Y) (f := fun y => Φ (x, y)) (C := max C 0)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using (hb (x, y)).trans (le_max_left C 0))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh
  have hX' : Measurable X := hX.mono hm le_rfl
  have hfi : Integrable (fun ω => Φ (X ω, Y ω)) P :=
    Integrable.of_bound (hΦ.comp (hX'.prodMk hY)).aestronglyMeasurable C
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb (X ω, Y ω))
  have hgi : Integrable (fun ω => G (X ω)) P :=
    Integrable.of_bound (hG.comp hX').aestronglyMeasurable (max C 0)
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hGb (X ω))
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hfi
    (fun s _ _ => hgi.integrableOn) ?_ (hG.comp hX).stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  have hs' : MeasurableSet s := hm s hs
  let V : Ω → E × Bool := fun ω => (X ω, if ω ∈ s then true else false)
  have hV : Measurable[m] V := hX.prodMk (Measurable.ite hs measurable_const measurable_const)
  have hV' : Measurable V := hV.mono hm le_rfl
  have hVY : IndepFun V Y P :=
    indep_of_indep_of_le hInd hV.comap_le le_rfl
  let H : (E × Bool) × Z → ℝ := fun q => if q.1.2 = true then Φ (q.1.1, q.2) else 0
  have hH : Measurable H := Measurable.ite
    (measurable_fst.snd (measurableSet_singleton true))
    (hΦ.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have hHb (q : (E × Bool) × Z) : |H q| ≤ max C 0 := by
    dsimp [H]
    split_ifs
    · exact (hb _).trans (le_max_left _ _)
    · simpa only [abs_zero] using le_max_right C 0
  have he := integral_independent_pair P hV' hY hVY hH hHb
  have hinner : AEStronglyMeasurable (fun v : E × Bool => ∫ y, H (v, y) ∂P.map Y) (P.map V) :=
    hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  rw [integral_map hV'.aemeasurable hinner] at he
  have hleft : (fun ω => H (V ω, Y ω)) = s.indicator (fun ω => Φ (X ω, Y ω)) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [H, V, hω]
  have hright : (fun ω => ∫ y, H (V ω, y) ∂P.map Y) = s.indicator (fun ω => G (X ω)) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [H, V, G, hω]
  rw [hleft, hright, integral_indicator hs', integral_indicator hs'] at he
  exact he.symm

end GlobalPhi43.Markov

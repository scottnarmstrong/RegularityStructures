module

public import GlobalPhi43.Markov.WindowIndependentParameter
public import Mathlib.Probability.Kernel.MeasurableIntegral

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace GlobalPhi43.Markov

/-- The generic conditional Markov step: independent future information, the measurable
restart substitution and deterministic-data law identification imply the conditional identity.
All flow properties are explicit hypotheses. -/
theorem conditional_markov_from_restart {Ω E : Type*} {m n : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ) (hn : n ≤ mΩ)
    (hInd : Indep m n P) {X U : Ω → E} (hX : Measurable[m] X)
    {F : E × Ω → E} (hF : @Measurable (E × Ω) E (mE.prod n) mE F)
    (κ : Kernel E E) (hlaw : ∀ x, P.map (fun ω => F (x, ω)) = κ x)
    (hrestart : U =ᵐ[P] fun ω => F (X ω, ω))
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ y, |f y| ≤ C) :
    P[fun ω => f (U ω) | m] =ᵐ[P] fun ω => ∫ y, f y ∂κ (X ω) := by
  have hΦ : @Measurable (E × Ω) ℝ (mE.prod n) inferInstance (fun p => f (F p)) := hf.comp hF
  have he := condExp_of_indep_param_window P hm hn hInd hX hΦ (fun p => hb (F p))
  have hmsec (x : E) : Measurable (fun ω => F (x, ω)) := by
    have hh : @Measurable Ω E n mE (fun ω => F (x, ω)) :=
      hF.comp (@measurable_prodMk_left E Ω mE n x)
    exact hh.mono hn le_rfl
  refine (condExp_congr_ae (hrestart.fun_comp f)).trans (he.trans ?_)
  apply ae_of_all
  intro ω
  dsimp only
  rw [← hlaw (X ω)]
  exact (integral_map (hmsec _).aemeasurable hf.stronglyMeasurable.aestronglyMeasurable).symm

/-- Taking expectations in the conditional Markov identity gives the kernel action law. -/
theorem integral_eq_iterated_of_conditional {Ω E : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {X U : Ω → E} (hX : Measurable X) (κ : Kernel E E) [IsSFiniteKernel κ]
    {f : E → ℝ} (hf : Measurable f)
    (hc : P[fun ω => f (U ω) | m] =ᵐ[P] fun ω => ∫ y, f y ∂κ (X ω)) :
    (∫ ω, f (U ω) ∂P) = ∫ x, ∫ y, f y ∂κ x ∂P.map X := by
  rw [← integral_condExp hm, integral_congr_ae hc]
  exact (integral_map hX.aemeasurable hf.stronglyMeasurable.integral_kernel.aestronglyMeasurable).symm

end GlobalPhi43.Markov

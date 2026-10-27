module

public import GlobalPhi43.Invariant.StationaryProduct
public import GlobalPhi43.Invariant.WhiteNoiseProduct
public import GlobalPhi43.Markov.FlowFiniteDimensional
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Conditional stationary solution on the prescribed product space -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures
open scoped NNReal

namespace GlobalPhi43.Invariant

open GlobalPhi43.Markov

/-- The selected flow has stationary laws on P.prod mu, with lifted
white noise independent of the initial coordinate. The flow and its Markov properties,
together with the invariant probability, are explicit hypotheses. -/
theorem stationary_flow_product {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {η : NegExponent}
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hj : Measurable (fun q : (ℝ≥0 × HolderBesov η) × Ω => u q.1.1 0 q.1.2 q.2))
    (μ : ProbabilityMeasure (HolderBesov η))
    (hinv : ∀ s, flowObservationKernel P u hj s ∘ₘ (μ : Measure (HolderBesov η)) = (μ : Measure (HolderBesov η)))
    (m : ℝ≥0 → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (ha : ∀ s x, Measurable[m s] (u s 0 x)) (hzero : ∀ x, u 0 0 x =ᵐ[P] fun _ => x)
    (hc : ∀ s t, s ≤ t → ∀ x (g : HolderBesov η → ℝ),
      Measurable g → (∀ y, ‖g y‖ ≤ 1) →
      P[fun ω => g (u t 0 x ω) | m s] =ᵐ[P]
        fun ω => flowTransition P u (t - s : ℝ≥0) g (u s 0 x ω)) :
    IsWhiteNoise (P.prod (μ : Measure (HolderBesov η))) (fun h p => W h p.1) ∧
      (P.prod (μ : Measure (HolderBesov η))).map Prod.snd = (μ : Measure (HolderBesov η)) ∧
      IndepFun (fun p : Ω × HolderBesov η => p.2)
        (fun p : Ω × HolderBesov η => fun h : {h : SpaceTime → ℝ // MemLp h 2} => W h.val p.1)
        (P.prod (μ : Measure (HolderBesov η))) ∧
      Measurable (fun p : ℝ≥0 × (Ω × HolderBesov η) => u p.1 0 p.2.2 p.2.1) ∧
      (∀ t : ℝ≥0, (P.prod (μ : Measure (HolderBesov η))).map
        (fun p : Ω × HolderBesov η => u t 0 p.2 p.1) = (μ : Measure (HolderBesov η))) ∧
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ r : ℝ≥0,
        (P.prod (μ : Measure (HolderBesov η))).map (fun p (i : Fin (n + 1)) => u (r + t i) 0 p.2 p.1) =
          (P.prod (μ : Measure (HolderBesov η))).map (fun p (i : Fin (n + 1)) => u (t i) 0 p.2 p.1) := by
  have hs (t : ℝ≥0) : Measurable (fun p : Ω × HolderBesov η => u t 0 p.2 p.1) :=
    hj.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have htime : Measurable (fun p : ℝ≥0 × (Ω × HolderBesov η) => u p.1 0 p.2.2 p.2.1) :=
    hj.comp ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd))
  refine ⟨isWhiteNoise_product P (μ : Measure (HolderBesov η)) W hW,
    initial_product_law P (μ : Measure (HolderBesov η)), initial_indep_l2Noise_product P (μ : Measure (HolderBesov η)) W hW,
    htime, ?_, ?_⟩
  · exact product_oneTime_law P (μ : Measure (HolderBesov η)) (flowObservationKernel P u hj) hinv
      (fun t x => u t 0 x) hs (fun _ _ => rfl)
  · intro n t ht r
    exact product_fdd_stationary P (μ : Measure (HolderBesov η)) (flowObservationKernel P u hj) hinv
      (fun t x => u t 0 x) hs m hm hmono ha hzero hc t ht r

end GlobalPhi43.Invariant

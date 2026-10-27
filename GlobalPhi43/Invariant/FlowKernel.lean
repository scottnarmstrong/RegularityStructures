module

public import GlobalPhi43Statements.Defs.IsFellerMarkovFlow
public import Mathlib.Probability.Kernel.Composition.Comp

/-! # The law semigroup of a Feller Markov flow -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Set
open scoped NNReal BoundedContinuousFunction

namespace GlobalPhi43.Invariant

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}

/-- Law measurability of the Feller Markov flow defines a kernel of its sample laws. -/
def flowKernel (h : IsFellerMarkovFlow P W u) (t : ℝ≥0) :
    Kernel (HolderBesov η) (HolderBesov η) where
  toFun x := flowLaw P u t x
  measurable' := by
    apply Measure.measurable_measure.mpr
    intro A hA
    exact (h.2.1 A hA).comp
      ((measurable_const (a := (⟨t, t.property⟩ : Ici (0 : ℝ)))).prodMk measurable_id)

instance flowKernel_isMarkovKernel (h : IsFellerMarkovFlow P W u) (t : ℝ≥0) :
    IsMarkovKernel (flowKernel h t) := ⟨fun x => h.1 t t.property x⟩

/-- The addition order matches kernel composition: first s, then t. -/
theorem flowKernel_semigroup (h : IsFellerMarkovFlow P W u) (s t : ℝ≥0) :
    flowKernel h (s + t) = flowKernel h t ∘ₖ flowKernel h s := by
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  exact h.2.2.2.1 t s t.property s.property x A hA

/-- The flow transition action has the Feller property. -/
theorem flowKernel_feller (h : IsFellerMarkovFlow P W u)
    (t : ℝ≥0) (f : HolderBesov η →ᵇ ℝ) :
    Continuous (fun x => ∫ y, f y ∂flowKernel h t x) :=
  ((h.2.2.2.2.2 f).1 t t.property).1

/-- The Feller Markov flow has jointly measurable nonnegative-time orbit laws. -/
theorem measurable_flowLaw_orbit (h : IsFellerMarkovFlow P W u) (z : HolderBesov η) :
    Measurable (fun t : Ici (0 : ℝ) => flowLaw P u t z) := by
  apply Measure.measurable_measure.mpr
  intro A hA
  exact (h.2.1 A hA).comp (measurable_id.prodMk measurable_const)

end GlobalPhi43.Invariant

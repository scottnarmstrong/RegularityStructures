module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import GlobalPhi43.Markov.Measurability

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GlobalPhi43.Markov

variable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace E]

/-- The law of a jointly measurable sampled map, as a kernel in its parameter. -/
def sampleKernel (P : Measure Ω) [SFinite P] (F : A × Ω → E) (hF : Measurable F) : Kernel A E where
  toFun a := P.map fun ω => F (a, ω)
  measurable' := by
    apply Measure.measurable_measure.mpr
    intro S hS
    have hm (a : A) : Measurable (fun ω => F (a, ω)) := hF.comp measurable_prodMk_left
    have he (a : A) : P.map (fun ω => F (a, ω)) S = P (Prod.mk a ⁻¹' F ⁻¹' S) :=
      Measure.map_apply (hm a) hS
    simp_rw [he]
    exact measurable_measure_prodMk_left (hF hS)

instance sampleKernel_isMarkovKernel (P : Measure Ω) [IsProbabilityMeasure P]
    (F : A × Ω → E) (hF : Measurable F) : IsMarkovKernel (sampleKernel P F hF) := by
  constructor
  intro a
  change IsProbabilityMeasure (P.map (fun ω => F (a, ω)))
  exact (Measure.isProbabilityMeasure_map_iff (hF.comp measurable_prodMk_left).aemeasurable).mpr inferInstance

/-- Kernel evaluation is measurable in the whole parameter, which may include time. -/
theorem measurable_sampleKernel_apply (P : Measure Ω) [SFinite P]
    (F : A × Ω → E) (hF : Measurable F) {S : Set E} (hS : MeasurableSet S) :
    Measurable (fun a => sampleKernel P F hF a S) :=
  (sampleKernel P F hF).measurable_coe hS

end GlobalPhi43.Markov

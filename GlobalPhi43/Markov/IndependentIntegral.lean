module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Prod

public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace GlobalPhi43.Markov

/-- Fubini for a bounded measurable function of two independent random variables.
This form avoids any standard-Borel hypothesis on the independent information carrier. -/
theorem integral_independent_pair {Ω E Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → E} {Y : Ω → Z}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Φ : E × Z → ℝ} (hΦ : Measurable Φ) {C : ℝ} (hb : ∀ p, |Φ p| ≤ C) :
    (∫ ω, Φ (X ω, Y ω) ∂P) = ∫ x, ∫ y, Φ (x, y) ∂P.map Y ∂P.map X := by
  have hi : Integrable Φ ((P.map X).prod (P.map Y)) :=
    Integrable.of_bound hΦ.aestronglyMeasurable C (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p)
  calc
    _ = ∫ p, Φ p ∂P.map (fun ω => (X ω, Y ω)) :=
      (integral_map (hX.prodMk hY).aemeasurable hΦ.stronglyMeasurable.aestronglyMeasurable).symm
    _ = _ := by rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]; exact integral_prod Φ hi

end GlobalPhi43.Markov

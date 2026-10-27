module

public import GlobalPhi43.Proofs.RegularisedKernelAssembly
public import GlobalPhi43.Flow.ReferenceClassicalFamily

/-! # Fixed-reference majorants and a moment profile independent of the noise space -/

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Attachment GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

universe u

/-- K(a,alpha) is the shared moment profile at the fixed reference
mollifier and defect-bound coefficient. -/
def referenceMomentProfile (a α : ℝ) : ℝ → ℝ≥0 :=
  regularisedProfile.{u} a α referencePhi0 referencePhi0_isMollifier

/-- Actual reference classical paths have one majorant before p, with the
shared profile fixed before the source space. The majorants are obtained from
the regularised solution bounds. -/
theorem reference_regularised_majorants (a α : ℝ)
    (hα : α ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    ∃ M : ℝ → Ω → ℝ,
      (∀ ε ∈ Ioc (0 : ℝ) 1, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω (x : C(Torus3, ℝ)), IsSmoothOnTorus x →
        ∀ t ∈ Ioc (0 : ℝ) 1,
          ENNReal.ofReal (√t) * holderBesovENorm α
            (Flow.referenceClassicalFamily P W hW a ε x ω t) ≤ ENNReal.ofReal (M ε ω)) ∧
      ∀ p : ℝ, 1 ≤ p →
        (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P) ≤
          referenceMomentProfile.{u} a α p := by
  exact regularisedBound_profile.{u} a α hα referencePhi0 referencePhi0_isMollifier P W hW
    (referenceNoiseFamily P W hW) (fun _ he => referenceNoiseFamily_spec P W hW he)
    (Flow.referenceClassicalFamily P W hW a)
    (fun _ he x hx ω => Flow.referenceClassicalFamily_spec P W hW a he x hx ω)

end GlobalPhi43.Assembly

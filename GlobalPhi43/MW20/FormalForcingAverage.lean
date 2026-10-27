module

public import GlobalPhi43.MW20.SourceExpansionHeat
public import GlobalPhi43.MW20.GlobalHeatSmoothing
public import GlobalPhi43.MW20.PastBallTesting
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.ExpansionForcingAlgebra

/-! The actual formal forcing and its kernel average, before any PDE
substitution. These identities also apply to augmented local data. -/

@[expose] public noncomputable section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

def sourceFormalForcing (v J V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (x z : ParabolicSpace) : ℝ :=
  -v z^3 - 3*(v z^2*J z) - 3*(v z-v x)*V z - 9*C₂*(v z+J z)

def sourceFormalForcingAverage (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J V : ParabolicSpace → ℝ) (C₂ T : ℝ) (hT : 0 < T)
    (x y : ParabolicSpace) : ℝ :=
  pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (sourceFormalForcing v J V C₂ x) y

/-- Literal integral consumed by the augmented local-data identity. -/
theorem sourceFormalForcingAverage_eq_integral
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J V : ParabolicSpace → ℝ) (C₂ T : ℝ) (hT : 0 < T) (x y : ParabolicSpace) :
    sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y =
      ∫ w, -v (y+w)^3 - 3*v (y+w)^2*J (y+w) -
        3*(v (y+w)-v x)*V (y+w) - 9*C₂*(v (y+w)+J (y+w))
        ∂infiniteKernelMeasure Φ hΦ T hT := by
  unfold sourceFormalForcingAverage pastSmooth
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  unfold sourceFormalForcing
  ring

/-- The complete signed expansion into the actual product and counterterm
pairings. Integrability comes from the actual compact sampling domain. -/
theorem sourceFormalForcingAverage_split
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContinuousOn v sourceClosedCylinder) (hJ : ContinuousOn J sourceClosedCylinder)
    (hV : ContinuousOn V sourceClosedCylinder)
    {T L r d : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (x : ParabolicSpace) (hball : Local.pastBall x (L+T) ⊆ Local.cylinderInterior r d)
    {y : ParabolicSpace} (hy : y ∈ Local.pastBall x L) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y =
      -pastSmooth μ (fun z => v z^3) y - 3*pastSmooth μ (fun z => v z^2*J z) y -
      3*(v y-v x)*pastSmooth μ V y - 3*pastSmooth μ (fun z => (v z-v y)*V z) y -
      9*C₂*(pastSmooth μ v y+pastSmooth μ J y) := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  let μ := infiniteKernelMeasure Φ hΦ T hT
  have hsample : ∀ᵐ z ∂μ, y+z ∈ sourceClosedCylinder := by
    filter_upwards [infiniteKernelMeasure_ae_testingDomain Φ hΦ hT hT1 hball hy] with z hz
    exact sourceCylinder_subset_closed hr (mixedInterior_subset_base hd hz)
  have hi (f : ParabolicSpace → ℝ) (hf : ContinuousOn f sourceClosedCylinder) :
      Integrable (fun z => f (y+z)) μ :=
    integrable_comp_of_ae_mem_compact μ f isCompact_Icc hf (fun z => y+z)
      (continuous_const.add continuous_id) hsample
  have hiv := hi v hv
  have hiJ := hi J hJ
  have hiV := hi V hV
  have hi3 := hi (fun z => v z^3) (hv.pow 3)
  have hi2J := hi (fun z => v z^2*J z) ((hv.pow 2).mul hJ)
  have hiRec := hi (fun z => (v z-v y)*V z) ((hv.sub continuousOn_const).mul hV)
  change (∫ z, sourceFormalForcing v J V C₂ x (y+z) ∂μ) = _
  calc
    _ = ∫ z, -v (y+z)^3 - 3*(v (y+z)^2*J (y+z)) -
        (3*(v y-v x))*V (y+z) - 3*((v (y+z)-v y)*V (y+z)) -
        (9*C₂)*(v (y+z)+J (y+z)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      unfold sourceFormalForcing
      ring
    _ = _ := by
      have ha := integral_sub hi3.neg (hi2J.const_mul 3)
      have hb := integral_sub (hi3.neg.sub (hi2J.const_mul 3)) (hiV.const_mul (3*(v y-v x)))
      have hc := integral_sub ((hi3.neg.sub (hi2J.const_mul 3)).sub
        (hiV.const_mul (3*(v y-v x)))) (hiRec.const_mul 3)
      have hd := integral_sub (((hi3.neg.sub (hi2J.const_mul 3)).sub
        (hiV.const_mul (3*(v y-v x)))).sub (hiRec.const_mul 3))
        ((hiv.add hiJ).const_mul (9*C₂))
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at ha hb hc hd
      rw [hd, hc, hb, ha, integral_neg, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_add hiv hiJ]
      rfl

end GlobalPhi43.MW20

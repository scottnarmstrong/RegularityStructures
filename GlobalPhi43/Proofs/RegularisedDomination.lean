module

public import GlobalPhi43.Proofs.RegularisedProfile
public import GlobalPhi43.Flow.ClassicalTranslation
public import GlobalPhi43.Attachment.SmoothNoiseSliceLaw
public import GlobalPhi43.Compactness.Lifting

/-! Pointwise algebra and uniqueness for arbitrary classical paths.
A physical-cover bound on the remainder yields a bound at every outcome,
without restricting to a probabilistic event. -/

@[expose] public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment MW20
open scoped NNReal ENNReal

/-- Add the actual J slice to an actual remainder bound, with the original
signed difference. The conclusion holds for the supplied solution. -/
theorem weighted_classical_norm_of_remainder {η : ℝ} (hη : η≤0)
    (u J : C(Torus3,ℝ)) (w B S : ENNReal)
    (hrem : w*‖u-J‖ₑ ≤ B) (hJ : w*holderBesovENorm η J ≤ S) :
    w*holderBesovENorm η u ≤ B+S := by
  have hadd : holderBesovENorm η u ≤ holderBesovENorm η (u-J)+holderBesovENorm η J := by
    simpa only [sub_add_cancel] using holderBesovENorm_add_le η (u-J) J
  have hsup : w*holderBesovENorm η (u-J) ≤ w*‖u-J‖ₑ := by
    simpa only [mul_comm] using mul_le_mul_left (holderBesovENorm_le hη (u-J)) w
  calc _ ≤ w*(holderBesovENorm η (u-J)+holderBesovENorm η J) := by gcongr
    _ = w*holderBesovENorm η (u-J)+w*holderBesovENorm η J := mul_add _ _ _
    _ ≤ B+S := add_le_add (hsup.trans hrem) hJ

/-- Uniqueness, lowering the exponent and adding the actual slice preserve the
literal sourceMajorant, at every outcome (without a growth hypothesis). -/
theorem sourceMajorant_dominates_classical_of_remainder {Ω : Type*}
    (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (ρ : ParabolicSpace → ℝ) (a : ℝ) (C : ℝ≥0)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hs : ∀ ε ∈ Ioc (0:ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    {ε : ℝ} (he : ε ∈ Ioc (0:ℝ) 1) (ω : Ω)
    (x : C(Torus3,ℝ)) (hx : IsSmoothOnTorus x)
    (u : ℝ → C(Torus3,ℝ))
    (hu : IsClassicalSolution (a+3*wickConstant ρ ε-9*sunsetConstant ρ ε) (ξ ε ω) x u)
    {t η : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) (hη : η ≤ (Flow.lossExponent κ : ℝ))
    (hrem : ENNReal.ofReal (Real.sqrt t) *
      ‖Flow.smoothSolution (a+3*wickConstant ρ ε-9*sunsetConstant ρ ε)
        (ξ ε ω) (hs ε he ω) x hx t - smoothNoiseJ 5 ⟨ξ ε ω,hs ε he ω⟩ t‖ₑ ≤
      2*(C:ENNReal)*max 2 (attachmentFunctional 5 κ Φ hΦ (ξ ε ω)
        (wickConstant ρ ε+a/3,sunsetConstant ρ ε+0) (Flow.coverRegion 0))) :
    ENNReal.ofReal (Real.sqrt t)*holderBesovENorm η (u t) ≤
      ENNReal.ofReal (sourceMajorant κ Φ hΦ ρ a C ξ hs ε ω) := by
  have heq := Flow.smoothSolution_eq_classical _ _ (hs ε he ω) x hx hu ht.1.le
  rw [heq] at hrem
  have hslice : ENNReal.ofReal (Real.sqrt t)*holderBesovENorm (Flow.lossExponent κ)
      (smoothNoiseJ 5 ⟨ξ ε ω,hs ε he ω⟩ t) ≤
      noiseSlice 5 (Flow.lossExponent κ) 0 (ξ ε) (hs ε he) ω := by
    have hh := le_iSup (fun q : Ioc (0:ℝ) 1 =>
      ENNReal.ofReal (Real.sqrt q.val)*holderBesovENorm (Flow.lossExponent κ)
        (smoothNoiseJ 5 ⟨ξ ε ω,hs ε he ω⟩ (0+q.val))) ⟨t,ht⟩
    simpa only [noiseSlice,smoothNoiseSlice,asSmoothNoise,zero_add] using hh
  have hb := weighted_classical_norm_of_remainder (Flow.lossExponent κ).2.le _ _ _ _ _ hrem hslice
  have hm : ENNReal.ofReal (Real.sqrt t)*holderBesovENorm η (u t) ≤
      ENNReal.ofReal (Real.sqrt t)*holderBesovENorm (Flow.lossExponent κ) (u t) := by
    gcongr
    exact holderBesovENorm_mono hη _
  apply (hm.trans hb).trans_eq
  rw [ofReal_sourceMajorant κ Φ hΦ ρ a C ξ hs ε he ω,
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2), ENNReal.ofReal_coe_nnreal]
  norm_num

end GlobalPhi43

module

public import GlobalPhi43.Attachment.ProbePsiAverage
public import RegularityStructures.PDE.Duhamel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.PDE Set

/-- Reverse the actual Duhamel integral to its positive heat-time variable. -/
theorem duhamel_heat_time (F : ℝ → C(Torus3,ℝ)) (r : ℝ) :
    duhamel F r = ∫ σ in (0:ℝ)..r, heatOp σ (F (r-σ)) := by
  have hh := intervalIntegral.integral_comp_sub_left
    (fun σ => heatOp σ (F (r-σ))) r (a := 0) (b := r)
  simpa only [duhamel,sub_self,sub_zero,sub_sub_cancel] using hh

/-- Heat characterization plus contraction, compared only at positive heat
times. The singular power is integrable; no estimate at heat time zero is used. -/
theorem duhamel_holder_forcing_bound (η : NegExponent) (hη : -2 < (η:ℝ))
    (F : ℝ → C(Torus3,ℝ)) (hF : Continuous F) (P : ℝ → C(Torus3,ℝ))
    {r : ℝ} (hr : r ∈ Ioc (0:ℝ) 1) (Y E : ℝ) (hY : 0≤Y)
    (hP : ∀ σ ∈ Ioc (0:ℝ) r, holderBesovENorm η (P σ) ≤ ENNReal.ofReal Y)
    (hErr : ∀ σ ∈ Ioc (0:ℝ) r, ‖F (r-σ)-P σ‖ ≤ E) :
    ‖duhamel F r‖ ≤ r^((η:ℝ)/2+1)/((η:ℝ)/2+1)*Y+r*E := by
  have hα : -1 < (η:ℝ)/2 := by linarith
  have hβ : 0 < (η:ℝ)/2+1 := by linarith
  have hi : IntervalIntegrable (fun σ => heatOp σ (F (r-σ))) volume 0 r :=
    (continuous_heatOp.comp (continuous_id.prodMk
      (hF.comp (continuous_const.sub continuous_id)))).intervalIntegrable 0 r
  have hp : IntervalIntegrable (fun σ : ℝ => σ^((η:ℝ)/2)) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow' hα
  have hb (σ : ℝ) (hσ : σ ∈ Ioo (0:ℝ) r) :
      ‖heatOp σ (F (r-σ))‖ ≤ σ^((η:ℝ)/2)*Y+E := by
    have hs : σ ∈ Ioc (0:ℝ) r := ⟨hσ.1,hσ.2.le⟩
    have hheat := Potential.norm_heatOp_le_of_holderBesovENorm_le (η:ℝ)
      ⟨hσ.1,hσ.2.le.trans hr.2⟩ hY (hP σ hs)
    have he : F (r-σ) = P σ+(F (r-σ)-P σ) := by abel
    rw [he,heatOp_add]
    exact (norm_add_le _ _).trans
      (add_le_add hheat ((norm_heatOp_le σ _).trans (hErr σ hs)))
  rw [duhamel_heat_time]
  calc
    _ ≤ ∫ σ in (0:ℝ)..r, ‖heatOp σ (F (r-σ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hr.1.le
    _ ≤ ∫ σ in (0:ℝ)..r, σ^((η:ℝ)/2)*Y+E :=
      intervalIntegral.integral_mono_on_of_le_Ioo hr.1.le hi.norm
        ((hp.mul_const Y).add intervalIntegrable_const) hb
    _ = _ := by
      rw [intervalIntegral.integral_add (hp.mul_const Y) intervalIntegrable_const,
        intervalIntegral.integral_mul_const,intervalIntegral.integral_const,
        integral_rpow (Or.inl hα)]
      simp only [Real.zero_rpow hβ.ne',sub_zero,smul_eq_mul]

end GlobalPhi43.Attachment

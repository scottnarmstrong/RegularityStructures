module

public import GlobalPhi43.Attachment.ProbeTimeCutoff
public import GlobalPhi43.Compactness.Embedding
public import Phi43.Potential.HolderContraction
public import RegularityStructures.PDE.HeatOp

/-! The matching averaged potential probe, at its actual input exponent.
No Gaussian compact-test estimate or averaged-potential estimate is assumed. -/

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.PDE
open scoped ENNReal

namespace GlobalPhi43.Attachment

def probePotentialWindow (η : NegExponent) (ψ : C(ℝ, C(Torus3, ℝ))) (s : ℝ) :
    C(Icc s (s + 1), HolderBesov η) where
  toFun r := toHolderBesov η (ψ r)
  continuous_toFun := (lipschitzWith_toHolderBesov η).continuous.comp
    (ψ.continuous.comp continuous_subtype_val)
theorem probePotentialWindow_bound (η : NegExponent) (ψ : C(ℝ, C(Torus3, ℝ)))
    (s : ℝ) {r : ℝ} (hr : r ∈ Icc s (s+1)) :
    holderBesovENorm η (ψ r) ≤ ENNReal.ofReal ‖probePotentialWindow η ψ s‖ := by
  rw [← ENNReal.ofReal_toReal (holderBesovENorm_lt_top η.property.le (ψ r)).ne]
  apply ENNReal.ofReal_le_ofReal
  rw [← norm_toHolderBesov]
  exact (probePotentialWindow η ψ s).norm_coe_le_norm ⟨r, hr⟩

def probePsiAverage (ψ : C(ℝ, C(Torus3, ℝ))) (s t : ℝ) : C(Torus3, ℝ) :=
  ∫ r : ℝ, probeTimeWeight t r • heatOp r (ψ (s+t-r))

theorem probePsiAverage_integrable (ψ : C(ℝ, C(Torus3, ℝ))) (s : ℝ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun r : ℝ => probeTimeWeight t r • heatOp r (ψ (s+t-r))) := by
  have hc : Continuous (fun r : ℝ => probeTimeWeight t r • heatOp r (ψ (s+t-r))) :=
    (probeTimeWeight_smooth t).continuous.smul
      (continuous_heatOp.comp (continuous_id.prodMk
        (ψ.continuous.comp (continuous_const.sub continuous_id))))
  exact hc.integrable_of_hasCompactSupport ((probeTimeWeight_compact ht).smul_right)

/-- The source positive-time averaging window preserves the actual eta norm.
The constant is fixed before the potential, start, or observation scale. -/
theorem probePsiAverage_bound (η : NegExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ψ : C(ℝ, C(Torus3, ℝ))) (s : ℝ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) 1 →
      ‖probePsiAverage ψ s t‖ ≤ c * t ^ ((η : ℝ) / 2) * ‖probePotentialWindow η ψ s‖ := by
  let c : ℝ := (1 / 2 : ℝ) ^ ((η : ℝ) / 2)
  refine ⟨c, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro ψ s t ht
  let B := c * t ^ ((η : ℝ) / 2) * ‖probePotentialWindow η ψ s‖
  have hi := probePsiAverage_integrable ψ s ht.1
  have hw : Integrable (fun r : ℝ => probeTimeWeight t r * B) volume :=
    ((probeTimeWeight_smooth t).continuous.integrable_of_hasCompactSupport
    (probeTimeWeight_compact ht.1)).mul_const B
  have hb (r : ℝ) : ‖probeTimeWeight t r • heatOp r (ψ (s+t-r))‖ ≤ probeTimeWeight t r * B := by
    by_cases hz : probeTimeWeight t r = 0
    · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
    have hr := probeTimeWeight_support ht.1 (subset_closure hz)
    have hrt : r ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_lt_of_le (by linarith [ht.1]) hr.1,
      by linarith [ht.2, hr.2]⟩
    have hwin : s+t-r ∈ Icc s (s+1) := by constructor <;> linarith [ht.1, ht.2, hr.1, hr.2]
    have hh := Potential.norm_heatOp_le_of_holderBesovENorm_le (η : ℝ) hrt
      (norm_nonneg _) (probePotentialWindow_bound η ψ s hwin)
    have hpow : r ^ ((η : ℝ)/2) ≤ (t/2) ^ ((η : ℝ)/2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) hr.1 (by linarith [η.property])
    have hp : (t/2) ^ ((η : ℝ)/2) = c * t ^ ((η : ℝ)/2) := by
      dsimp only [c]
      calc (t/2) ^ ((η : ℝ)/2) = (t * (1/2 : ℝ)) ^ ((η : ℝ)/2) := by congr 1; ring
        _ = t ^ ((η : ℝ)/2) * (1/2 : ℝ) ^ ((η : ℝ)/2) :=
          Real.mul_rpow ht.1.le (by norm_num)
        _ = _ := mul_comm _ _
    rw [hp] at hpow
    rw [norm_smul, Real.norm_of_nonneg (probeTimeWeight_nonneg ht.1 r)]
    exact mul_le_mul_of_nonneg_left
      (hh.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))) (probeTimeWeight_nonneg ht.1 r)
  calc ‖probePsiAverage ψ s t‖ ≤ ∫ r, ‖probeTimeWeight t r • heatOp r (ψ (s+t-r))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r, probeTimeWeight t r * B := integral_mono hi.norm hw hb
    _ = B := by rw [integral_mul_const, probeTimeWeight_integral ht.1, one_mul]

end GlobalPhi43.Attachment

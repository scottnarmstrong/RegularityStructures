module

public import GlobalPhi43.Attachment.SliceWindowBounds
public import GlobalPhi43.Attachment.DuhamelPowerBound

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE Set
open RegularityStructures.Inhomogeneity

/-- The actual second term of the source averaged Duhamel identity. -/
def sliceDuhamelRemainder {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ) (s t : ℝ) : C(Torus3,ℝ) :=
  ∫ τ, probeTimeWeight t τ • duhamel (sliceDuhamelForcing (N := N) hf hg hψ (s+t-τ)) τ

theorem sliceDuhamelRemainder_integrable {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ) (s : ℝ)
    {t : ℝ} (ht : 0<t) :
    Integrable (fun τ => probeTimeWeight t τ •
      duhamel (sliceDuhamelForcing (N := N) hf hg hψ (s+t-τ)) τ) := by
  let W := sliceDifferencePath (N := N) hf hg hψ
  have hW : Continuous W := continuous_forcePath _
  have hG : Integrable (fun τ => probeTimeWeight t τ • W (s+t)) :=
    ((probeTimeWeight_smooth t).continuous.smul continuous_const).integrable_of_hasCompactSupport
      (probeTimeWeight_compact ht).smul_right
  have hF : Integrable (fun τ => probeTimeWeight t τ • heatOp τ (W (s+t-τ))) :=
    ((probeTimeWeight_smooth t).continuous.smul
      (continuous_heatOp.comp (continuous_id.prodMk
      (hW.comp (continuous_const.sub continuous_id))))).integrable_of_hasCompactSupport
        (probeTimeWeight_compact ht).smul_right
  apply (hG.sub hF).congr
  filter_upwards [] with τ
  simp only [Pi.sub_apply]
  by_cases hz : probeTimeWeight t τ = 0
  · simp only [hz,zero_smul,sub_zero]
  have hs := probeTimeWeight_support ht (subset_closure hz)
  have hd := sliceDifference_duhamel (N := N) hf hg hψ (s+t-τ) τ (by linarith [hs.1])
  rw [sub_add_cancel] at hd
  change probeTimeWeight t τ • W (s+t) - _ = _
  rw [show W (s+t) = _ from hd,smul_add]
  abel

/-- The sharp integrated power bound for the remainder of the given potential.
The defect norms are finite by the derivative estimates. -/
theorem sliceDuhamelRemainder_bound {N : ℕ} (κ : Kappa)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ)
    (C : RenormalisationConstants)
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    (η : NegExponent) (hη : -2 < (η:ℝ)) (s : ℝ) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    ‖sliceDuhamelRemainder (N := N) hf hg hψ s t‖ ≤
      t^((η:ℝ)/2+1)/((η:ℝ)/2+1)*
        ‖probePotentialWindow η (slicePotentialPath hf hg hψ) s‖ + t*sliceDefectSize N f C s := by
  obtain ⟨c,_hc,hcB⟩ := slice_defect_size_bound N κ
  have hfin := (hcB f C Z hf hg hZ s).1
  let Y := ‖probePotentialWindow η (slicePotentialPath hf hg hψ) s‖
  let E := sliceDefectSize N f C s
  let B := t^((η:ℝ)/2+1)/((η:ℝ)/2+1)*Y+t*E
  have hβ : 0 < (η:ℝ)/2+1 := by linarith
  have hi := sliceDuhamelRemainder_integrable (N := N) hf hg hψ s ht.1
  have hw : Integrable (fun τ => probeTimeWeight t τ * B) :=
    ((probeTimeWeight_smooth t).continuous.integrable_of_hasCompactSupport
      (probeTimeWeight_compact ht.1)).mul_const B
  have hb (τ : ℝ) : ‖probeTimeWeight t τ •
      duhamel (sliceDuhamelForcing (N := N) hf hg hψ (s+t-τ)) τ‖ ≤ probeTimeWeight t τ * B := by
    by_cases hz : probeTimeWeight t τ = 0
    · simp only [hz,zero_smul,norm_zero,zero_mul,le_refl]
    have hs := probeTimeWeight_support ht.1 (subset_closure hz)
    have hτ : τ ∈ Ioc (0:ℝ) 1 := ⟨by linarith [ht.1,hs.1],by linarith [ht.2,hs.2]⟩
    have hτt : τ ≤ t := by linarith [hs.2,ht.1]
    have hp (σ : ℝ) (hσ : σ ∈ Ioc (0:ℝ) τ) :
        holderBesovENorm η (ψ (s+t-σ)) ≤ ENNReal.ofReal Y :=
      probePotentialWindow_bound η (slicePotentialPath hf hg hψ) s
        ⟨by linarith [hσ.2],by linarith [ht.2,hσ.1]⟩
    have he (σ : ℝ) (hσ : σ ∈ Ioc (0:ℝ) τ) :
        ‖sliceDuhamelForcing (N := N) hf hg hψ (s+t-τ) (τ-σ)-ψ (s+t-σ)‖ ≤ E := by
      have hh := slice_forcing_defect_bound (N := N) hf hg hψ C s (s+t-τ) (τ-σ)
        (show s+t-τ+(τ-σ) ∈ Icc s (s+1) from
          ⟨by linarith [hσ.2],by linarith [ht.2,hσ.1]⟩) hfin
      have htime : s+t-τ+(τ-σ) = s+t-σ := by ring
      simpa only [htime] using hh
    have hd := duhamel_holder_forcing_bound η hη _ (continuous_forcePath _)
      (fun σ => ψ (s+t-σ)) hτ Y E (norm_nonneg _) hp he
    have hpow := Real.rpow_le_rpow hτ.1.le hτt hβ.le
    have hB : ‖duhamel (sliceDuhamelForcing (N := N) hf hg hψ (s+t-τ)) τ‖ ≤ B :=
      hd.trans (add_le_add
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow hβ.le) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hτt ENNReal.toReal_nonneg))
    rw [norm_smul,Real.norm_of_nonneg (probeTimeWeight_nonneg ht.1 τ)]
    exact mul_le_mul_of_nonneg_left hB (probeTimeWeight_nonneg ht.1 τ)
  calc
    _ ≤ ∫ τ, ‖probeTimeWeight t τ •
        duhamel (sliceDuhamelForcing (N := N) hf hg hψ (s+t-τ)) τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ, probeTimeWeight t τ * B := integral_mono hi.norm hw hb
    _ = B := by rw [integral_mul_const,probeTimeWeight_integral ht.1,one_mul]

end GlobalPhi43.Attachment

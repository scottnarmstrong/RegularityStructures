module

public import GlobalPhi43.Attachment.SliceRemainderBound
public import GlobalPhi43.Attachment.SliceDuhamelAverage
public import GlobalPhi43.Attachment.SmoothNoiseSlices

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE Set

/-- The initial J average whose Gaussian pairing is used in the slice bound. -/
def sliceInitialJAverage (N : ℕ) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (s t : ℝ) : C(Torus3,ℝ) :=
  ∫ τ, probeTimeWeight t τ • heatOp τ (smoothNoiseJ N ⟨f,hf⟩ (s+t-τ))

theorem sliceInitialJAverage_integrable (N : ℕ) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) {t : ℝ} (ht : 0<t) :
    Integrable (fun τ => probeTimeWeight t τ • heatOp τ (smoothNoiseJ N ⟨f,hf⟩ (s+t-τ))) :=
  ((probeTimeWeight_smooth t).continuous.smul
    (continuous_heatOp.comp (continuous_id.prodMk
      ((smoothNoiseJ_continuous N ⟨f,hf⟩).comp
        (continuous_const.sub continuous_id))))).integrable_of_hasCompactSupport
          (probeTimeWeight_compact ht).smul_right

theorem sliceDifferencePath_eq_sub {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ) (r : ℝ) :
    sliceDifferencePath (N := N) hf hg hψ r = smoothNoiseJ N ⟨f,hf⟩ r - ψ r := by
  ext x
  have h := sliceDifferencePath_apply (N := N) hf hg hψ r (torusRep x)
  simpa only [torusProj_torusRep,ContinuousMap.sub_apply,smoothNoiseJ,ContinuousMap.coe_mk] using h

/-- The actual initial term splits with its original sign, before taking norms. -/
theorem slice_initial_average_split {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ) (s : ℝ)
    {t : ℝ} (ht : 0<t) :
    (∫ τ, probeTimeWeight t τ • heatOp τ
      (sliceDifferencePath (N := N) hf hg hψ (s+t-τ))) =
    sliceInitialJAverage N hf s t - probePsiAverage (slicePotentialPath hf hg hψ) s t := by
  simp_rw [sliceDifferencePath_eq_sub hf hg hψ,heatOp_sub,smul_sub]
  exact integral_sub (sliceInitialJAverage_integrable N hf s ht)
    (probePsiAverage_integrable (slicePotentialPath hf hg hψ) s ht)

/-- Exact Step 3 for the constructed positive mass-one source time weight. -/
theorem slice_averaged_duhamel_split {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ) (s : ℝ)
    {t : ℝ} (ht : 0<t) :
    sliceDifferencePath (N := N) hf hg hψ (s+t) =
      sliceInitialJAverage N hf s t - probePsiAverage (slicePotentialPath hf hg hψ) s t +
        sliceDuhamelRemainder (N := N) hf hg hψ s t := by
  have hpos (τ : ℝ) (hne : probeTimeWeight t τ ≠ 0) : 0≤τ := by
    have hh := probeTimeWeight_support ht (subset_closure hne)
    linarith [hh.1]
  have h := sliceDifference_averaged_duhamel (N := N) hf hg hψ (s+t)
    (probeTimeWeight t) (probeTimeWeight_smooth t).continuous
    (probeTimeWeight_compact ht) hpos (probeTimeWeight_integral ht)
  rw [slice_initial_average_split hf hg hψ s ht] at h
  exact h

end GlobalPhi43.Attachment

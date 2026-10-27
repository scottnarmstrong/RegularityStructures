module

public import GlobalPhi43.Attachment.SliceInitialSplit
public import GlobalPhi43.Flow.WindowMajorantEnvelope

public section
namespace GlobalPhi43.Attachment
open Set RegularityStructures RegularityStructures.Phi43

/-- The continuous-window norm is exactly the actual extended source supremum. -/
theorem probePotentialWindow_ofReal_norm (η : NegExponent)
    (ψ : C(ℝ,C(Torus3,ℝ))) (s : ℝ) :
    ENNReal.ofReal ‖probePotentialWindow η ψ s‖ = Flow.unitPotentialSize η s ψ := by
  have hu : Flow.unitPotentialSize η s ψ ≤ ENNReal.ofReal ‖probePotentialWindow η ψ s‖ := by
    apply iSup₂_le
    intro r hr
    exact probePotentialWindow_bound η ψ s hr
  have hfin : Flow.unitPotentialSize η s ψ ≠ ⊤ :=
    ne_of_lt (hu.trans_lt ENNReal.ofReal_lt_top)
  apply le_antisymm ?_ hu
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  apply (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).mpr
  intro r
  rw [show ‖probePotentialWindow η ψ s r‖ = (holderBesovENorm η (ψ r)).toReal from
    norm_toHolderBesov η (ψ r)]
  exact ENNReal.toReal_mono hfin (le_iSup₂_of_le r.val r.property le_rfl)

/-- Negative-norm embedding of the actual J-minus-psi difference. -/
theorem slice_holderBesov_le_difference {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3,ℝ)} (hψ : IsMassivePotential f ψ)
    (η : NegExponent) (s : ℝ) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    holderBesovENorm η (smoothNoiseJ N ⟨f,hf⟩ (s+t)) ≤
      ENNReal.ofReal (‖sliceDifferencePath (N := N) hf hg hψ (s+t)‖ +
        ‖probePotentialWindow η (slicePotentialPath hf hg hψ) s‖) := by
  have he : smoothNoiseJ N ⟨f,hf⟩ (s+t) =
      sliceDifferencePath (N := N) hf hg hψ (s+t) + ψ (s+t) := by
    rw [sliceDifferencePath_eq_sub hf hg hψ]
    abel
  have hb := (holderBesovENorm_add_le (η:ℝ)
    (sliceDifferencePath (N := N) hf hg hψ (s+t)) (ψ (s+t))).trans
    (add_le_add (holderBesovENorm_le η.2.le _)
      (probePotentialWindow_bound η (slicePotentialPath hf hg hψ) s
        ⟨by linarith [ht.1],by linarith [ht.2]⟩))
  rw [← he] at hb
  simpa only [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),ofReal_norm] using hb

end GlobalPhi43.Attachment

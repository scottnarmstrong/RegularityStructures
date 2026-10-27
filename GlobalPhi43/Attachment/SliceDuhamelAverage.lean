module

public import GlobalPhi43.Attachment.SliceDuhamel

/-! Exact source averaging of the actual arbitrary-start Duhamel identity. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE
open RegularityStructures.Inhomogeneity Set

/-- The two-term averaged Duhamel identity for a continuous compactly supported
nonnegative-time profile of integral one. Forcing integrability follows from
the evolution equation and smoothness. -/
theorem sliceDifference_averaged_duhamel {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ)
    (b : ℝ) (χ : ℝ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχpos : ∀ τ, χ τ ≠ 0 → 0 ≤ τ) (hχmass : ∫ τ, χ τ = 1) :
    sliceDifferencePath (N := N) hf hg hψ b =
      (∫ τ, χ τ • heatOp τ (sliceDifferencePath (N := N) hf hg hψ (b-τ))) +
      ∫ τ, χ τ • duhamel (sliceDuhamelForcing (N := N) hf hg hψ (b-τ)) τ := by
  let W := sliceDifferencePath (N := N) hf hg hψ
  let F (τ : ℝ) := χ τ • heatOp τ (W (b-τ))
  let H (τ : ℝ) := χ τ • duhamel (sliceDuhamelForcing (N := N) hf hg hψ (b-τ)) τ
  let G (τ : ℝ) := χ τ • W b
  have hpoint (τ : ℝ) : G τ = F τ + H τ := by
    by_cases hz : χ τ = 0
    · simp only [G, F, H, hz, zero_smul, add_zero]
    · have h := sliceDifference_duhamel (N := N) hf hg hψ (b-τ) τ (hχpos τ hz)
      rw [sub_add_cancel] at h
      simpa only [G, F, H, W, smul_add] using congrArg (fun v => χ τ • v) h
  have hW : Continuous W := continuous_forcePath _
  have hF : Integrable F :=
    (hχ.smul (continuous_heatOp.comp (continuous_id.prodMk
      (hW.comp (continuous_const.sub continuous_id))))).integrable_of_hasCompactSupport
        hχc.smul_right
  have hG : Integrable G :=
    (hχ.smul continuous_const).integrable_of_hasCompactSupport hχc.smul_right
  have heH : H = G-F := by
    funext τ
    change H τ = G τ - F τ
    rw [hpoint]
    abel
  have hH : Integrable H := by
    rw [heH]
    exact hG.sub hF
  have hmass : (∫ τ, G τ) = W b := by
    dsimp only [G]
    rw [integral_smul_const, hχmass, one_smul]
  calc W b = ∫ τ, G τ := hmass.symm
       _ = (∫ τ, F τ) + ∫ τ, H τ := by
         rw [← integral_add hF hH]
         exact integral_congr_ae (ae_of_all _ hpoint)

end GlobalPhi43.Attachment

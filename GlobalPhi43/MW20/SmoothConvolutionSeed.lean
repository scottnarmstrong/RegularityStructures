module

public import GlobalPhi43.MW20.SmoothConvolutionJets

/-!
# Smoothness of the constructed infinite average of a compact smooth seed
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A compact smooth seed bundled in the uniform norm, with its actual values. -/
@[expose] noncomputable def compactSmoothSeed (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : E →ᵇ F :=
  (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuousBounded
    (𝕜 := ℝ) E (compactSmoothJet f hf hs 0)

@[simp] theorem compactSmoothSeed_apply (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (x : E) : compactSmoothSeed f hf hs x = f x := by
  simp only [compactSmoothSeed, ContinuousLinearMap.compLeftContinuousBounded_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    compactSmoothJet, BoundedContinuousFunction.coe_ofNormedAddCommGroup, continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]

/-- The compact smooth seed has a global Lipschitz constant. -/
theorem compactSmoothSeed_lipschitz (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : ∃ K : ℝ≥0, LipschitzWith K (compactSmoothSeed f hf hs) := by
  obtain ⟨K, hK⟩ := compactSmoothJet_lipschitz f hf hs 0
  refine ⟨K, ?_⟩
  simpa only [compactSmoothSeed, ContinuousLinearMap.compLeftContinuousBounded_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    Function.comp_def, one_mul] using!
    (continuousMultilinearCurryFin0 ℝ E F).isometry.lipschitzWith.comp hK

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace F]

/-- The infinite probability average of a compact smooth seed is smooth.
Convergence of every derivative is constructed from the same shrinking measures. -/
theorem convolutionLimit_compactSmooth_contDiff (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) :
    ContDiff ℝ ∞ (convolutionLimit μ (compactSmoothSeed f hf hs)) := by
  let L := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨K, hK⟩ := compactSmoothJet_lipschitz f hf hs 0
  have heq := convolutionLimit_postcompose (E := E) (F := E [×0]→L[ℝ] F) (G := F)
    μ L (compactSmoothJet f hf hs 0) hK hA hq0 hq1 hsupp
  change ContDiff ℝ ∞ (convolutionLimit μ (L.compLeftContinuousBounded (𝕜 := ℝ) E
    (compactSmoothJet f hf hs 0)))
  rw [heq]
  have hlinear : IsBoundedLinearMap ℝ (fun y : E [×0]→L[ℝ] F =>
      (continuousMultilinearCurryFin0 ℝ E F) y) := by
    refine ⟨⟨?_, ?_⟩, 1, by norm_num, ?_⟩
    · intro a b; exact map_add _ a b
    · intro c a; exact map_smul _ c a
    · intro a; simp only [LinearIsometryEquiv.norm_map, one_mul]; exact le_rfl
  have hcurry : ContDiff ℝ ∞ (fun y : E [×0]→L[ℝ] F => (continuousMultilinearCurryFin0 ℝ E F) y) :=
    IsBoundedLinearMap.contDiff (𝕜 := ℝ) (E := E [×0]→L[ℝ] F) (F := F) hlinear
  exact hcurry.comp (smoothConvolutionJet_contDiff μ f hf hs hA hq0 hq1 hsupp 0)

end GlobalPhi43.MW20

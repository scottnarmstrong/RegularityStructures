module

public import GlobalPhi43.MW20.CompactSmoothJets
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import GlobalPhi43.MW20.ConvolutionLimitDerivative
public import GlobalPhi43.MW20.ConvolutionPostcompose

/-!
# Constructed smooth limits of the derivative fields of a compact seed
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The actual limit of the n-th derivative seed averaged by the shrinking measures. -/
@[expose] noncomputable def smoothConvolutionJet (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) : E →ᵇ (E [×n]→L[ℝ] F) :=
  convolutionLimit μ (compactSmoothJet f hf hs n)

/-- Successive limit jets retain the actual derivative relation. -/
theorem smoothConvolutionJet_hasFDerivAt (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) (n : ℕ) (x : E) :
    HasFDerivAt (smoothConvolutionJet μ f hf hs n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F)
        (smoothConvolutionJet μ f hf hs (n + 1) x)) x := by
  let L :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨K, hK⟩ := compactSmoothJet_lipschitz f hf hs n
  obtain ⟨K', hK'⟩ := compactSmoothJet_lipschitz f hf hs (n + 1)
  have hder : ∀ y : E, HasFDerivAt (𝕜 := ℝ) (compactSmoothJet f hf hs n)
      (L.compLeftContinuousBounded (𝕜 := ℝ) E (compactSmoothJet f hf hs (n + 1)) y) y := by
    intro y
    simpa only [ContinuousLinearMap.compLeftContinuousBounded_apply, L] using!
      compactSmoothJet_hasFDerivAt f hf hs n y
  have hLK : LipschitzWith K' (fun y : E => L (compactSmoothJet f hf hs (n + 1) y)) := by
    simpa only [ContinuousLinearMap.compLeftContinuousBounded_apply, Function.comp_def, one_mul, L]
      using! (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).isometry.lipschitzWith.comp hK'
  have hd := hasFDerivAt_convolutionLimit μ _ _ hder hK hLK
    hA hq0 hq1 hsupp x
  have heq := convolutionLimit_postcompose (E := E)
    (F := E [×n + 1]→L[ℝ] F) (G := E →L[ℝ] (E [×n]→L[ℝ] F))
    μ L (compactSmoothJet f hf hs (n + 1)) hK' hA hq0 hq1 hsupp
  rw [heq] at hd
  exact hd

/-- Every constructed jet is smooth. Finite regularity is proved simultaneously
at every jet order, using the derivative relation and the next continuous jet. -/
theorem smoothConvolutionJet_contDiff (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) (n : ℕ) :
    ContDiff ℝ ∞ (smoothConvolutionJet μ f hf hs n) := by
  have hd := smoothConvolutionJet_hasFDerivAt μ f hf hs hA hq0 hq1 hsupp
  have hfinite : ∀ k : ℕ, ∀ j : ℕ, ContDiff ℝ k (smoothConvolutionJet μ f hf hs j) := by
    intro k
    induction k with
    | zero => intro j; exact contDiff_zero.mpr (smoothConvolutionJet μ f hf hs j).continuous
    | succ k ih =>
      intro j
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by simp]
      apply contDiff_succ_iff_fderiv.mpr
      refine ⟨fun x => (hd j x).differentiableAt, by simp, ?_⟩
      have heq : fderiv ℝ (smoothConvolutionJet μ f hf hs j) = fun x =>
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F)
            (smoothConvolutionJet μ f hf hs (j + 1) x) := funext fun x => (hd j x).fderiv
      rw [heq]
      have hlinear : IsBoundedLinearMap ℝ
          (fun y : E [×j + 1]→L[ℝ] F =>
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F) y) := by
        refine ⟨⟨?_, ?_⟩, 1, by norm_num, ?_⟩
        · intro a b; exact map_add _ a b
        · intro c a; exact map_smul _ c a
        · intro a; simp only [LinearIsometryEquiv.norm_map, one_mul]; exact le_rfl
      have hcurry : ContDiff ℝ k
          (fun y : E [×j + 1]→L[ℝ] F =>
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F) y) :=
        IsBoundedLinearMap.contDiff (𝕜 := ℝ) (E := E [×j + 1]→L[ℝ] F)
          (F := E →L[ℝ] (E [×j]→L[ℝ] F)) (n := (k : WithTop ℕ∞)) hlinear
      exact hcurry.comp (ih (j + 1))
  exact contDiff_infty.mpr (fun k => hfinite k n)

end GlobalPhi43.MW20

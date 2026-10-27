module

public import GlobalPhi43.Attachment.SmoothNoiseFields
public import GlobalPhi43.Attachment.GermSeminormMeasurable
public import GlobalPhi43.Attachment.HolderSeminormMeasurable
public import GlobalPhi43.Attachment.TreeFunctional

/-! Actual ordinary and positive attachment seminorms as full smooth-noise observables. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set
open scoped ContDiff

/-- Continuity of the lifted primitive, with its domain fixed explicitly. -/
theorem smoothNoisePrimitive_continuous (N : ℕ) (C : RenormalisationConstants) (i : Fin 3)
    (f : SmoothNoise) : Continuous (fun y : ParabolicSpace => defectPrimitive N f.1 C i (spaceTimeProj y)) := by
  have h : ContDiff ℝ ∞ (fun y : ParabolicSpace => defectPrimitive N f.1 C i (spaceTimeProj y)) :=
    defectPrimitive_smooth (N := N) f.2 C i
  exact h.continuous

/-- Continuity of the lifted input, with its domain fixed explicitly. -/
theorem smoothNoiseInput_continuous (N : ℕ) (C : RenormalisationConstants) (i : Fin 3)
    (f : SmoothNoise) : Continuous (defectInput N f.1 C i) := by
  have h : ContDiff ℝ ∞ (defectInput N f.1 C i) := defectInput_smooth (N := N) f.2 C i
  exact h.continuous

/-- Negative tests of the actual primitive fields. -/
theorem smoothNoisePrimitive_test_measurable (N : ℕ) (C : RenormalisationConstants)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (S : Set ParabolicSpace) (α : ℝ) (i : Fin 3) :
    Measurable (fun f : SmoothNoise => negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S α
      (fun y => defectPrimitive N f.1 C i (spaceTimeProj y))) := by
  exact localTestSeminorm_measurable Φ hΦ S (Ioc 0 1) (fun _ h => h) α
    (fun (f : SmoothNoise) p => defectPrimitive N f.1 C i (spaceTimeProj p.2))
    (fun f => (smoothNoisePrimitive_continuous N C i f).comp continuous_snd)
    (fun p => smoothNoisePrimitive_measurable N C i (spaceTimeProj p.2))

/-- Negative tests of noise,V,W on the full smooth-noise space. -/
theorem smoothNoiseInput_test_measurable (N : ℕ) (C : RenormalisationConstants)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (S : Set ParabolicSpace) (α : ℝ) (i : Fin 3) :
    Measurable (fun f : SmoothNoise => negativeTreeSeminorm (mw20TestingKernel Φ hΦ) S α
      (defectInput N f.1 C i)) := by
  exact localTestSeminorm_measurable Φ hΦ S (Ioc 0 1) (fun _ h => h) α
    (fun (f : SmoothNoise) p => defectInput N f.1 C i p.2)
    (fun f => (smoothNoiseInput_continuous N C i f).comp continuous_snd)
    (fun p => smoothNoiseInput_measurable N C i p.2)

/-- The actual Y/Z Holder norms, retaining every pair of distinct points in S. -/
theorem smoothNoisePrimitive_holder_measurable (N : ℕ) (C : RenormalisationConstants)
    (S : Set ParabolicSpace) (α : ℝ) (i : Fin 3) :
    Measurable (fun f : SmoothNoise => scalarHolderSeminorm
      (fun y => defectPrimitive N f.1 C i (spaceTimeProj y)) S α) := by
  exact scalarHolderSeminorm_measurable S α
    (fun (f : SmoothNoise) y => defectPrimitive N f.1 C i (spaceTimeProj y))
    (fun f => smoothNoisePrimitive_continuous N C i f)
    (fun y => smoothNoisePrimitive_measurable N C i (spaceTimeProj y))

end GlobalPhi43.Attachment

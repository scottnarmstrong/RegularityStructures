module

public import GlobalPhi43.Attachment.OrdinaryFunctionalMeasurable
public import GlobalPhi43.Attachment.CoordinateSeminormMeasurable

/-! The actual vector and recentered attachment fields, without a good-event restriction. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- The vector XV norm at every smooth forcing. -/
theorem attachment_XV_measurable (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) :
    Measurable (fun f : SmoothNoise => attachmentTreeSeminorm N κ Φ hΦ f.1 C S .XV) := by
  exact recenteredXVSeminorm_measurable Φ hΦ S κ.1
    (fun (f : SmoothNoise) => defectInput N f.1 C 1)
    (fun f => smoothNoiseInput_continuous N C 1 f) (smoothNoiseInput_measurable N C 1)

/-- Actual signed A tests. -/
theorem attachment_A_measurable (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) :
    Measurable (fun f : SmoothNoise => attachmentTreeSeminorm N κ Φ hΦ f.1 C S .A) := by
  let Y (f : SmoothNoise) (y : ParabolicSpace) := defectPrimitive N f.1 C 1 (spaceTimeProj y)
  let V (f : SmoothNoise) := defectInput N f.1 C 1
  have hY (f : SmoothNoise) : Continuous (Y f) := (smoothNoisePrimitive_continuous N C 1 f)
  have hV (f : SmoothNoise) : Continuous (V f) := (smoothNoiseInput_continuous N C 1 f)
  refine localTestSeminorm_measurable Φ hΦ S (Ioo 0 1) (fun _ h => ⟨h.1, h.2.le⟩) (-4*κ.1)
    (fun f p => (Y f p.2 - Y f p.1) * V f p.2 - C₂ C) ?_ ?_
  · intro f
    exact (((hY f |>.comp continuous_snd).sub (hY f |>.comp continuous_fst)).mul
      (hV f |>.comp continuous_snd)).sub continuous_const
  · intro p
    exact (((smoothNoisePrimitive_measurable N C 1 (spaceTimeProj p.2)).sub
      (smoothNoisePrimitive_measurable N C 1 (spaceTimeProj p.1))).mul
      (smoothNoiseInput_measurable N C 1 p.2)).sub measurable_const

/-- Actual B tests. -/
theorem attachment_B_measurable (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) :
    Measurable (fun f : SmoothNoise => attachmentTreeSeminorm N κ Φ hΦ f.1 C S .B) := by
  let Zt (f : SmoothNoise) (y : ParabolicSpace) := defectPrimitive N f.1 C 2 (spaceTimeProj y)
  let J (f : SmoothNoise) (y : ParabolicSpace) := defectPrimitive N f.1 C 0 (spaceTimeProj y)
  have hZ (f : SmoothNoise) : Continuous (Zt f) := (smoothNoisePrimitive_continuous N C 2 f)
  have hJ (f : SmoothNoise) : Continuous (J f) := (smoothNoisePrimitive_continuous N C 0 f)
  refine localTestSeminorm_measurable Φ hΦ S (Ioo 0 1) (fun _ h => ⟨h.1, h.2.le⟩) (-4*κ.1)
    (fun f p => (Zt f p.2 - Zt f p.1) * J f p.2) ?_ ?_
  · intro f
    exact ((hZ f |>.comp continuous_snd).sub (hZ f |>.comp continuous_fst)).mul
      (hJ f |>.comp continuous_snd)
  · intro p
    exact ((smoothNoisePrimitive_measurable N C 2 (spaceTimeProj p.2)).sub
      (smoothNoisePrimitive_measurable N C 2 (spaceTimeProj p.1))).mul
      (smoothNoisePrimitive_measurable N C 0 (spaceTimeProj p.2))

/-- Actual D tests with precisely the signed counterterm 3 C2 J. -/
theorem attachment_D_measurable (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) :
    Measurable (fun f : SmoothNoise => attachmentTreeSeminorm N κ Φ hΦ f.1 C S .D) := by
  let Zt (f : SmoothNoise) (y : ParabolicSpace) := defectPrimitive N f.1 C 2 (spaceTimeProj y)
  let J (f : SmoothNoise) (y : ParabolicSpace) := defectPrimitive N f.1 C 0 (spaceTimeProj y)
  let V (f : SmoothNoise) := defectInput N f.1 C 1
  have hZ (f : SmoothNoise) : Continuous (Zt f) := (smoothNoisePrimitive_continuous N C 2 f)
  have hJ (f : SmoothNoise) : Continuous (J f) := (smoothNoisePrimitive_continuous N C 0 f)
  have hV (f : SmoothNoise) : Continuous (V f) := (smoothNoiseInput_continuous N C 1 f)
  refine localTestSeminorm_measurable Φ hΦ S (Ioo 0 1) (fun _ h => ⟨h.1, h.2.le⟩) (-(1/2)-5*κ.1)
    (fun f p => (Zt f p.2 - Zt f p.1) * V f p.2 - 3*C₂ C*J f p.2) ?_ ?_
  · intro f
    exact (((hZ f |>.comp continuous_snd).sub (hZ f |>.comp continuous_fst)).mul
      (hV f |>.comp continuous_snd)).sub (continuous_const.mul (hJ f |>.comp continuous_snd))
  · intro p
    exact (((smoothNoisePrimitive_measurable N C 2 (spaceTimeProj p.2)).sub
      (smoothNoisePrimitive_measurable N C 2 (spaceTimeProj p.1))).mul
      (smoothNoiseInput_measurable N C 1 p.2)).sub
      (measurable_const.mul (smoothNoisePrimitive_measurable N C 0 (spaceTimeProj p.2)))

end GlobalPhi43.Attachment

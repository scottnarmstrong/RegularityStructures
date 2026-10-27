module

public import GlobalPhi43.Attachment.SmoothNoiseDefects
public import GlobalPhi43.Attachment.DefectPDE

/-! Fixed-point measurability of all actual attachment fields on full smooth-noise space. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE

/-- Measurability of noise,V,W at every lifted point. -/
theorem smoothNoiseInput_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) (x : ParabolicSpace) :
    Measurable (fun f : SmoothNoise => defectInput N f.1 C i x) :=
  (smoothNoise_defectInput_measurable N C i).comp (measurable_id.prodMk measurable_const)

/-- Smooth-noise input evaluations are the same functions, without any growth-event replacement. -/
theorem smoothNoiseInput_spaceTime_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) (z : SpaceTime) :
    Measurable (fun f : SmoothNoise => (![f.1, treeV N f.1 (C₁ C), treeW N f.1 (C₁ C)] i) z) := by
  have h := smoothNoiseInput_measurable N C i (z.1, torusRep z.2)
  simpa only [defectInput, spaceTimeProj, Prod.fst, Prod.snd, torusProj_torusRep] using h

/-- Joint measurable input fields before the compact-kernel convolution. -/
theorem smoothNoiseInput_spaceTime_uncurry_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) : Measurable (fun p : SmoothNoise × SpaceTime =>
      (![p.1.1, treeV N p.1.1 (C₁ C), treeW N p.1.1 (C₁ C)] i) p.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (z : SpaceTime) (f : SmoothNoise) =>
      (![f.1, treeV N f.1 (C₁ C), treeW N f.1 (C₁ C)] i) z)
    (fun f => IsSmoothOnSpaceTime.continuous (defectInput_smooth (N := N) f.2 C i))
    (fun z => smoothNoiseInput_spaceTime_measurable N C i z)
  exact h.comp (measurable_snd.prodMk measurable_fst)

/-- All actual primitives J,Y,Z are fixed measurable functions of the full smooth noise. -/
theorem smoothNoisePrimitive_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) (z : SpaceTime) :
    Measurable (fun f : SmoothNoise => defectPrimitive N f.1 C i z) := by
  have hi : Measurable (fun p : SmoothNoise × SpaceTime => hairerKernelTorus N (z - p.2) *
      (![p.1.1, treeV N p.1.1 (C₁ C), treeW N p.1.1 (C₁ C)] i) p.2) :=
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_snd)).mul (smoothNoiseInput_spaceTime_uncurry_measurable N C i)
  have he : (fun f : SmoothNoise => defectPrimitive N f.1 C i z) =
      (fun f : SmoothNoise => ∫ w, hairerKernelTorus N (z - w) *
        (![f.1, treeV N f.1 (C₁ C), treeW N f.1 (C₁ C)] i) w) := by
    funext f
    exact defectPrimitive_eq_torusIntegral N f.1 C i z
  rw [he]
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

end GlobalPhi43.Attachment

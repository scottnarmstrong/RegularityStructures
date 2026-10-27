module

public import GlobalPhi43.Attachment.SmoothNoiseSlices
public import GlobalPhi43.Attachment.DefectNorms
public import GlobalPhi43.MW20.ScalarSupNorm

/-! Actual defect observables on every smooth forcing, without growth or model assumptions. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity
open scoped ContDiff

/-- Qualitative continuity of the three whole source inputs needs smoothness alone. -/
theorem defectInput_continuous (N : ℕ) (f : SmoothNoise) (C : RenormalisationConstants)
    (i : Fin 3) : Continuous (defectInput N f.1 C i) := by
  fin_cases i
  · exact f.2.continuous
  · exact (continuous_treeV f.2 _).comp continuous_spaceTimeProj
  · exact (continuous_treeW f.2 _).comp continuous_spaceTimeProj

/-- The actual defects are smooth for every smooth forcing, including outside all growth events. -/
theorem smoothNoise_defectField_smooth (N : ℕ) (f : SmoothNoise) (C : RenormalisationConstants)
    (i : Fin 3) : ContDiff ℝ ∞ (defectField N f.1 C i) :=
  (contDiff_potConv (defectInput_continuous N f C i) (contDiff_potQ N)
    (by simpa only [ddA] using hasCompactSupport_ddA_potQ N [])).neg

/-- Joint measurability of the actual source inputs on full smooth-noise evaluation space. -/
theorem smoothNoise_defectInput_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) : Measurable (fun p : SmoothNoise × ParabolicSpace => defectInput N p.1.1 C i p.2) := by
  have hn (z : ParabolicSpace) : Measurable (fun f : SmoothNoise => f.1 (spaceTimeProj z)) :=
    (measurable_pi_apply _).comp measurable_subtype_coe
  have hj (z : ParabolicSpace) : Measurable (fun f : SmoothNoise => treeJ N f.1 (spaceTimeProj z)) :=
    (ContinuousMap.measurable_eval _).comp (smoothNoiseJ_measurable N z.1)
  have hi (z : ParabolicSpace) : Measurable (fun f : SmoothNoise => defectInput N f.1 C i z) := by
    fin_cases i
    · exact hn z
    · exact ((hj z).pow_const 2).sub_const _
    · exact ((hj z).pow_const 3).sub ((hj z).const_mul (3 * C₁ C))
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (z : ParabolicSpace) (f : SmoothNoise) => defectInput N f.1 C i z)
    (fun f => defectInput_continuous N f C i) hi
  exact h.comp (measurable_snd.prodMk measurable_fst)

/-- Fixed-point measurability of the actual remainder convolution, everywhere. -/
theorem smoothNoise_defectField_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) (x : ParabolicSpace) :
    Measurable (fun f : SmoothNoise => defectField N f.1 C i x) := by
  have hi : Measurable (fun p : SmoothNoise × ParabolicSpace =>
      defectInput N p.1.1 C i p.2 * potQ N (x - p.2)) :=
    (smoothNoise_defectInput_measurable N C i).mul
      ((contDiff_potQ N).continuous.measurable.comp (measurable_const.sub measurable_snd))
  exact hi.stronglyMeasurable.integral_prod_right'.measurable.neg

/-- The exact sup-norm defect entries consumed by the source tree functional. -/
def smoothNoiseDefectSup (N : ℕ) (C : RenormalisationConstants) (i : Fin 3)
    (S : Set ParabolicSpace) (f : SmoothNoise) : ENNReal :=
  MW20.localScalarSup (defectField N f.1 C i) S

theorem smoothNoiseDefectSup_measurable (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) (S : Set ParabolicSpace) : Measurable (smoothNoiseDefectSup N C i S) := by
  have he : smoothNoiseDefectSup N C i S =
      (⨆ x : S, fun f : SmoothNoise => ENNReal.ofReal |defectField N f.1 C i x|) := by
    funext f
    simp only [smoothNoiseDefectSup, MW20.localScalarSup, iSup_subtype, iSup_apply]
  rw [he]
  apply measurable_iSup_of_lowerSemicontinuous
    (fun x : S => (continuous_abs.measurable.comp
      (smoothNoise_defectField_measurable N C i x)).ennreal_ofReal)
  intro f
  exact (ENNReal.continuous_ofReal.comp
    ((smoothNoise_defectField_smooth N f C i).continuous.abs.comp continuous_subtype_val)).lowerSemicontinuous

theorem smoothNoiseDefectSup_ne_top (N : ℕ) (C : RenormalisationConstants)
    (i : Fin 3) (S : Set ParabolicSpace) (hS : IsCompact S) (f : SmoothNoise) :
    smoothNoiseDefectSup N C i S f ≠ ⊤ :=
  MW20.localScalarSup_ne_top _ (smoothNoise_defectField_smooth N f C i).continuous S S
    (fun _ h => h) hS

end GlobalPhi43.Attachment

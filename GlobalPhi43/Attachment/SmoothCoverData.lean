module

public import GlobalPhi43.Attachment.CoverLocalData
public import GlobalPhi43.Attachment.SmoothNoiseSlices

/-! Cover local data for EVERY smooth forcing, including outcomes outside growth events. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- Compact-kernel smoothing gives smooth defects without growth or model assumptions. -/
theorem defectField_smooth_everywhere {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants) (i : Fin 3) :
    ContDiff ℝ ∞ (defectField N f C i) := by
  have hi : ContDiff ℝ ∞ (defectInput N f C i) := defectInput_smooth (N := N) hf C i
  exact (contDiff_potConv hi.continuous (contDiff_potQ N)
    (by simpa only [ddA] using hasCompactSupport_ddA_potQ N [])).neg

/-- The actual selected classical solution on the periodic lift, without a LiftData input. -/
@[expose] def unshiftedClassicalField (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) :
    ParabolicSpace → ℝ :=
  fun z => Flow.smoothSolution (3*C.1-9*C.2) f hf q hq z.1 (torusProj z.2)

/-- The actual u-minus-original-J path at start zero. -/
@[expose] def smoothClassicalRemainder (N : ℕ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) (t : ℝ) : C(Torus3, ℝ) :=
  Flow.smoothSolution (3*C.1-9*C.2) f hf q hq t - smoothNoiseJ N ⟨f,hf⟩ t

theorem smoothClassicalRemainder_continuousOn (N : ℕ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) :
    ContinuousOn (fun z : ParabolicSpace => smoothClassicalRemainder N f hf C q hq z.1
      (torusProj z.2)) {z | 0 < z.1} := by
  have hu := (Flow.smoothSolution_spec (3*C.1-9*C.2) f hf q hq).contDiffOn.continuousOn
  have huc : ContinuousOn (unshiftedClassicalField f hf C q hq) {z | 0 < z.1} := by
    apply hu.mono
    intro z hz
    exact ⟨hz, mem_univ _⟩
  exact huc.sub ((continuous_treeJ hf).comp continuous_spaceTimeProj).continuousOn

/-- All eight smoothness and four PDE requirements hold at every smooth forcing. -/
theorem smooth_cover_localData (N : ℕ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {x₀ : Fin 3 → ℝ}
    (hx₀ : x₀ ∈ coverGrid (coverScale t)) :
    let l := coverScale t
    let b := coverBase 0 t x₀
    IsMWLocalData
      (Local.parabolicPullback l (unshiftedClassicalField f hf C q hq) b l)
      (Local.parabolicPullback (l^3) (fun z => f (spaceTimeProj z)) b l)
      (Local.parabolicPullback l (fun z => defectPrimitive N f C 0 (spaceTimeProj z)) b l)
      (Local.parabolicPullback 1 (fun z => defectPrimitive N f C 1 (spaceTimeProj z)) b l)
      (Local.parabolicPullback l (fun z => defectPrimitive N f C 2 (spaceTimeProj z)) b l)
      (Local.parabolicPullback (l^3) (defectField N f C 0) b l)
      (Local.parabolicPullback (l^2) (defectField N f C 1) b l)
      (Local.parabolicPullback (l^3) (defectField N f C 2) b l)
      (l^2*C.1) (l^2*C.2) := by
  have hu := Flow.smoothSolution_spec (3*C.1-9*C.2) f hf q hq
  have hUs : ContDiffOn ℝ ∞ (unshiftedClassicalField f hf C q hq) {z | 0 < z.1} := by
    apply hu.contDiffOn.mono
    intro z hz
    exact ⟨hz, mem_univ _⟩
  have hp (i : Fin 3) := defectPrimitive_smooth (N := N) hf C i
  have he (i : Fin 3) := defectField_smooth_everywhere (N := N) hf C i
  apply Local.isMWLocalData_parabolicPullback _ _ _ _ _ _ _ _ _ _
    (coverBase 0 t x₀) (coverScale t) {z | 0 < z.1} {z | 0 < z.1} (Flow.coverRegion 0)
    (isOpen_lt continuous_const continuous_fst) hUs
  · rintro _ ⟨z, hz, rfl⟩
    exact coverMap_closed_positive ht.1 0 x₀ hz
  · rintro _ ⟨z, hz, rfl⟩
    have hh := coverMap_cylinder_time ht.1 0 x₀ hz
    change 0 < (coverMap 0 t x₀ z).1
    linarith [hh.1, ht.1]
  · rintro _ ⟨z, hz, rfl⟩
    exact coverMap_enlargement_subset ht 0 hx₀.2 hz
  · exact hf
  · exact hp 0
  · exact hp 1
  · exact hp 2
  · exact he 0
  · exact he 1
  · exact he 2
  · intro z hz
    exact classical_heatOperator hu z hz
  · intro z _
    refine ⟨heatOperator_defectPrimitive hf C 0 z, ?_, ?_⟩
    · simpa [defectPrimitive, defectInput, treeV, C₁] using heatOperator_defectPrimitive hf C 1 z
    · simpa [defectPrimitive, defectInput, treeW, C₁] using heatOperator_defectPrimitive hf C 2 z

end GlobalPhi43.Attachment

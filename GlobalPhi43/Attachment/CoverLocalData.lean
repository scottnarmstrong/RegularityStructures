module

public import GlobalPhi43.Attachment.PhysicalStartedField
public import GlobalPhi43.Attachment.DefectTreeHeat
public import GlobalPhi43.Attachment.CoverGrid
public import GlobalPhi43.Local.Scaling

/-! Scaled local data on the concrete cover cylinder.
No bounded-defect or slice estimate is assumed. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- The concrete translated centre, before applying the scaling library. -/
@[expose] def coverBase (s t : ℝ) (x₀ : Fin 3 → ℝ) : ParabolicSpace :=
  (s+t-coverScale t^2, x₀)

theorem coverMap_closed_positive {t : ℝ} (ht : 0 < t) (s : ℝ) (x₀ : Fin 3 → ℝ) :
    MapsTo (coverMap s t x₀) (closure mwCylinder) {z | s < z.1} := by
  have hc : closure mwCylinder ⊆ {z : ParabolicSpace | 0 ≤ z.1} :=
    closure_minimal (fun z hz => hz.1.1.le) (isClosed_le continuous_const continuous_fst)
  intro z hz
  have hp := mul_nonneg (sq_nonneg (coverScale t)) (hc hz)
  change s < s+t-coverScale t^2+coverScale t^2*z.1
  nlinarith [coverScale_sq ht.le]

/-- The actual chosen solution and J/Y/Z/defects form exactly the
normalized MW data, including scaled C1 AND C2 and amplitudes 3/2/3.
Only smooth-lift data, the real start, smooth datum and legal grid patch
are inputs; no bounded-defect or analytic norm estimate is assumed. -/
theorem cover_localData {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {x₀ : Fin 3 → ℝ}
    (hx₀ : x₀ ∈ coverGrid (coverScale t)) :
    let l := coverScale t
    let b := coverBase s t x₀
    IsMWLocalData
      (Local.parabolicPullback l (physicalStartedField a s q hq) b l)
      (Local.parabolicPullback (l^3) (fun z => a.forcing (spaceTimeProj z)) b l)
      (Local.parabolicPullback l (fun z => defectPrimitive N a.forcing a.constants 0 (spaceTimeProj z)) b l)
      (Local.parabolicPullback 1 (fun z => defectPrimitive N a.forcing a.constants 1 (spaceTimeProj z)) b l)
      (Local.parabolicPullback l (fun z => defectPrimitive N a.forcing a.constants 2 (spaceTimeProj z)) b l)
      (Local.parabolicPullback (l^3) (defectField N a.forcing a.constants 0) b l)
      (Local.parabolicPullback (l^2) (defectField N a.forcing a.constants 1) b l)
      (Local.parabolicPullback (l^3) (defectField N a.forcing a.constants 2) b l)
      (l^2*a.constants.1) (l^2*a.constants.2) := by
  let O : Set ParabolicSpace := {z | s < z.1}
  have hf := Flow.smooth_of_moderateLift a.moderate
  have hp (i : Fin 3) := defectPrimitive_smooth (N := N) hf a.constants i
  have he (i : Fin 3) := defectField_smooth hf a.moderate.1 a.moderate.2.1 i
  apply Local.isMWLocalData_parabolicPullback _ _ _ _ _ _ _ _ _ _
    (coverBase s t x₀) (coverScale t) O O (Flow.coverRegion s)
    (isOpen_lt continuous_const continuous_fst) (physicalStartedField_smooth a s q hq)
  · rintro _ ⟨z, hz, rfl⟩
    exact coverMap_closed_positive ht.1 s x₀ hz
  · rintro _ ⟨z, hz, rfl⟩
    have hh := coverMap_cylinder_time ht.1 s x₀ hz
    change s < (coverMap s t x₀ z).1
    linarith [hh.1, ht.1]
  · rintro _ ⟨z, hz, rfl⟩
    exact coverMap_enlargement_subset ht s hx₀.2 hz
  · exact hf
  · exact hp 0
  · exact hp 1
  · exact hp 2
  · exact he 0
  · exact he 1
  · exact he 2
  · intro z hz
    exact physicalStartedField_pde a s q hq z hz
  · intro z _
    refine ⟨?_, ?_, ?_⟩
    · exact heatOperator_defectPrimitive hf a.constants 0 z
    · simpa [defectPrimitive, defectInput, treeV, C₁] using heatOperator_defectPrimitive hf a.constants 1 z
    · simpa [defectPrimitive, defectInput, treeW, C₁] using heatOperator_defectPrimitive hf a.constants 2 z

end GlobalPhi43.Attachment

module

public import GlobalPhi43.Attachment.PhysicalStartedField
public import GlobalPhi43.Attachment.StartedRemainder

/-! Exact identification of physical cover patches with relative restart coordinates. -/

public noncomputable section

open RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Attachment

theorem coverMap_relative (s t : ℝ) (x₀ : Fin 3 → ℝ) (z : ParabolicSpace) :
    Local.parabolicMap (-s, 0) 1 (coverMap s t x₀ z) = coverMap 0 t x₀ z := by
  apply Prod.ext <;> simp [Local.parabolicMap, coverMap, parabolicDilate]
  ring

theorem physicalStartedField_cover {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    (t : ℝ) (x₀ : Fin 3 → ℝ) (z : ParabolicSpace) :
    physicalStartedField a s q hq (coverMap s t x₀ z) =
      startedClassicalField a s q hq (coverMap 0 t x₀ z) := by
  change 1 * startedClassicalField a s q hq
    (Local.parabolicMap (-s, 0) 1 (coverMap s t x₀ z)) = _
  rw [coverMap_relative, one_mul]

/-- The SAME original J at physical time becomes the J subtracted by startedRemainder. -/
theorem physicalRemainder_cover {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    (t : ℝ) (x₀ : Fin 3 → ℝ) (z : ParabolicSpace) :
    physicalStartedField a s q hq (coverMap s t x₀ z) -
      treeJ N a.forcing (spaceTimeProj (coverMap s t x₀ z)) =
      startedRemainder a s q hq (coverMap 0 t x₀ z).1 (torusProj (coverMap 0 t x₀ z).2) := by
  have ht : (coverMap s t x₀ z).1 = s+(coverMap 0 t x₀ z).1 := by
    change s+t-coverScale t^2+coverScale t^2*z.1 = s+(0+t-coverScale t^2+coverScale t^2*z.1)
    ring
  rw [physicalStartedField_cover]
  change _ - treeJ N a.forcing ((coverMap s t x₀ z).1, torusProj (coverMap s t x₀ z).2) = _
  rw [ht]
  rfl

end GlobalPhi43.Attachment

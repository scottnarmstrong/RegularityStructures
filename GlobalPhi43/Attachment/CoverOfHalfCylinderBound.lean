module

public import GlobalPhi43.Attachment.CoverDataFunctional
public import GlobalPhi43.Attachment.CoverRestartCoordinates
public import GlobalPhi43.Attachment.ConditionalEveryStart

/-! Cover bounds from the half-cylinder and time-slice estimates,
using the tree and defect scaling identities. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- The half-cylinder bound implies the cover bound with the same coefficient.
All local fields and the twelve-entry functional retain their given definitions. -/
theorem normalizedCoverRow_of_mw20HalfCylinderBound (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C : ℝ≥0)
    (hhalf : MW20HalfCylinderBound κ Φ hΦ C) : NormalizedCoverRow N κ Φ hΦ C := by
  unfold NormalizedCoverRow
  intro a s _ q hq t ht x₀ hx₀ z hz
  let l := coverScale t
  let b := coverBase s t x₀
  let J := fun w => treeJ N a.forcing (spaceTimeProj w)
  let Y := fun w => treeY N a.forcing (C₁ a.constants) (spaceTimeProj w)
  let Z := fun w => treeZ N a.forcing (C₁ a.constants) (spaceTimeProj w)
  let M := attachmentFunctional N κ Φ hΦ a.forcing a.constants (Flow.coverRegion s)
  have hl : 0 < l := coverScale_pos ht.1
  have hlocal := cover_localData a s q hq ht hx₀
  unfold MW20HalfCylinderBound at hhalf
  have hg := hhalf (parabolicPullback l (physicalStartedField a s q hq) b l)
    (parabolicPullback (l^3) (fun w => a.forcing (spaceTimeProj w)) b l)
    (parabolicPullback l J b l) (parabolicPullback 1 Y b l) (parabolicPullback l Z b l)
    (parabolicPullback (l^3) (defectField N a.forcing a.constants 0) b l)
    (parabolicPullback (l^2) (defectField N a.forcing a.constants 1) b l)
    (parabolicPullback (l^3) (defectField N a.forcing a.constants 2) b l)
    (l^2*C₁ a.constants) (l^2*C₂ a.constants)
    (by simpa [defectPrimitive, C₁, C₂, l, b, J, Y, Z] using hlocal) z hz
  rw [mwDataFunctional_scaled_eq] at hg
  change ENNReal.ofReal |l*physicalStartedField a s q hq (coverMap s t x₀ z) -
      l*treeJ N a.forcing (spaceTimeProj (coverMap s t x₀ z))| ≤ _ at hg
  rw [← mul_sub, abs_mul, abs_of_pos hl, physicalRemainder_cover] at hg
  have hbudget := cover_scaled_functional_le a Φ hΦ s ht hx₀
  have hb := hg.trans (mul_le_mul_right (max_le_max le_rfl hbudget) (C : ℝ≥0∞))
  have hM : M ≠ ⊤ := attachmentFunctional_ne_top N κ Φ hΦ
    (Flow.smooth_of_moderateLift a.moderate) a.constants _ (isCompact_coverRegion s)
  have hR : ENNReal.ofReal ((C : ℝ)*max 2 (l*M.toReal)) =
      (C : ℝ≥0∞)*max 2 (ENNReal.ofReal l*M) := by
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_max, ENNReal.ofReal_mul hl.le, ENNReal.ofReal_toReal hM]
    norm_num
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (C : ℝ)*max 2 (l*M.toReal))).mp
  rw [hR]
  exact hb

/-- The deterministic majorant bound before evaluating random fields. -/
theorem everyStartMajorant_of_halfCylinderBound_of_slice (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C H : ℝ≥0)
    (hhalf : MW20HalfCylinderBound κ Φ hΦ C) (hslice : ActualSliceRow N κ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ A : ℕ → Flow.LiftData N κ, Flow.EveryStartMajorant c A :=
  everyStartMajorant_of_normalized_cover_and_slice N κ Φ hΦ C H
    (normalizedCoverRow_of_mw20HalfCylinderBound N κ Φ hΦ C hhalf) hslice

end GlobalPhi43.Attachment

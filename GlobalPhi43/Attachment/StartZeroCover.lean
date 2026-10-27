module

public import GlobalPhi43.Attachment.SmoothCoverData
public import GlobalPhi43.Attachment.MW20Constant
public import GlobalPhi43.Attachment.CoverDataFunctional
public import GlobalPhi43.Attachment.MajorantRegions
public import GlobalPhi43.Attachment.CoverTorusNorm
public import GlobalPhi43.Attachment.TreeFunctionalFiniteness

/-! Start-zero cover for every smooth forcing and the SAME deterministic Cdef.
No model, growth event, dyadic restriction or supplied solution bound is needed. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- Cover estimate with the deterministic coefficient used in the
regularised solution bound. -/
theorem start_zero_cover_of_halfCylinderBound
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (Cdef : Kappa → ℝ≥0)
    (hhalf : ∀ κ, MW20HalfCylinderBound κ Φ hΦ (Cdef κ))
    (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (C : RenormalisationConstants) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ENNReal.ofReal (Real.sqrt t) * ‖smoothClassicalRemainder N f hf C q hq t‖ₑ ≤
      2*(Cdef κ : ℝ≥0∞)*max 2 (attachmentFunctional N κ Φ hΦ f C (Flow.coverRegion 0)) := by
  let l := coverScale t
  let M := attachmentFunctional N κ Φ hΦ f C (Flow.coverRegion 0)
  have hl : 0 < l := coverScale_pos ht.1
  have hM : M ≠ ⊤ := attachmentFunctional_ne_top N κ Φ hΦ hf C _ (isCompact_coverRegion 0)
  have hpoint (x₀ : Fin 3 → ℝ) (hx₀ : x₀ ∈ coverGrid (coverScale t))
      (z : ParabolicSpace) (hz : z ∈ mwInnerCylinder (1/2)) :
      coverScale t * |smoothClassicalRemainder N f hf C q hq (coverMap 0 t x₀ z).1
        (torusProj (coverMap 0 t x₀ z).2)| ≤ (Cdef κ : ℝ)*max 2 (l*M.toReal) := by
    let b := coverBase 0 t x₀
    let J := fun w => treeJ N f (spaceTimeProj w)
    let Y := fun w => treeY N f (C₁ C) (spaceTimeProj w)
    let Z := fun w => treeZ N f (C₁ C) (spaceTimeProj w)
    have hlocal := smooth_cover_localData N f hf C q hq ht hx₀
    have hg := hhalf κ (parabolicPullback l (unshiftedClassicalField f hf C q hq) b l)
      (parabolicPullback (l^3) (fun w => f (spaceTimeProj w)) b l)
      (parabolicPullback l J b l) (parabolicPullback 1 Y b l) (parabolicPullback l Z b l)
      (parabolicPullback (l^3) (defectField N f C 0) b l)
      (parabolicPullback (l^2) (defectField N f C 1) b l)
      (parabolicPullback (l^3) (defectField N f C 2) b l)
      (l^2*C₁ C) (l^2*C₂ C)
      (by simpa [defectPrimitive, C₁, C₂, l, b, J, Y, Z] using hlocal) z hz
    rw [mwDataFunctional_scaled_eq] at hg
    change ENNReal.ofReal |l*unshiftedClassicalField f hf C q hq (coverMap 0 t x₀ z) -
      l*treeJ N f (spaceTimeProj (coverMap 0 t x₀ z))| ≤ _ at hg
    rw [← mul_sub, abs_mul, abs_of_pos hl] at hg
    have hbudget : scaledAttachmentFunctional N κ Φ hΦ f C b l
        (parabolicClosedNbhd mwCylinder 1) ≤ ENNReal.ofReal l*M := by
      apply scaledAttachmentFunctional_le N κ Φ hΦ hf C b hl
        ((coverScale_le_half ht).trans (by norm_num))
      rintro _ ⟨w, hw, rfl⟩
      exact coverMap_enlargement_subset ht 0 hx₀.2 hw
    have hb := hg.trans (mul_le_mul_right (max_le_max le_rfl hbudget) (Cdef κ : ℝ≥0∞))
    have hR : ENNReal.ofReal ((Cdef κ : ℝ)*max 2 (l*M.toReal)) =
        (Cdef κ : ℝ≥0∞)*max 2 (ENNReal.ofReal l*M) := by
      rw [ENNReal.ofReal_mul (Cdef κ).coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_max, ENNReal.ofReal_mul hl.le, ENNReal.ofReal_toReal hM]
      norm_num
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (Cdef κ : ℝ)*max 2 (l*M.toReal))).mp
    rw [hR]
    exact hb
  have h := cover_torus_norm_of_normalized_row ht 0 (smoothClassicalRemainder N f hf C q hq)
    (Cdef κ : ℝ) M.toReal (Cdef κ).coe_nonneg ENNReal.toReal_nonneg
    (smoothClassicalRemainder_continuousOn N f hf C q hq) hpoint
  simpa only [zero_add, ENNReal.ofReal_toReal hM,
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal] using h

end GlobalPhi43.Attachment

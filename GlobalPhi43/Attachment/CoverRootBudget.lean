module

public import GlobalPhi43.Attachment.CoverTreeScaling

/-! The normalized actual tree/defect functional is at most lambda times
the original cover functional. All quantities remain extended-valued. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal

namespace GlobalPhi43.Attachment

/-- Taking the exact source root cancels the exact scaling degree. -/
theorem cover_scaled_root_le {l d : ℝ} (hl : 0 < l) (hd : 0 < d)
    {A B : ℝ≥0∞} (h : A ≤ ENNReal.ofReal (l^d)*B) :
    A^(d⁻¹) ≤ ENNReal.ofReal l * B^(d⁻¹) := by
  calc
    _ ≤ (ENNReal.ofReal (l^d)*B)^(d⁻¹) := ENNReal.rpow_le_rpow h (inv_nonneg.mpr hd.le)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hd.le),
        ← ENNReal.ofReal_rpow_of_pos hl, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hd.ne', ENNReal.rpow_one]

/-- The actual normalized nine-tree/three-defect functional, using the scaled local-data tuple, not the canonical lift of a new artificial forcing. -/
@[expose] def scaledAttachmentFunctional (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (b : ParabolicSpace) (l : ℝ)
    (D : Set ParabolicSpace) : ℝ≥0∞ :=
  max (⨆ τ : LocalTree, scaledAttachmentTreeSeminorm N κ Φ hΦ f C b l D τ ^ (τ.degree κ.1)⁻¹)
    (max (localScalarSup (parabolicPullback (l^3) (defectField N f C 0) b l) D ^ (1/3 : ℝ))
      (max (localScalarSup (parabolicPullback (l^2) (defectField N f C 1) b l) D ^ (1/2 : ℝ))
        (localScalarSup (parabolicPullback (l^3) (defectField N f C 2) b l) D ^ (1/3 : ℝ))))

/-- No bounded-defect estimate, solution bound, slice estimate or finiteness hypothesis is assumed.
The domain on the right is any genuine superset of sigma(D). -/
theorem scaledAttachmentFunctional_le (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (C : RenormalisationConstants)
    (b : ParabolicSpace) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1)
    (D E : Set ParabolicSpace) (hDE : parabolicMap b l '' D ⊆ E) :
    scaledAttachmentFunctional N κ Φ hΦ f C b l D ≤
      ENNReal.ofReal l * attachmentFunctional N κ Φ hΦ f C E := by
  have ht (τ : LocalTree) :
      scaledAttachmentTreeSeminorm N κ Φ hΦ f C b l D τ ^ (τ.degree κ.1)⁻¹ ≤
        ENNReal.ofReal l * attachmentFunctional N κ Φ hΦ f C E := by
    have hn := (scaledAttachmentTreeSeminorm_le N κ Φ hΦ hf C b hl hl1 D τ).trans
      (mul_le_mul_right (attachmentTreeSeminorm_mono N κ Φ hΦ f C hDE τ) _)
    have hr := cover_scaled_root_le hl (LocalTree.degree_pos (by linarith only [κ.2.2]) τ) hn
    apply hr.trans
    apply mul_le_mul_right
    exact (le_iSup (fun τ => attachmentTreeSeminorm N κ Φ hΦ f C E τ ^ (τ.degree κ.1)⁻¹) τ).trans
      (le_max_left _ _)
  have he := defect_sup_scaling (defectField N f C 0) (defectField N f C 1)
    (defectField N f C 2) b hl D
  have hdef (i : Fin 3) (n : ℕ) (hn : 0 < n)
      (hscale : localScalarSup (parabolicPullback (l^n) (defectField N f C i) b l) D =
        ENNReal.ofReal (l^n)*localScalarSup (defectField N f C i) (parabolicMap b l '' D)) :
      localScalarSup (parabolicPullback (l^n) (defectField N f C i) b l) D ^ ((n : ℝ)⁻¹) ≤
        ENNReal.ofReal l * localScalarSup (defectField N f C i) E ^ ((n : ℝ)⁻¹) := by
    apply cover_scaled_root_le hl (by exact_mod_cast hn)
    rw [hscale, Real.rpow_natCast]
    exact mul_le_mul_right (cover_scalarSup_mono _ hDE) _
  have h0 := hdef 0 3 (by decide) he.1
  have h1 := hdef 1 2 (by decide) he.2.1
  have h2 := hdef 2 3 (by decide) he.2.2
  norm_num only [Nat.cast_ofNat, inv_eq_one_div] at h0 h1 h2
  unfold scaledAttachmentFunctional
  refine max_le (iSup_le ht) (max_le ?_ (max_le ?_ ?_))
  · exact h0.trans (mul_le_mul_right ((le_max_left _ _).trans (le_max_right _ _)) _)
  · exact h1.trans (mul_le_mul_right
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) _)
  · exact h2.trans (mul_le_mul_right
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) _)

/-- The exact physical cover budget, uniformly before applying the bounded-defect estimate. -/
theorem cover_scaled_functional_le {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (s : ℝ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {x₀ : Fin 3 → ℝ}
    (hx₀ : x₀ ∈ coverGrid (coverScale t)) :
    scaledAttachmentFunctional N κ Φ hΦ a.forcing a.constants (coverBase s t x₀)
      (coverScale t) (parabolicClosedNbhd mwCylinder 1) ≤
      ENNReal.ofReal (coverScale t) *
        attachmentFunctional N κ Φ hΦ a.forcing a.constants (Flow.coverRegion s) := by
  apply scaledAttachmentFunctional_le N κ Φ hΦ (Flow.smooth_of_moderateLift a.moderate)
    a.constants _ (coverScale_pos ht.1) ((coverScale_le_half ht).trans (by norm_num))
  rintro _ ⟨z, hz, rfl⟩
  exact coverMap_enlargement_subset ht s hx₀.2 hz

end GlobalPhi43.Attachment

module

public import GlobalPhi43.MW20.CompactTestIntegral
public import GlobalPhi43.MW20.CylinderTesting

/-!
# Boundedness of the actual source testing fields
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- Actual source averages are bounded from continuity on the closed source
cylinder alone; nothing is imposed on the field outside it. -/
theorem sourceSup_bddAbove_pastSmooth (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (f : ParabolicSpace → ℝ) (hf : ContinuousOn f sourceClosedCylinder)
    {T S : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTS : T ≤ S) :
    BddAbove ((fun x => |∫ y, f (x + y) ∂infiniteKernelMeasure Φ hΦ T hT|) '' sourceCylinder S) := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hf.abs).bddAbove
  refine ⟨B, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hb : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, ‖f (x + y)‖ ≤ B := by
    filter_upwards [infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTS hx] with y hy
    rw [Real.norm_eq_abs]
    exact hB ⟨x + y, sourceCylinder_subset_closed (sub_nonneg.mpr hTS) hy, rfl⟩
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- Bounded source fields are closed under addition. -/
theorem sourceSup_bddAbove_add {f g : ParabolicSpace → ℝ} {S : ℝ}
    (hf : BddAbove ((fun z => |f z|) '' sourceCylinder S))
    (hg : BddAbove ((fun z => |g z|) '' sourceCylinder S)) :
    BddAbove ((fun z => |f z + g z|) '' sourceCylinder S) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, ?_⟩
  rintro a ⟨z, hz, rfl⟩
  dsimp only
  exact (abs_add_le _ _).trans (add_le_add (hM ⟨z, hz, rfl⟩) (hN ⟨z, hz, rfl⟩))

/-- Bounded source fields are closed under subtraction. -/
theorem sourceSup_bddAbove_sub {f g : ParabolicSpace → ℝ} {S : ℝ}
    (hf : BddAbove ((fun z => |f z|) '' sourceCylinder S))
    (hg : BddAbove ((fun z => |g z|) '' sourceCylinder S)) :
    BddAbove ((fun z => |f z - g z|) '' sourceCylinder S) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, ?_⟩
  rintro a ⟨z, hz, rfl⟩
  dsimp only
  exact (abs_sub _ _).trans (add_le_add (hM ⟨z, hz, rfl⟩) (hN ⟨z, hz, rfl⟩))

/-- Every real coefficient preserves boundedness, with no restriction on
its sign or dependence. -/
theorem sourceSup_bddAbove_const_mul {f : ParabolicSpace → ℝ} {S : ℝ}
    (hf : BddAbove ((fun z => |f z|) '' sourceCylinder S)) (c : ℝ) :
    BddAbove ((fun z => |c * f z|) '' sourceCylinder S) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨|c| * M, ?_⟩
  rintro a ⟨z, hz, rfl⟩
  dsimp only
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM ⟨z, hz, rfl⟩) (abs_nonneg _)

/-- Integer powers preserve boundedness on the actual cylinder. -/
theorem sourceSup_bddAbove_pow {f : ParabolicSpace → ℝ} {S : ℝ}
    (hf : BddAbove ((fun z => |f z|) '' sourceCylinder S)) (n : ℕ) :
    BddAbove ((fun z => |f z ^ n|) '' sourceCylinder S) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨(max M 0) ^ n, ?_⟩
  rintro a ⟨z, hz, rfl⟩
  dsimp only
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((hM ⟨z, hz, rfl⟩).trans (le_max_left _ _)) n

end GlobalPhi43.MW20

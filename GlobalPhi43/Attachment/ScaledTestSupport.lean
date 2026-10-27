module

public import GlobalPhi43.Attachment.ScaledTestBounds

/-! Support and ordinary L1 bounds for scaled tests with an explicit derivative allowance. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures

/-- The support radius of a scaled profile is R T. -/
theorem rescaled_eq_zero_outside {φ : ParabolicSpace → ℝ} {R : ℝ}
    (hs : ∀ z, R < parabolicNorm z → φ z = 0) {T : ℝ} (hT : 0 < T)
    {x y : ParabolicSpace} (hy : R * T < parabolicNorm (y - x)) :
    rescaledTestFunction φ T x y = 0 := by
  unfold rescaledTestFunction
  rw [hs _ ?_, mul_zero]
  rw [parabolicNorm_parabolicDilate_inv hT, lt_inv_mul_iff₀ hT]
  simpa only [mul_comm] using hy

open scoped ContDiff in
/-- A smooth profile with the stated support gives the exact semigroup support predicate. -/
theorem isSupported_rescaled_of_radius {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {R : ℝ} (hR : 0 < R) (hs : ∀ z, R < parabolicNorm z → φ z = 0)
    {T : ℝ} (hT : 0 < T) (x : ParabolicSpace) :
    parabolicSemigroup.IsSupported (rescaledTestFunction φ T x) x (R * T) := by
  have hc : HasCompactSupport (rescaledTestFunction φ T x) :=
    hasCompactSupport_of_eq_zero (mul_pos hR hT) x (fun _ hy => rescaled_eq_zero_outside hs hT hy)
  have hcont := (contDiff_rescaledTestFunction hφ T x).continuous
  exact ⟨hcont.measurable, hcont.integrable_of_hasCompactSupport hc,
    fun _ hy => rescaled_eq_zero_outside hs hT hy⟩

/-- The ordinary L1 scaled-test estimate with the same compact support constant. -/
theorem integral_abs_rescaled_le {φ : ParabolicSpace → ℝ} (hφ : Continuous φ)
    {K : Set ParabolicSpace} (hK : IsCompact K) (hs : ∀ z, z ∉ K → φ z = 0)
    {B : ℝ} (hB : ∀ z, |φ z| ≤ B) {T : ℝ} (hT : 0 < T) (x : ParabolicSpace) :
    ∫ y, |rescaledTestFunction φ T x y| ≤ volume.real K * B := by
  rw [integral_abs_rescaled_eq φ hT x]
  exact integral_abs_le_compact hφ hK hs hB

end GlobalPhi43.Attachment

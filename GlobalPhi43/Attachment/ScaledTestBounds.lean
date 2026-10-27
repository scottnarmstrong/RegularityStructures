module

public import GlobalPhi43.Attachment.Pairing
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The C4-to-L1 estimates for scaled compact tests. The derivative allowance is an arbitrary
real B; the C4 norm can be inserted without changing this analytic statement. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures Set

/-- A compactly supported function bounded by B has L1 norm at most volume(support ball) B. -/
theorem integral_abs_le_compact {φ : ParabolicSpace → ℝ} (hφ : Continuous φ)
    {K : Set ParabolicSpace} (hK : IsCompact K) (hs : ∀ z, z ∉ K → φ z = 0)
    {B : ℝ} (hB : ∀ z, |φ z| ≤ B) :
    ∫ z, |φ z| ≤ volume.real K * B := by
  let S := K
  have hS : MeasurableSet S := hK.measurableSet
  have hfin : volume S ≠ ⊤ := hK.measure_ne_top
  have hc : HasCompactSupport φ := hK.of_isClosed_subset isClosed_closure
    (closure_minimal (fun z hz => by_contra fun hn => hz (hs z hn)) hK.isClosed)
  have hint : Integrable (fun z => |φ z|) := (hφ.integrable_of_hasCompactSupport hc).abs
  have hind : Integrable (S.indicator fun _ => B) :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hfin)
  have hle : ∀ z, |φ z| ≤ S.indicator (fun _ => B) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]; exact hB z
    · rw [indicator_of_notMem hz, hs z hz]
      simp only [abs_zero, le_refl]
  have h := integral_mono hint hind hle
  simpa only [integral_indicator_const _ hS, smul_eq_mul] using h

/-- Pointwise generator control from derivatives of orders two and four. -/
theorem abs_generator_le_derivative_bound {φ : ParabolicSpace → ℝ} {B : ℝ}
    (hB : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ B) (z : ParabolicSpace) :
    |parabolicGenerator φ z| ≤ (generatorTimeCoeff + 3 * generatorSpaceCoeff) * B := by
  have ht : |iteratedFDeriv ℝ 2 φ z (fun _ => timeDir)| ≤ B := by
    have h := (iteratedFDeriv ℝ 2 φ z).le_opNorm (fun _ => timeDir)
    simp only [norm_timeDir, Finset.prod_const_one, mul_one] at h
    exact (Real.norm_eq_abs _ ▸ h).trans (hB 2 (by decide) z)
  have hs (i : Fin 3) : |iteratedFDeriv ℝ 4 φ z (fun _ => spaceDir i)| ≤ B := by
    have h := (iteratedFDeriv ℝ 4 φ z).le_opNorm (fun _ => spaceDir i)
    simp only [norm_spaceDir, Finset.prod_const_one, mul_one] at h
    exact (Real.norm_eq_abs _ ▸ h).trans (hB 4 le_rfl z)
  have hsum : |∑ i, iteratedFDeriv ℝ 4 φ z (fun _ => spaceDir i)| ≤ 3 * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => hs i
      _ = _ := by simp
  unfold parabolicGenerator
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos generatorTimeCoeff_pos, abs_of_pos generatorSpaceCoeff_pos]
  have h1 := mul_le_mul_of_nonneg_left ht generatorTimeCoeff_pos.le
  have h2 := mul_le_mul_of_nonneg_left hsum generatorSpaceCoeff_pos.le
  nlinarith

/-- The generator vanishes outside the same support ball. -/
theorem generator_eq_zero_outside {φ : ParabolicSpace → ℝ} {K : Set ParabolicSpace}
    (hK : IsClosed K) (hs : ∀ z, z ∉ K → φ z = 0) {z : ParabolicSpace}
    (hz : z ∉ K) : parabolicGenerator φ z = 0 := by
  apply parabolicGenerator_eq_zero_of_eventuallyEq
  filter_upwards [hK.isOpen_compl.mem_nhds hz] with w hw
  exact hs w hw

open scoped ContDiff in
/-- The unscaled generator estimate; the support radius is fixed before the test. -/
theorem integral_abs_generator_le {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set ParabolicSpace} (hK : IsCompact K) (hs : ∀ z, z ∉ K → φ z = 0)
    {B : ℝ} (hB : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ B) :
    ∫ z, |parabolicGenerator φ z| ≤
      volume.real K * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * B := by
  have h := integral_abs_le_compact (continuous_parabolicGenerator hφ) hK
    (fun _ hz => generator_eq_zero_outside hK.isClosed hs hz) (abs_generator_le_derivative_bound hB)
  simpa only [mul_assoc] using h

/-- Rescaling preserves the L1 norm of an arbitrary profile. -/
theorem integral_abs_rescaled_eq (φ : ParabolicSpace → ℝ) {T : ℝ} (hT : 0 < T)
    (x : ParabolicSpace) :
    ∫ y, |rescaledTestFunction φ T x y| = ∫ y, |φ y| := by
  have he (y : ParabolicSpace) : |rescaledTestFunction φ T x y| =
      rescaledTestFunction (fun z => |φ z|) T x y := by
    unfold rescaledTestFunction
    rw [abs_mul, abs_of_pos (by positivity)]
  simp_rw [he]
  exact integral_rescaledTestFunction _ hT x

open scoped ContDiff in
/-- The scaled-generator estimate, with exactly the factor T^(-4). -/
theorem integral_abs_generator_rescaled_le {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K : Set ParabolicSpace} (hK : IsCompact K)
    (hs : ∀ z, z ∉ K → φ z = 0)
    {B : ℝ} (hB : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ B)
    {T : ℝ} (hT : 0 < T) (x : ParabolicSpace) :
    ∫ y, |parabolicGenerator (rescaledTestFunction φ T x) y| ≤
      (volume.real K * (generatorTimeCoeff + 3 * generatorSpaceCoeff) * B) *
        T ^ (-(4 : ℝ)) := by
  have he (y : ParabolicSpace) : |parabolicGenerator (rescaledTestFunction φ T x) y| =
      (T ^ 4)⁻¹ * |rescaledTestFunction (parabolicGenerator φ) T x y| := by
    rw [parabolicGenerator_rescaledTestFunction hφ hT, abs_mul, abs_of_pos (by positivity)]
  simp_rw [he]
  rw [integral_const_mul, integral_abs_rescaled_eq _ hT x]
  have hp := mul_le_mul_of_nonneg_left (integral_abs_generator_le hφ hK hs hB)
    (show 0 ≤ (T ^ 4)⁻¹ by positivity)
  have hpow : T ^ (-(4 : ℝ)) = (T ^ 4)⁻¹ := by
    calc T ^ (-(4 : ℝ)) = (T ^ (4 : ℝ))⁻¹ := Real.rpow_neg hT.le 4
      _ = (T ^ (4 : ℕ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast T 4)
  simpa only [hpow, mul_comm (T ^ 4)⁻¹] using hp

end GlobalPhi43.Attachment

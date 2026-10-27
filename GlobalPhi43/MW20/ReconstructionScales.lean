module

public import GlobalPhi43.MW20.KernelPastSupport
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Dyadic scales and the actual infinite-kernel tails used by reconstruction.
The tail identities follow from the infinite-kernel convolution identities. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter
open scoped Topology

/-- The source scale T*2^(-n). -/
@[expose] noncomputable def reconstructionScale (T : ℝ) (n : ℕ) : ℝ := T / 2 ^ n

@[simp] theorem reconstructionScale_zero (T : ℝ) : reconstructionScale T 0 = T := by
  simp [reconstructionScale]

theorem reconstructionScale_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < reconstructionScale T n :=
  div_pos hT (by positivity)

theorem reconstructionScale_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : reconstructionScale T n ≤ T := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hT

theorem reconstructionScale_le_one {T : ℝ} (hT : T ≤ 1) (n : ℕ) : reconstructionScale T n ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).2
  exact hT.trans (one_le_pow₀ (by norm_num))

theorem reconstructionScale_succ (T : ℝ) (n : ℕ) :
    reconstructionScale T (n + 1) = reconstructionScale T n / 2 := by
  unfold reconstructionScale
  rw [pow_succ, div_mul_eq_div_div]

theorem reconstructionScale_eq_mul (T : ℝ) (n : ℕ) :
    reconstructionScale T n = T * (1 / 2 : ℝ) ^ n := by
  simp only [reconstructionScale, div_eq_mul_inv, one_mul, inv_pow]

theorem reconstructionScale_tendsto_zero (T : ℝ) :
    Tendsto (reconstructionScale T) atTop (𝓝 0) := by
  change Tendsto (fun n => reconstructionScale T n) atTop (𝓝 0)
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [reconstructionScale_eq_mul, mul_zero] using hp.const_mul T

/-- Exact source power identity, without a constant depending on the rate. -/
theorem reconstructionScale_rpow {T : ℝ} (hT : 0 ≤ T) (a : ℝ) (n : ℕ) :
    reconstructionScale T n ^ a = T ^ a * ((1 / 2 : ℝ) ^ a) ^ n := by
  rw [reconstructionScale_eq_mul, Real.mul_rpow hT (by positivity),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) a n]

/-- The actual constructed infinite kernel at a dyadic source scale. -/
@[expose] noncomputable def reconstructionTail (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) (hT : 0 < T) (n : ℕ) : Measure ParabolicSpace :=
  infiniteKernelMeasure Φ hΦ (reconstructionScale T n) (reconstructionScale_pos hT n)

theorem reconstructionTail_probability (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (reconstructionTail Φ hΦ T hT n) :=
  infiniteKernelMeasure_probability Φ hΦ (reconstructionScale_pos hT n) (reconstructionScale_le_one hT₁ n)


/-- The block identity, with the actual dyadic infinite tails. -/
theorem reconstructionTail_block (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (n : ℕ) :
    infiniteKernelMeasure Φ hΦ T hT =
      (dyadicKernelMeasure (kernelProfileMeasure Φ) T n).conv (reconstructionTail Φ hΦ T hT n) := by
  simpa only [reconstructionTail, reconstructionScale] using infiniteKernelMeasure_block Φ hΦ hT hT₁ n

/-- The one-step identity at every dyadic scale. -/
theorem reconstructionTail_recursion (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (n : ℕ) :
    reconstructionTail Φ hΦ T hT n =
      (dyadicKernelFactor (kernelProfileMeasure Φ) T n).conv (reconstructionTail Φ hΦ T hT (n + 1)) := by
  have hf : dyadicKernelFactor (kernelProfileMeasure Φ) (reconstructionScale T n) 0 =
      dyadicKernelFactor (kernelProfileMeasure Φ) T n := by
    simpa only [reconstructionScale, Nat.add_zero] using
      (dyadicKernelFactor_shift (kernelProfileMeasure Φ) T n 0).symm
  have hh := infiniteKernelMeasure_recursion Φ hΦ (reconstructionScale_pos hT n)
    (reconstructionScale_le_one hT₁ n)
  simpa only [reconstructionTail, reconstructionScale_succ, hf] using hh

end GlobalPhi43.MW20

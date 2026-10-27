module

public import GlobalPhi43.MW20.KernelMeasure
public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# Finite dyadic MW20 kernels at parabolic scales

We use the base's `ParabolicSpace` and `parabolicDilate`. Starting with a
probability measure `μ`, the factors are its pushforwards at scales
`T / 2, T / 4, ...`. The finite scale identity is exact for these measures.
This does not yet identify their smooth densities or construct their limit.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- The `j`-th parabolically rescaled probability measure, first scale `T/2`. -/
@[expose] noncomputable def dyadicKernelFactor
    (μ : Measure ParabolicSpace) (T : ℝ) (j : ℕ) : Measure ParabolicSpace :=
  μ.map (parabolicDilate (T / (2 : ℝ) ^ (j + 1)))

/-- The actual finite dyadic convolution starting from the probability measure `μ`. -/
@[expose] noncomputable def dyadicKernelMeasure
    (μ : Measure ParabolicSpace) (T : ℝ) (n : ℕ) : Measure ParabolicSpace :=
  kernelMeasure (dyadicKernelFactor μ T) 0 n

instance dyadicKernelFactor_probability (μ : Measure ParabolicSpace)
    [IsProbabilityMeasure μ] (T : ℝ) (j : ℕ) :
    IsProbabilityMeasure (dyadicKernelFactor μ T j) := by
  unfold dyadicKernelFactor
  infer_instance

instance dyadicKernelMeasure_probability (μ : Measure ParabolicSpace)
    [IsProbabilityMeasure μ] (T : ℝ) (n : ℕ) :
    IsProbabilityMeasure (dyadicKernelMeasure μ T n) := by
  unfold dyadicKernelMeasure
  infer_instance

/-- Shifting the dyadic index is exactly the same as shrinking `T`. -/
theorem dyadicKernelFactor_shift (μ : Measure ParabolicSpace) (T : ℝ) (n j : ℕ) :
    dyadicKernelFactor μ T (n + j) = dyadicKernelFactor μ (T / 2 ^ n) j := by
  have hs : T / (2 : ℝ) ^ (n + j + 1) = (T / 2 ^ n) / 2 ^ (j + 1) := by
    rw [Nat.add_assoc, pow_add, div_mul_eq_div_div]
  simp only [dyadicKernelFactor, hs]

/-- MW20 (2.7), as an equality of actual finite dyadic probability measures. -/
theorem dyadicKernelMeasure_add (μ : Measure ParabolicSpace) [IsProbabilityMeasure μ]
    (T : ℝ) (n m : ℕ) :
    dyadicKernelMeasure μ T (n + m) =
      (dyadicKernelMeasure μ T n).conv (dyadicKernelMeasure μ (T / 2 ^ n) m) := by
  unfold dyadicKernelMeasure
  rw [kernelMeasure_add]
  congr 1
  rw [kernelMeasure_shift]
  congr 1
  funext j
  simp only [Nat.zero_add, dyadicKernelFactor_shift]

end GlobalPhi43.MW20

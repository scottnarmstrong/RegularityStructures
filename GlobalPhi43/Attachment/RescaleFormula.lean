module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling

/-! The coordinate formula for parabolic test rescaling. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures

/-- Equality with the coordinate rescaling formula, including at zero scale. -/
theorem rescaledTestFunction_formula (φ : ParabolicSpace → ℝ) (T : ℝ)
    (x y : ParabolicSpace) :
    rescaledTestFunction φ T x y =
      T ^ (-5 : ℤ) * φ ((y - x).1 / T ^ 2, T⁻¹ • (y - x).2) := by
  simp [rescaledTestFunction, parabolicDilate, div_eq_mul_inv, mul_comm]

end GlobalPhi43.Attachment

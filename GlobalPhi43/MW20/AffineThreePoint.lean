module

public import GlobalPhi43.MW20.AffineSeminorm

/-! The exact three-remainder identity underlying MW20 (2.38). The affine
coefficient is kept as a spatial vector; the three actual U values and all
three residuals remain in the signed combination. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set

/-- The spatial affine pairing appearing in MW20 (2.6). -/
@[expose] def spatialPair (a : Fin 3 → ℝ) (x y : ParabolicSpace) : ℝ :=
  ∑ j, a j * (y.2 j - x.2 j)

/-- Exact signed identity for the three residuals; no estimate or norm
assumption is used to replace the actual two-variable source field. -/
theorem affine_three_remainder_identity
    (U : ParabolicSpace × ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    (x z y : ParabolicSpace) :
    spatialPair (ν x - ν z) z y =
      (U (x, y) - U (x, z) - U (z, y)) -
      (U (x, y) - spatialPair (ν x) x y) +
      (U (x, z) - spatialPair (ν x) x z) +
      (U (z, y) - spatialPair (ν z) z y) := by
  have hp : spatialPair (ν x - ν z) z y =
      spatialPair (ν x) x y - spatialPair (ν x) x z - spatialPair (ν z) z y := by
    unfold spatialPair
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hp]
  ring

/-- Three bounded source remainders and the actual three-point defect bound
the increment of the affine coefficient tested in the cone direction. -/
theorem affine_three_remainder_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    (x z y : ParabolicSpace) {Exy Exz Ezy M : ℝ}
    (hxy : |U (x, y) - spatialPair (ν x) x y| ≤ Exy)
    (hxz : |U (x, z) - spatialPair (ν x) x z| ≤ Exz)
    (hzy : |U (z, y) - spatialPair (ν z) z y| ≤ Ezy)
    (hthree : |U (x, y) - U (x, z) - U (z, y)| ≤ M) :
    |spatialPair (ν x - ν z) z y| ≤ Exy + Exz + Ezy + M := by
  rw [affine_three_remainder_identity U ν x z y]
  have h₁ := abs_sub (U (x, y) - U (x, z) - U (z, y))
    (U (x, y) - spatialPair (ν x) x y)
  have h₂ := abs_add_le
    ((U (x, y) - U (x, z) - U (z, y)) - (U (x, y) - spatialPair (ν x) x y))
    (U (x, z) - spatialPair (ν x) x z)
  have h₃ := abs_add_le
    ((U (x, y) - U (x, z) - U (z, y)) - (U (x, y) - spatialPair (ν x) x y) +
      (U (x, z) - spatialPair (ν x) x z))
    (U (z, y) - spatialPair (ν z) z y)
  linarith

end GlobalPhi43.MW20

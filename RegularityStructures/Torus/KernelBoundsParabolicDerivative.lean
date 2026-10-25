/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsSpatialSingularDerivative
public import RegularityStructures.Torus.KernelBoundsBasic
public import RegularityStructures.Torus.KernelBoundsGlobal

/-!
# Parabolic singular bounds for the differentiated torus heat kernel

The centred Gaussian derivative estimates are now expressed in the parabolic size used by
Hairer's Assumption 5.1, (5.4).  The constants are chosen before the point and scale binders,
so they are uniform over the torus and over positive times in the singular regime.

Source: [Hai14] = arXiv:1303.5113v4, §5.1, (5.4).
-/

@[expose] public noncomputable section

open Real Set
open scoped Topology

namespace RegularityStructures

theorem singular_bound_of_power_mul_le {q A C : ℝ} {m : ℕ} (hq : 0 < q)
    (h : q ^ m * A ≤ C) : A ≤ C * q ^ (-(m : ℝ)) := by
  have hqpow : 0 < q ^ m := pow_pos hq m
  have hdiv : A ≤ C / q ^ m := (le_div_iff₀ hqpow).2 (by
    simpa [mul_comm] using h)
  calc
    A ≤ C / q ^ m := hdiv
    _ = C * q ^ (-(m : ℝ)) := by
      rw [div_eq_mul_inv, Real.rpow_neg hq.le, Real.rpow_natCast]

end RegularityStructures

end

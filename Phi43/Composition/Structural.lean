/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Composition.Consts
public import Phi43.FixedPointF.WindowNear
public import Phi43.FixedPointFDiff.WindowNearDiff
public import Phi43.TimeSlice.OneCoeff
public import Phi43.TimeSlice.OneCoeffDiff
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The structural constants of the restart compositions, as explicit functions

The six structural constants (one- and two-model window fixed points, one- and two-model time
slices, one- and two-model restart packages), chosen once from their existence theorems; they
depend only on `(κ, η, N)`.  With them, `compTime`, `compR₀` and `compK` are the explicit
existence time, fixed-point radius and slice constant of `Composition.restart_fixedPoint_exists`,
shared by `Composition.restart_fixedPoint_diff`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.Composition

variable (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - η)
  (N : ℕ) (hN : 3 ≤ N)

/-- The constant of the one-model window fixed point. -/
def fpC : ℝ := Classical.choose (phi43FixedPointF_window_nearOne κ hη₁ hκη hN (kernelPair_ann N))

/-- The constant of the two-model window fixed point. -/
def fpCd : ℝ :=
  Classical.choose (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη hN (kernelPair_ann N))

/-- The constant of the one-model time slice. -/
def tsC : ℝ :=
  Classical.choose (TimeSlice.phi43_one_coeff_fixedPoint_le κ hη₁ hκη hN (kernelPair_ann N))

/-- The constant of the two-model time slice. -/
def tsCd : ℝ :=
  Classical.choose (TimeSlice.phi43_one_coeff_fixedPoint_diff_le κ hη₁ hκη hN (kernelPair_ann N))

/-- The constant of the one-model restart package. -/
def rqC : ℝ := Classical.choose (Restart.restart_quantitative (κ := κ) N hN)

/-- The constant of the two-model restart package. -/
def rqCd : ℝ := Classical.choose (Restart.restart_quantitative_diff (κ := κ) N hN)

/-- **The restart existence time** `t₀ L B`. -/
def compTime (Gc : ℕ → ℝ) (L B : ℝ) : ℝ :=
  restartTime κ η Gc (fpC κ η hη₁ hκη N hN) (fpCd κ η hη₁ hκη N hN) (rqC κ N hN) L B

/-- **The fixed-point radius** `R₀ L B` (bound on the inhomogeneity). -/
def compR₀ (Gc : ℕ → ℝ) (L B : ℝ) : ℝ := datumR η Gc L B

/-- **The slice constant** `K L B`. -/
def compK (Gc : ℕ → ℝ) (L B : ℝ) : ℝ :=
  sliceConst κ (tsC κ η hη₁ hκη N hN) (rqC κ N hN) B (datumR η Gc L B)

end RegularityStructures.Phi43.Composition

end

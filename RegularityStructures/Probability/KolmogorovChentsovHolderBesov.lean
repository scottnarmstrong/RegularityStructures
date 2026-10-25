/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovSupNorm
public import RegularityStructures.Torus.HolderBesov

/-!
# Kolmogorov--Chentsov in negative Hölder--Besov spaces

This is the `𝒞^η` application.  The completion-valued process has the
initial moment written in the native `holderBesovENorm` notation on the
dense continuous-map subspace.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem enorm_toHolderBesov (η : NegExponent) (f : C(Torus3, ℝ)) :
    ‖toHolderBesov η f‖ₑ = holderBesovENorm η f := by
  calc
    ‖toHolderBesov η f‖ₑ = ENNReal.ofReal ‖toHolderBesov η f‖ := by
      symm
      exact ofReal_norm (toHolderBesov η f)
    _ = ENNReal.ofReal ((holderBesovENorm η f).toReal) := by
      rw [norm_toHolderBesov]
    _ = holderBesovENorm η f :=
      ENNReal.ofReal_toReal (holderBesovENorm_lt_top η.2.le f).ne

end RegularityStructures

end

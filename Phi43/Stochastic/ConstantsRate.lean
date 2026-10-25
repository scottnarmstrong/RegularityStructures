/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateWick
public import Phi43.Stochastic.ConstantsRateSunset

/-!
# Power rates for the renormalisation-constant differences

Import this module for the two power-rate theorems
`constantsRate_wick` and `constantsRate_sunset`:
for every mollifier `ρ` and every `N`, the differences `C₁^ε - C̃₁^ε` and `C₂^ε - C̃₂^ε` converge
to the finite limits `constantsComparison_wickLimit N` and `constantsComparison_sunsetLimit N`
at the rate `ε^{1/6}` on `(0, 1]`.

The proof proceeds through translation moduli: `‖G(· - h) - G‖_{3/2}`, `‖K(· - h) - K‖_{3/2}` and
`‖R(· - h) - R‖₃` are `O(size(h)^{1/3})`, `O(size(h)^{1/3})` and `O(size(h)^{1/6})`
(`ConstantsRateModuliKernel`, `ConstantsRateModuliR`), from the pointwise bounds
`ConstantsRateMassiveMain` and `ConstantsRateHairerTorus`; a quantitative approximate identity
(`ConstantsRateApprox`) and Young/Hölder estimates (`ConstantsRateYoung`, `ConstantsRateCorr`,
`ConstantsRateSunsetEst`) give the rates.
-/

@[expose] public section

end

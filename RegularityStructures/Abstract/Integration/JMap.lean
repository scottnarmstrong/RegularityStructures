/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.JMapCoeff
public import RegularityStructures.Abstract.Integration.JMapLinear

/-!
# Hairer's map `J(x)` (facade)

The coefficients `jCoeff M N x i k` of `J(x) e_i = ∑_k X^k/k! jCoeff ..` [Hai14, (5.11)] and their
bound `abs_jCoeff_le`.
-/

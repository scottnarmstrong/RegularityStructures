/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.FunctionModel
public import RegularityStructures.Abstract.Singular.Ident.Pointwise
public import RegularityStructures.Abstract.Singular.Ident.LatticeAvg
public import RegularityStructures.Abstract.Singular.Ident.LatticeLimit
public import RegularityStructures.Abstract.Singular.Ident.DomIntegrable
public import RegularityStructures.Abstract.Singular.Ident.Integrals
public import RegularityStructures.Abstract.Singular.Ident.RemElementary
public import RegularityStructures.Abstract.Singular.Ident.ShellSum

/-!
# Identification of the abstract `𝒦_γ + R_γ` with convolution (aggregator)

For a model realised by smooth functions (`Model.IsSmoothFunctionModelBelow`) and a singular
modelled distribution in the window setting, the lattice reconstruction is the pointwise one
(`Model.latticeRecon_eq_integral`, Remark 3.15 of [Hai14]), and the unit coefficient of
`𝒦_γ f + R_γ f` is the convolution of the heat kernel with `R̃f`
(`Model.kGammaRem_apply_emb_zero_eq_integral_heat`).
-/

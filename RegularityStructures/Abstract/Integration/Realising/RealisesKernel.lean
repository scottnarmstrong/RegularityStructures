/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Integration
public import RegularityStructures.Abstract.RegularityStructureDegrees
public import RegularityStructures.Abstract.Polynomial
public import RegularityStructures.Abstract.Integration.Realising.Reg
public import RegularityStructures.Abstract.Integration.Realising.RealReg
public import RegularityStructures.Abstract.Polynomial.Model.Reg

/-!
# Models realising a kernel

`Model.RealisesKernel` is the integral clause of [Hai14, Definition 5.9] on the basis vectors of
`V`: `Q_t Π_x I e_i = Q_t g_{x,i}` for `t > 0`, with `K_n = annShell N n`. `Model.IsRealising`
adds compatibility with the polynomials.

Source: [Hai14, Definition 5.9].
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- The clause of [Hai14, Definition 5.9] on the basis vectors `e_i`, `deg i < γ`, of `V`:
`Q_t Π_x I e_i = Q_t g_{x,i}` for `t > 0` (kernel `K_n = annShell N n`). -/
def RealisesKernel (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ (x : ParabolicSpace) (i : ι), 𝒯.deg i < γ → (Pi.single i 1 : ι → ℝ) ∈ V →
    ∀ t : ℝ, 0 < t → ∀ z : ParabolicSpace,
      M.regPi x (I (Pi.single i 1)) t z = realReg M N x i t z

/-- `M` realises the kernel for `I` [Hai14, Definition 5.9]: the integral clause
(`RealisesKernel`) and compatibility with the polynomials of `P` (`IsPolyCompatible`). -/
structure IsRealising (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) :
    Prop where
  realises : M.RealisesKernel N γ I V
  poly : M.IsPolyCompatible P

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.RealGerm
public import RegularityStructures.Abstract.Integration.Realising
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Model

/-!
# Models realising a kernel with a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Realising.Reg` and
`RegularityStructures.Abstract.Integration.Realising.Def`, with the consistency bound. A model
`(Π, Γ)` realises `K = ∑_n scaledShell h n` for `I` [Hai14, Definition 5.9, Remark 5.10] if, for the
basis vectors `e_i` of the sector `V` with `deg i < γ`,
`Q_t Π_x I e_i = realRegP M h x i t = Q_t g_{x,i}` for `t > 0` (`Model.RealisesKernelP`); the
polynomial part `IsPolyCompatible` does not involve the kernel and is reused. `Model.IsRealisingP`
is their conjunction. The germ `g_{x,i} = realGermP M h x i` has polynomial growth
(`polyBounded_realGermP`), and the consistency bound at degree `deg i + 2` holds
(`abs_regPi_integral_leP`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 5.9, Remark 5.10.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The `Q`-family `t ↦ Q_t g_{x,i}` of the realised distribution
`ψ ↦ ∫ ψ(y) ∑_n (Π_x e_i)(K^{deg i}_{n;xy}) dy`, extended by `0` to `t ≤ 0`. -/
def realRegP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (i : ι) : ℝ → ParabolicSpace → ℝ := fun t z =>
  if 0 < t then parabolicSemigroup.apply t (realGermP M h x i) z else 0

namespace Model

/-- The clause of [Hai14, Definition 5.9] on the basis vectors `e_i`, `deg i < γ`, of `V`:
`Q_t Π_x I e_i = Q_t g_{x,i}` for `t > 0` (kernel `K_n = scaledShell h n`). -/
def RealisesKernelP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (γ : ℝ)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ (x : ParabolicSpace) (i : ι), 𝒯.deg i < γ → (Pi.single i 1 : ι → ℝ) ∈ V →
    ∀ t : ℝ, 0 < t → ∀ z : ParabolicSpace,
      M.regPi x (I (Pi.single i 1)) t z = realRegP M h x i t z

/-- `M` realises the kernel with profile `h` for `I` [Hai14, Definition 5.9]: the integral clause
(`RealisesKernelP`) and compatibility with the polynomials of `P` (`IsPolyCompatible`). -/
structure IsRealisingP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (γ : ℝ)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (V : Submodule ℝ (ι → ℝ)) : Prop where
  realises : M.RealisesKernelP h γ I V
  poly : M.IsPolyCompatible P

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {h : ParabolicSpace → ℝ} {N : ℕ}

theorem realRegP_of_pos (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (i : ι) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    realRegP M h x i t z = parabolicSemigroup.apply t (realGermP M h x i) z := by
  simp [realRegP, ht]

end RegularityStructures

end

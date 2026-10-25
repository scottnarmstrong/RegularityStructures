/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2Field
public import Phi43.BPHZ.TreeI3PsiField
public import Phi43.BPHZ.TreeI2Psi2Field
public import Phi43.BPHZ.TreeWickCube

/-!
# Tree fields with arbitrary renormalisation constants

The tree fields `hairerPsiWickSquare`, `hairerI3PsiField`, `hairerI2Psi2Field`, `hairerI3Psi2Field`
use the constants `c_ε = hairerWickConstant N ρ ε` and `C₂ = hairerSunsetConstant N ρ ε`.  To state
the bridge with general constants `C = (C₁, C₂)` we restate the same pathwise expressions with
arbitrary real constants `c₁ c₂`.  With the Hairer constants they are definitionally the existing
fields.  We also record the integral identity that turns a combination of two convolutions with the
kernel increment into one convolution of the combination.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The pathwise Wick square `Ψ² - c₁` with an arbitrary constant. -/
def hairerTreePsiSq {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ : ℝ) (ω : Ω)
    (z : SpaceTime) : ℝ :=
  hairerPsiField N ξ ω z ^ 2 - c₁

/-- The pathwise Wick cube `Ψ³ - 3 c₁ Ψ` with an arbitrary constant. -/
def hairerTreePsiCube {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ : ℝ) (ω : Ω)
    (z : SpaceTime) : ℝ :=
  hairerPsiField N ξ ω z ^ 3 - 3 * c₁ * hairerPsiField N ξ ω z

/-- The tree `I(Ψ³)Ψ` with an arbitrary constant. -/
def hairerTreeI3Psi {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ : ℝ) (x : SpaceTime)
    (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, hairerI2Psi2Kernel N x y w * hairerTreePsiCube N ξ c₁ ω w) * hairerPsiField N ξ ω y

/-- The tree `I(Ψ²)Ψ²` with arbitrary constants. -/
def hairerTreeI2Psi2 {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ c₂ : ℝ) (x : SpaceTime)
    (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, hairerI2Psi2Kernel N x y w * hairerTreePsiSq N ξ c₁ ω w) *
    hairerTreePsiSq N ξ c₁ ω y - c₂

/-- The tree `I(Ψ³)Ψ²` with arbitrary constants. -/
def hairerTreeI3Psi2 {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ c₂ : ℝ) (x : SpaceTime)
    (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, hairerI2Psi2Kernel N x y w * hairerTreePsiCube N ξ c₁ ω w) *
    hairerTreePsiSq N ξ c₁ ω y - 3 * c₂ * hairerPsiField N ξ ω y

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)

/-- A convolution of the kernel increment against `f - c g` is the combination of the four
convolutions, for continuous `f` and `g`. -/
theorem integral_hairerI2Psi2Kernel_mul_sub_const_mul (x y : SpaceTime) {f g : SpaceTime → ℝ}
    (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    ∫ w, hairerI2Psi2Kernel N x y w * (f w - c * g w) =
      ((∫ w, hairerKernelTorus N (y - w) * f w) - ∫ w, hairerKernelTorus N (x - w) * f w) -
        c * ((∫ w, hairerKernelTorus N (y - w) * g w) -
          ∫ w, hairerKernelTorus N (x - w) * g w) := by
  have hfy := integrable_hairerKernelTorus_sub_mul_continuous N y hf
  have hfx := integrable_hairerKernelTorus_sub_mul_continuous N x hf
  have hgy := integrable_hairerKernelTorus_sub_mul_continuous N y hg
  have hgx := integrable_hairerKernelTorus_sub_mul_continuous N x hg
  have hpt : ∀ w, hairerI2Psi2Kernel N x y w * (f w - c * g w) =
      (hairerKernelTorus N (y - w) * f w - hairerKernelTorus N (x - w) * f w) -
        c * (hairerKernelTorus N (y - w) * g w - hairerKernelTorus N (x - w) * g w) := by
    intro w
    unfold hairerI2Psi2Kernel
    ring
  simp_rw [hpt]
  have h1 : Integrable (fun w => hairerKernelTorus N (y - w) * f w -
      hairerKernelTorus N (x - w) * f w) := hfy.sub hfx
  have h2 : Integrable (fun w => c * (hairerKernelTorus N (y - w) * g w -
      hairerKernelTorus N (x - w) * g w)) := (hgy.sub hgx).const_mul c
  rw [integral_sub h1 h2, integral_sub hfy hfx, integral_const_mul, integral_sub hgy hgx]

/-- The convolution of the constant `1` with the kernel increment vanishes. -/
theorem integral_hairerKernelTorus_sub_mul_one_sub (x y : SpaceTime) :
    ((∫ w, hairerKernelTorus N (y - w) * (1 : ℝ)) -
      ∫ w, hairerKernelTorus N (x - w) * (1 : ℝ)) = 0 := by
  have h := integral_hairerI2Psi2Kernel N x y
  unfold hairerI2Psi2Kernel at h
  rw [integral_sub (integrable_hairerKernelTorus_sub N y)
    (integrable_hairerKernelTorus_sub N x)] at h
  simpa only [mul_one] using h

end RegularityStructures.Phi43

end

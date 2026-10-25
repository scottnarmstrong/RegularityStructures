/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.ModelSpace
public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Analysis.Parabolic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.FinCases

/-!
# The algebraic canonical lift from abstract kernel data

This file gives the algebraic, smooth fixed-regularisation version of Hairer's canonical lift in
§8.2, equations (8.18)--(8.21), specialised to the finite Φ⁴₃ sector.  The kernel record is
deliberately abstract: its function field, convolution operator, and Taylor-coefficient
functionals are independent inputs.  No theorem here identifies the latter with the value and
gradient of the former; a later heat-kernel module must provide that identification.

Only spatial Taylor terms are needed here: every retained integrated symbol has homogeneity below
two, while the parabolic time monomial has degree two.  Thus the displayed Taylor polynomial is
the truncation with parabolic degree strictly below the target homogeneity.  The source is Hairer,
arXiv:1303.5113v4, §8.2 (8.18)--(8.21), and the Φ⁴₃ kernel choice is described in §10.5 before
Theorem 10.22.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

open RegularityStructures

open scoped ContDiff in
/-- A smooth spatially periodic realisation of the noise. -/
structure CanonicalNoise where
  /-- The smooth noise on space-time. -/
  zeta : ParabolicSpace → ℝ
  /-- Smoothness of the fixed regularisation. -/
  smooth : ContDiff ℝ ∞ zeta
  /-- Periodicity in the three spatial directions. -/
  periodic : ∀ (n : Fin 3 → ℤ) (z : ParabolicSpace),
    zeta (z.1, fun i => z.2 i + (n i : ℝ)) = zeta z

/-- Abstract kernel data for the finite algebraic lift.

The fields are intentionally independent.  A concrete module may set `convolutionOp` to
convolution by `kernel` and `taylorConstant`/`taylorSpatial` to the value/gradient of that
convolution, but the algebraic theorems in this file assume only the supplied operations. -/
structure CanonicalKernel where
  /-- A candidate translation-invariant kernel `K`; no relation to the other fields is assumed. -/
  kernel : ParabolicSpace → ℝ
  /-- Abstract convolution data, to be identified with `K * f` by a concrete analytic module. -/
  convolutionOp : (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  /-- Abstract constant Taylor data for the convolution. -/
  taylorConstant : (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  /-- Abstract spatial first Taylor data for the convolution. -/
  taylorSpatial : (ParabolicSpace → ℝ) → Fin 3 → ParabolicSpace → ℝ

namespace CanonicalKernel

variable (K : CanonicalKernel)

/-- The abstract convolution operation supplied by `K`.

For a concrete kernel record this is to be instantiated by `K * f`; no integral or regularity
claim is made at this algebraic layer. -/
def convolution (K : CanonicalKernel) (f : ParabolicSpace → ℝ) (y : ParabolicSpace) : ℝ :=
  K.convolutionOp f y

/-- The finite parabolic Taylor polynomial built from the supplied abstract coefficients. -/
def taylorPolynomial (r : ℝ) (f : ParabolicSpace → ℝ)
    (z y : ParabolicSpace) : ℝ :=
  (if 0 < r then K.taylorConstant f z else 0) +
    (if 1 < r then
      ∑ i : Fin 3, K.taylorSpatial f i z *
        (parabolicCoords y i.succ - parabolicCoords z i.succ)
    else 0)

@[simp]
theorem taylorPolynomial_of_nonpos {r : ℝ} (hr : r ≤ 0)
    (f : ParabolicSpace → ℝ) (z y : ParabolicSpace) :
    K.taylorPolynomial r f z y = 0 := by
  have hr1 : ¬ 1 < r := by linarith
  simp [taylorPolynomial, hr, hr1]

end CanonicalKernel

/-- The fixed-`κ` data used by the finite canonical lift. -/
structure CanonicalData (κ : Kappa) where
  noise : CanonicalNoise
  kernel : CanonicalKernel

namespace CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

local notation "E" => ParabolicSpace

/-- The finite Taylor-subtracted integration operation. -/
def integrate (r : ℝ) (f : E → ℝ) (z y : E) : ℝ :=
  CanonicalKernel.convolution D.kernel f y - D.kernel.taylorPolynomial r f z y

def relCoord (z y : E) (i : Fin 4) : ℝ :=
  parabolicCoords y i - parabolicCoords z i

def localPolynomialQuadratic (z y : E) (p : Sym2 (Fin 3)) : ℝ :=
  Sym2.lift ⟨fun i j => relCoord z y i.succ * relCoord z y j.succ, by
    intro i j
    change relCoord z y i.succ * relCoord z y j.succ =
      relCoord z y j.succ * relCoord z y i.succ
    rw [mul_comm]⟩ p

def globalPolynomialQuadratic (y : E) (p : Sym2 (Fin 3)) : ℝ :=
  Sym2.lift ⟨fun i j => parabolicCoords y i.succ * parabolicCoords y j.succ, by
    intro i j
    change parabolicCoords y i.succ * parabolicCoords y j.succ =
      parabolicCoords y j.succ * parabolicCoords y i.succ
    rw [mul_comm]⟩ p

def localPsi : CanonicalData κ → E → ℝ := fun D =>
  fun y => D.integrate (homogeneity κ .psi) D.noise.zeta 0 y

def localIPsi : CanonicalData κ → E → E → ℝ := fun D z y =>
  D.integrate (homogeneity κ .iPsi) (localPsi D) z y

def localPsiSq : CanonicalData κ → E → ℝ := fun D y =>
  localPsi D y * localPsi D y

def localPsiCube : CanonicalData κ → E → ℝ := fun D y =>
  localPsiSq D y * localPsi D y

def localPsiX (D : CanonicalData κ) (z : E) (i : Fin 3) : E → ℝ :=
  fun y => localPsi D y * relCoord z y i.succ

def localPsiSqX (D : CanonicalData κ) (z : E) (i : Fin 3) : E → ℝ :=
  fun y => localPsiSq D y * relCoord z y i.succ

def localIPsiSq : CanonicalData κ → E → E → ℝ := fun D z y =>
  D.integrate (homogeneity κ .iPsiSq) (localPsiSq D) z y

def localIPsiCube : CanonicalData κ → E → E → ℝ := fun D z y =>
  D.integrate (homogeneity κ .iPsiCube) (localPsiCube D) z y

def localIPsiPsi (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsi D z y * localPsi D y

def localIPsiPsiSq (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsi D z y * localPsiSq D y

def localIPsiSqPsi (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsiSq D z y * localPsi D y

def localIPsiSqPsiSq (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsiSq D z y * localPsiSq D y

def localIPsiCubePsi (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsiCube D z y * localPsi D y

def localIPsiCubePsiSq (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsiCube D z y * localPsiSq D y

def localIPsiCubeSq (D : CanonicalData κ) (z : E) : E → ℝ :=
  fun y => localIPsiCube D z y * localIPsiCube D z y

/-- The local, based canonical lift on the symbol basis.

The argument `z` is the base point and `y` is the evaluation point.  Products are pointwise and
the three displayed integrated primitives use `K * f` minus the finite Taylor polynomial. -/
def localPiBasis (z : E) : Symbol → E → ℝ
  | .one => fun _ => 1
  | .noise => D.noise.zeta
  | .x0 => fun y => relCoord z y 0
  | .x i => fun y => relCoord z y i.succ
  | .xMul p => fun y => localPolynomialQuadratic z y p
  | .psi => localPsi D
  | .iPsi => localIPsi D z
  | .psiSq => localPsiSq D
  | .psiCube => localPsiCube D
  | .psiX i => localPsiX D z i
  | .psiSqX i => localPsiSqX D z i
  | .iPsiSq => localIPsiSq D z
  | .iPsiCube => localIPsiCube D z
  | .iPsiPsi => localIPsiPsi D z
  | .iPsiPsiSq => localIPsiPsiSq D z
  | .iPsiSqPsi => localIPsiSqPsi D z
  | .iPsiSqPsiSq => localIPsiSqPsiSq D z
  | .iPsiCubePsi => localIPsiCubePsi D z
  | .iPsiCubePsiSq => localIPsiCubePsiSq D z
  | .iPsiCubeSq => localIPsiCubeSq D z

def globalPsi : CanonicalData κ → E → ℝ := fun D =>
  CanonicalKernel.convolution D.kernel D.noise.zeta

def globalIPsi : CanonicalData κ → E → ℝ := fun D =>
  CanonicalKernel.convolution D.kernel (globalPsi D)

def globalPsiSq : CanonicalData κ → E → ℝ := fun D y =>
  globalPsi D y * globalPsi D y

def globalPsiCube : CanonicalData κ → E → ℝ := fun D y =>
  globalPsiSq D y * globalPsi D y

def globalPsiX (D : CanonicalData κ) (i : Fin 3) : E → ℝ :=
  fun y => globalPsi D y * parabolicCoords y i.succ

def globalPsiSqX (D : CanonicalData κ) (i : Fin 3) : E → ℝ :=
  fun y => globalPsiSq D y * parabolicCoords y i.succ

def globalIPsiSq : CanonicalData κ → E → ℝ := fun D =>
  CanonicalKernel.convolution D.kernel (globalPsiSq D)

def globalIPsiCube : CanonicalData κ → E → ℝ := fun D =>
  CanonicalKernel.convolution D.kernel (globalPsiCube D)

def globalIPsiPsi : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsi D y * globalPsi D y

def globalIPsiPsiSq : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsi D y * globalPsiSq D y

def globalIPsiSqPsi : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsiSq D y * globalPsi D y

def globalIPsiSqPsiSq : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsiSq D y * globalPsiSq D y

def globalIPsiCubePsi : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsiCube D y * globalPsi D y

def globalIPsiCubePsiSq : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsiCube D y * globalPsiSq D y

def globalIPsiCubeSq : CanonicalData κ → E → ℝ := fun D y =>
  globalIPsiCube D y * globalIPsiCube D y

/-- The unbased lift `Π` in Hairer's proof of (8.23)--(8.26). -/
def globalPiBasis : Symbol → E → ℝ
  | .one => fun _ => 1
  | .noise => D.noise.zeta
  | .x0 => fun y => parabolicCoords y 0
  | .x i => fun y => parabolicCoords y i.succ
  | .xMul p => fun y => globalPolynomialQuadratic y p
  | .psi => globalPsi D
  | .iPsi => globalIPsi D
  | .psiSq => globalPsiSq D
  | .psiCube => globalPsiCube D
  | .psiX i => globalPsiX D i
  | .psiSqX i => globalPsiSqX D i
  | .iPsiSq => globalIPsiSq D
  | .iPsiCube => globalIPsiCube D
  | .iPsiPsi => globalIPsiPsi D
  | .iPsiPsiSq => globalIPsiPsiSq D
  | .iPsiSqPsi => globalIPsiSqPsi D
  | .iPsiSqPsiSq => globalIPsiSqPsiSq D
  | .iPsiCubePsi => globalIPsiCubePsi D
  | .iPsiCubePsiSq => globalIPsiCubePsiSq D
  | .iPsiCubeSq => globalIPsiCubeSq D

/-- The linear extension of the local lift to the free model space. -/
def localPi (z : E) : T →ₗ[ℝ] (E → ℝ) :=
  Finsupp.linearCombination ℝ (D.localPiBasis z)

/-- The linear extension of the unbased lift to the free model space. -/
def globalPi : T →ₗ[ℝ] (E → ℝ) :=
  Finsupp.linearCombination ℝ D.globalPiBasis

@[simp]
theorem localPi_basis (z : E) (τ : Symbol) :
    D.localPi z (basis τ) = D.localPiBasis z τ := by
  simp [localPi, basis]

@[simp]
theorem globalPi_basis (τ : Symbol) :
    D.globalPi (basis τ) = D.globalPiBasis τ := by
  simp [globalPi, basis]

end CanonicalData

end RegularityStructures.Phi43

end

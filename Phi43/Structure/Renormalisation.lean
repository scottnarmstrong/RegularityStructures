/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.ModelSpace
import Mathlib.Tactic

/-!
# Renormalisation of the finite Φ⁴₃ sector

This is Hairer's finite map from §9.2 and §10.5.  On this truncation it is
the finite polynomial `id + A + A²/2`, with `A = -C₁L₁-C₂L₂`, agreeing with
the table (9.3); we do not identify that table with an infinite exponential.
The maps `L₁` and `L₂` are defined on the free basis and extended linearly;
`M` is the finite exponential `id + A + A²/2`, with `A = -C₁L₁-C₂L₂`;
the square is retained because it contributes the `3C₁² I(Ψ)` term in (9.3).

The ansatz is Hairer's (9.22).  The final identity uses the full product of
that ansatz three times, followed by projection to non-positive homogeneity;
it is the finite algebraic form of Proposition 9.10 and (9.21).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

abbrev RenormalisationConstants := ℝ × ℝ

def C₁ (C : RenormalisationConstants) : ℝ := C.1

def C₂ (C : RenormalisationConstants) : ℝ := C.2

/-- Hairer's first contraction operator, before multiplying by `C₁`. -/
def L1BasisAction : Symbol → T
  | .psiSq => basis .one
  | .psiCube => (3 : ℝ) • basis .psi
  | .iPsiCube => (3 : ℝ) • basis .iPsi
  | .psiSqX i => basis (.x i)
  | .iPsiPsiSq => basis .iPsi
  | .iPsiSqPsiSq => basis .iPsiSq
  | .iPsiCubePsi => (3 : ℝ) • basis .iPsiPsi
  | .iPsiCubePsiSq => basis .iPsiCube + (3 : ℝ) • basis .iPsiPsiSq
  | _ => 0

/-- Hairer's second contraction operator, before multiplying by `C₂`. -/
def L2BasisAction : Symbol → T
  | .iPsiSqPsiSq => basis .one
  | .iPsiCubePsiSq => (3 : ℝ) • basis .psi
  | _ => 0

/-- The two contraction operators extended linearly from the finite basis. -/
def L1 : T →ₗ[ℝ] T := Finsupp.linearCombination ℝ L1BasisAction

def L2 : T →ₗ[ℝ] T := Finsupp.linearCombination ℝ L2BasisAction

@[simp]
theorem L1_basis (τ : Symbol) : L1 (basis τ) = L1BasisAction τ := by
  simp [L1, basis]

@[simp]
theorem L2_basis (τ : Symbol) : L2 (basis τ) = L2BasisAction τ := by
  simp [L2, basis]

def contraction (C : RenormalisationConstants) : T →ₗ[ℝ] T :=
  -(C₁ C) • L1 - (C₂ C) • L2

/-- The finite polynomial used here, through the nonzero square term in (9.3). -/
def finiteExponential (A : T →ₗ[ℝ] T) : T →ₗ[ℝ] T :=
  LinearMap.id + A + (1 / 2 : ℝ) • A.comp A

/-- The finite map matching Hairer's table (9.3) on this sector. -/
def M (C : RenormalisationConstants) : T →ₗ[ℝ] T :=
  finiteExponential (contraction C)

@[simp]
theorem contraction_basis (C : RenormalisationConstants) (τ : Symbol) :
    contraction C (basis τ) =
      -(C₁ C) • L1BasisAction τ - (C₂ C) • L2BasisAction τ := by
  simp [contraction]

@[simp]
theorem M_basis (C : RenormalisationConstants) (τ : Symbol) :
    M C (basis τ) = basis τ + contraction C (basis τ) +
      (1 / 2 : ℝ) • contraction C (contraction C (basis τ)) := by
  simp [M, finiteExponential]

/-- The finite integration map on the retained symbols. -/
def integrationBasisAction : Symbol → T
  | .noise => basis .psi
  | .psi => basis .iPsi
  | .psiSq => basis .iPsiSq
  | .psiCube => basis .iPsiCube
  | _ => 0

def integration : T →ₗ[ℝ] T :=
  Finsupp.linearCombination ℝ integrationBasisAction

@[simp]
theorem integration_basis (τ : Symbol) : integration (basis τ) =
    integrationBasisAction τ := by
  simp [integration, basis]

end RegularityStructures.Phi43

end

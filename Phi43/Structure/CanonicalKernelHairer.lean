/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalModelData
public import RegularityStructures.Analysis.Heat.Causal
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RegularityStructures.Analysis.Heat.Kernel

/-!
# The truncated Hairer kernel in the canonical lift

For `N`, the singular part of Hairer's causal kernel is the actual function
`K_N = ∑ n, annShellC N n`.  This module installs that kernel in the finite
canonical data used by `CanonicalModelData`: convolution is convolution by
`K_N`, and the Taylor data are, by definition, the value and spatial gradient
of that convolution.  The pointwise decomposition is Hairer [Hai14, Lemma 5.5]
and the Taylor convention is [Hai14, (5.12), (8.20)].

The analytic convergence and model estimates are deliberately kept separate:
the annShell decomposition supplies the exact singular kernel here, while the
abstract Schauder layer supplies the pairing estimates for Q-distributions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

local notation "E" => ParabolicSpace

/-- The singular kernel obtained from Hairer's polynomial-annihilating shells. -/
def hairerKernel (N : ℕ) (z : E) : ℝ := ∑' n : ℕ, annShellC N n z

/-- Convolution by the singular kernel `hairerKernel N`.

The Bochner integral is used pointwise; the analytic module which supplies a
particular noise proves the corresponding integrability. -/
def hairerConvolution (N : ℕ) (f : E → ℝ) (z : E) : ℝ :=
  ∫ w, hairerKernel N (z - w) * f w

/-- The spatial section of `K_N * f` at a fixed time. -/
def hairerSpatialSection (N : ℕ) (f : E → ℝ) (z : E) (x : Fin 3 → ℝ) : ℝ :=
  hairerConvolution N f (z.1, x)

/-- The spatial gradient of `K_N * f`, written coordinatewise. -/
def hairerSpatialGradient (N : ℕ) (f : E → ℝ) (i : Fin 3) (z : E) : ℝ :=
  fderiv ℝ (hairerSpatialSection N f z) z.2 (Pi.single i 1)

/-- The `CanonicalKernel` obtained from Hairer's singular kernel decomposition. -/
def hairerCanonicalKernel (N : ℕ) : CanonicalKernel where
  kernel := hairerKernel N
  convolutionOp := hairerConvolution N
  taylorConstant := hairerConvolution N
  taylorSpatial := fun f i z => hairerSpatialGradient N f i z

/-- The canonical data using the truncated Hairer kernel. -/
def hairerCanonicalData (N : ℕ) {κ : Kappa} (noise : CanonicalNoise) :
    CanonicalData κ :=
  ⟨noise, hairerCanonicalKernel N⟩

theorem hairerKernel_decomposition {N : ℕ} {z : E} (hz : z ≠ 0) :
    heatKernelR4 z = hairerKernel N z + annRemainderC N z := by
  exact heatKernelR4_eq_tsum_annShellC hz

theorem hairerKernel_eq_heat_sub_remainder {N : ℕ} {z : E} (hz : z ≠ 0) :
    hairerKernel N z = heatKernelR4 z - annRemainderC N z := by
  rw [hairerKernel_decomposition hz]
  linarith

end RegularityStructures.Phi43

end

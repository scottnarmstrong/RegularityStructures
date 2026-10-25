/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants
public import Phi43.Structure.CanonicalKernelHairer
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The truncated-kernel versions of `C₁` and `C₂`

This file fixes the convention used for the comparison of the constants in Section 7 of the
statement.  Hairer's causal kernel is first periodised in the spatial
variables, and then mollified with the same periodised parabolic mollifier as the massive
kernel.  We use the causal `annShellC` construction, which is the kernel used by the abstract
fixed-point layer; the separate noncausal `annShell` construction is not identified
with it.  Thus the definitions below are literal torus versions of Hairer (10.33) and (10.41).

The support convention of the statement is that the support of `K` has parabolic radius
less than `1/4`; under that convention its spatial periodisation is the kernel used below.
The present file records the definitions and algebraic identities.  The uniform estimates needed
for the comparison are proved in the later `ConstantsComparison*` modules.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- Spatial periodisation of Hairer's Euclidean singular kernel. -/
def hairerKernelTorus (N : ℕ) (z : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ,
    hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))

/-- The mollification of `hairerKernelTorus N` by `ρ_ε^♯`. -/
def hairerMollifiedKernel (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (z : SpaceTime) : ℝ :=
  ∫ w, hairerKernelTorus N (z - w) * periodise ρ ε w

/-- The covariance formed from the mollified Hairer kernel. -/
def hairerCovariance (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (z : SpaceTime) : ℝ :=
  ∫ w, hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w

/-- Hairer's first renormalisation constant, (10.33), with the torus-periodised `K`. -/
def hairerWickConstant (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ∫ z, hairerMollifiedKernel N ρ ε z ^ 2

/-- Hairer's second renormalisation constant, (10.41), with the torus-periodised `K`. -/
def hairerSunsetConstant (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  2 * ∫ z, hairerKernelTorus N z * hairerCovariance N ρ ε z ^ 2

/-- The massive and truncated mollified kernels used in the first comparison. -/
def wickComparisonR (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  mollifiedKernel ρ ε z - hairerMollifiedKernel N ρ ε z

/-- The sum of the massive and truncated mollified kernels. -/
def wickComparisonP (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  mollifiedKernel ρ ε z + hairerMollifiedKernel N ρ ε z

/-- The unregularised kernel difference `R = G - K^♯` from Section 7. -/
def constantsComparisonR (N : ℕ) (z : SpaceTime) : ℝ :=
  massiveHeatKernel z - hairerKernelTorus N z

@[simp]
theorem constantsComparisonR_def (N : ℕ) (z : SpaceTime) :
    constantsComparisonR N z = massiveHeatKernel z - hairerKernelTorus N z :=
  rfl

theorem wickConstant_sub_hairerWickConstant_integrand (N : ℕ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (hG : Integrable (fun z : SpaceTime => mollifiedKernel ρ ε z ^ 2))
    (hK : Integrable (fun z : SpaceTime => hairerMollifiedKernel N ρ ε z ^ 2)) :
    wickConstant ρ ε - hairerWickConstant N ρ ε =
      ∫ z, wickComparisonR N ρ ε z * wickComparisonP N ρ ε z := by
  rw [wickConstant, hairerWickConstant, ← integral_sub hG hK]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp [wickComparisonR, wickComparisonP]
  ring

theorem sunsetConstant_sub_hairerSunsetConstant_integrand (N : ℕ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (hG : Integrable (fun z : SpaceTime => massiveHeatKernel z * covariance ρ ε z ^ 2))
    (hK : Integrable (fun z : SpaceTime => hairerKernelTorus N z *
      hairerCovariance N ρ ε z ^ 2))
    (hR : Integrable (fun z : SpaceTime => constantsComparisonR N z * covariance ρ ε z ^ 2))
    (hD : Integrable (fun z : SpaceTime => hairerKernelTorus N z *
      (covariance ρ ε z - hairerCovariance N ρ ε z) *
      (covariance ρ ε z + hairerCovariance N ρ ε z))) :
    sunsetConstant ρ ε - hairerSunsetConstant N ρ ε =
      2 * (∫ z, constantsComparisonR N z * covariance ρ ε z ^ 2) +
        2 * (∫ z, hairerKernelTorus N z *
          (covariance ρ ε z - hairerCovariance N ρ ε z) *
          (covariance ρ ε z + hairerCovariance N ρ ε z)) := by
  rw [sunsetConstant, hairerSunsetConstant]
  calc
    2 * (∫ z, massiveHeatKernel z * covariance ρ ε z ^ 2) -
          2 * (∫ z, hairerKernelTorus N z * hairerCovariance N ρ ε z ^ 2) =
        2 * ((∫ z, massiveHeatKernel z * covariance ρ ε z ^ 2) -
          (∫ z, hairerKernelTorus N z * hairerCovariance N ρ ε z ^ 2)) := by ring
    _ = 2 * ∫ z, (massiveHeatKernel z * covariance ρ ε z ^ 2 -
          hairerKernelTorus N z * hairerCovariance N ρ ε z ^ 2) := by
      rw [integral_sub hG hK]
    _ = 2 * (∫ z, constantsComparisonR N z * covariance ρ ε z ^ 2 +
          hairerKernelTorus N z *
            (covariance ρ ε z - hairerCovariance N ρ ε z) *
            (covariance ρ ε z + hairerCovariance N ρ ε z)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [constantsComparisonR]
      ring
    _ = 2 * (∫ z, constantsComparisonR N z * covariance ρ ε z ^ 2) +
          2 * (∫ z, hairerKernelTorus N z *
            (covariance ρ ε z - hairerCovariance N ρ ε z) *
            (covariance ρ ε z + hairerCovariance N ρ ε z)) := by
      rw [integral_add hR hD]
      ring

end RegularityStructures.Phi43

end

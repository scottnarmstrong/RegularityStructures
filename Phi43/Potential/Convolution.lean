/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.QKernel
public import Phi43.Inhomogeneity.DuhamelField
public import RegularityStructures.Analysis.Heat.Schauder.ConvolutionLineIter

/-!
# Convolution of a continuous function with a smooth compactly supported kernel

`potConv ξ g z = ∫ ξ(y) g(z - y) dy` is Mathlib's convolution `ξ ⋆ g` for the multiplication
pairing.  For `g` smooth with compactly supported derivatives and `ξ` continuous it is smooth and
`ddA l (ξ ⋆ g) = ξ ⋆ (ddA l g)` (`ddA_potConv`).  If `ξ` is spatially periodic so is `ξ ⋆ g`
(`perSmooth_potConv`), and the convolution commutes with time translations (`potConv_potShift`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Potential

/-- `(ξ ⋆ g)(z) = ∫ ξ(y) g(z - y) dy`. -/
def potConv (ξ g : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  ∫ y, ξ y * g (z - y)

/-- The time translation `ξ ↦ ξ(· + (a, 0))`. -/
def potShift (a : ℝ) (ξ : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  ξ (z.1 + a, z.2)

end RegularityStructures.Potential

end

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

private instance : (volume : Measure ParabolicSpace).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

theorem contDiff_potConv {ξ g : ParabolicSpace → ℝ} (hξ : Continuous ξ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ContDiff ℝ ∞ (potConv ξ g) :=
  RegularityStructures.contDiff_integral_mul_sub hξ.locallyIntegrable hg hc

theorem ddv_potConv {ξ g : ParabolicSpace → ℝ} (hξ : Continuous ξ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (j : Fin 4) (z : ParabolicSpace) :
    ddv j (potConv ξ g) z = potConv ξ (ddv j g) z :=
  congrFun (RegularityStructures.dirDeriv_integral_mul_sub hξ.locallyIntegrable hg hc (Datum.stBasis j)) z

theorem ddA_potConv {ξ g : ParabolicSpace → ℝ} (hξ : Continuous ξ) (hg : ContDiff ℝ ∞ g)
    (hc : ∀ l, HasCompactSupport (ddA l g)) :
    ∀ (l : List (Fin 4)) (z : ParabolicSpace), ddA l (potConv ξ g) z = potConv ξ (ddA l g) z
  | [], _ => rfl
  | j :: l, z => by
    have ih : ddA l (potConv ξ g) = potConv ξ (ddA l g) := funext (ddA_potConv hξ hg hc l)
    rw [show ddA (j :: l) (potConv ξ g) = ddv j (ddA l (potConv ξ g)) from rfl, ih,
      ddv_potConv hξ (contDiff_ddA hg l) (hc l)]
    rfl

/-- Convolution with a smooth compactly supported kernel preserves spatial periodicity. -/
theorem perSmooth_potConv {ξ g : ParabolicSpace → ℝ} (hξ : PerSmooth ξ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : PerSmooth (potConv ξ g) where
  smooth := contDiff_potConv hξ.smooth.continuous hg hc
  periodic z c hc0 := by
    unfold potConv
    have h := integral_add_right_eq_self (μ := (volume : Measure ParabolicSpace))
      (fun y : ParabolicSpace => ξ y * g (((z.1, z.2 + c) : ParabolicSpace) - y)) ((0, c) : ParabolicSpace)
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e1 : ξ (y + (0, c)) = ξ y := by
      have e0 : y + ((0 : ℝ), c) = (y.1, y.2 + c) := by ext <;> simp
      rw [e0]
      exact hξ.periodic y c hc0
    have e2 : ((z.1, z.2 + c) : ParabolicSpace) - (y + (0, c)) = z - y := by
      ext <;> simp
    simp only [e1, e2]

/-- The convolution commutes with the time translation: `((ξ(· + a)) ⋆ g)(z) = (ξ ⋆ g)(z + a)`. -/
theorem potConv_potShift (a : ℝ) (ξ g : ParabolicSpace → ℝ) (z : ParabolicSpace) :
    potConv (potShift a ξ) g z = potConv ξ g (z.1 + a, z.2) := by
  unfold potConv
  have h := integral_add_right_eq_self (μ := (volume : Measure ParabolicSpace))
    (fun y : ParabolicSpace => ξ y * g (((z.1 + a, z.2) : ParabolicSpace) - y))
    ((a, 0) : ParabolicSpace)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e : ((z.1 + a, z.2) : ParabolicSpace) - (y + (a, 0)) = z - y := by
    ext <;> simp
  have e' : ((y.1 + a, y.2) : ParabolicSpace) = y + (a, 0) := by ext <;> simp
  simp only [potShift, e, e']

end RegularityStructures.Potential

end

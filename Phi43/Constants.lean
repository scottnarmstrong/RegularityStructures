/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import RegularityStructures.Torus.HeatKernel

/-!
# The renormalisation constants

The constants of Definition 2.5 of the statement:
`G_ε = G * ρ_ε^♯`, `Q_ε(z) = ∫ G_ε(z + w) G_ε(w) dw`,
`C₁^ε = ∫ G_ε²` and `C₂^ε = 2 ∫ G Q_ε²`. They are the constants of [Hai14, (10.33) and (10.41)],
with Hairer's truncated heat kernel replaced by the massive heat kernel `G`.

Source: the statement, Definition 2.5; [Hai14, (10.33), (10.41)].
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- `G_ε(z) = ∫ G(z - w) ρ_ε^♯(w) dw`. -/
def mollifiedKernel (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, massiveHeatKernel (z - w) * periodise ρ ε w

/-- `Q_ε(z) = ∫ G_ε(z + w) G_ε(w) dw`, the covariance of the stationary mollified field. -/
def covariance (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w

/-- The Wick constant `C₁^ε = ∫ G_ε²`. -/
def wickConstant (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ∫ z, mollifiedKernel ρ ε z ^ 2

/-- The logarithmically divergent constant `C₂^ε = 2 ∫ G Q_ε²`. -/
def sunsetConstant (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  2 * ∫ z, massiveHeatKernel z * covariance ρ ε z ^ 2

end RegularityStructures.Phi43

end

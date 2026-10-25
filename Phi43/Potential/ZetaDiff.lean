/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.ZetaBound
public import Phi43.Potential.PairingDiff
public import Phi43.Potential.QKernel

/-!
# The forcing bound, two models: derivative bounds of the difference of the restarted forcings

For two renormalised canonical models `Z₁, Z₂` (of the noises `noise₁, noise₂`) with window
bounds for the restarts `Z_i.translate (s, 0)` and for their difference (`PiDiffBoundOn`,
`GammaDiffBoundOn`, constants at most `d`), the difference of the restarted forcings
`ζ₁ - ζ₂ = Q ∗ (noise₁ - noise₂)(· + (s, 0))` satisfies
`DerivHyp (ζ₁ - ζ₂) (Gc L * B') L` with `Gc = potWordConst N` and
`B' = d · r4ModelConst 𝒯⊕ · max(1, C_Γ) max(C_Π, 1)` (`derivHyp_zeta_restart_diff`).
-/

public section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace RegularityStructures.Phi43.Potential

open RegularityStructures RegularityStructures.Potential RegularityStructures.Phi43.LiftBounds
  RegularityStructures.Inhomogeneity

theorem ddv_sub {F G : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : Fin 4) :
    ddv j (F - G) = ddv j F - ddv j G := by
  funext z
  have h1 : DifferentiableAt ℝ F z := (hF.differentiable (by simp)) z
  have h2 : DifferentiableAt ℝ G z := (hG.differentiable (by simp)) z
  simp only [ddv, Pi.sub_apply]
  rw [fderiv_sub h1 h2]
  rfl

theorem ddA_sub {F G : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ∀ l : List (Fin 4), ddA l (F - G) = ddA l F - ddA l G
  | [] => rfl
  | j :: l => by
    show ddv j (ddA l (F - G)) = ddv j (ddA l F) - ddv j (ddA l G)
    rw [ddA_sub hF hG l]
    exact ddv_sub (contDiff_ddA hF l) (contDiff_ddA hG l) j

end RegularityStructures.Phi43.Potential

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceS4
public import RegularityStructures.Torus.KolmogorovHolderBesovConclusion

/-!
# Measurability inputs for the spatial Besov criterion

The negative Besov seminorm and the dyadic heat seminorms are continuous for the uniform
topology on continuous spatial functions. Joint heat evaluation is continuous as well.
Thus a measurable continuous-function-valued version supplies every measurability hypothesis
of the spatial Kolmogorov estimate for the norm (2.3) of the statement.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem continuous_holderBesovENorm_negative (η : NegExponent) :
    Continuous (holderBesovENorm η : C(Torus3, ℝ) → ℝ≥0∞) := by
  have he : (holderBesovENorm η : C(Torus3, ℝ) → ℝ≥0∞) =
      fun f => ENNReal.ofReal ‖toHolderBesov η f‖ := by
    funext f
    rw [norm_toHolderBesov, ENNReal.ofReal_toReal (holderBesovENorm_lt_top η.2.le f).ne]
  rw [he]
  exact ENNReal.continuous_ofReal.comp (toHolderBesov_lipschitzWith η).continuous.norm

theorem continuous_dyadicHolderBesovTerm (η : ℝ) (n : ℕ) :
    Continuous (dyadicHolderBesovTerm η n : C(Torus3, ℝ) → ℝ≥0∞) := by
  let a := (dyadicScale n) ^ (-η / 2)
  have ha : 0 ≤ a := Real.rpow_nonneg (dyadicScale_pos n).le _
  have he : (dyadicHolderBesovTerm η n : C(Torus3, ℝ) → ℝ≥0∞) =
      fun f => ENNReal.ofReal (a * ‖PDE.heatOp (dyadicScale (n + 1)) f‖) := by
    funext f
    rw [ENNReal.ofReal_mul ha, ofReal_norm, ContinuousMap.enorm_eq_iSup_enorm]
    unfold dyadicHolderBesovTerm
    congr 1
    apply iSup_congr
    intro x
    rw [PDE.heatOp_eq_heatSemigroup (dyadicScale_pos _)]
  rw [he]
  exact ENNReal.continuous_ofReal.comp
    (continuous_const.mul (PDE.heatOpCLM (E := ℝ) (dyadicScale (n + 1))).continuous.norm)

theorem continuous_heatSemigroup_apply {s : ℝ} (hs : 0 < s) :
    Continuous (fun q : C(Torus3, ℝ) × Torus3 => heatSemigroup s q.1 q.2) := by
  have hc : Continuous (fun q : C(Torus3, ℝ) × Torus3 => PDE.heatOp s q.1 q.2) :=
    continuous_eval.comp ((PDE.heatOpCLM (E := ℝ) s).continuous.prodMap continuous_id)
  convert hc using 1
  funext q
  exact (PDE.heatOp_eq_heatSemigroup hs q.1 q.2).symm

end RegularityStructures.Phi43

end

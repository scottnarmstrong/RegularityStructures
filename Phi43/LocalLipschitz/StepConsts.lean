/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.Datum
public import Phi43.Composition.DiffConsts

/-!
# The constants of the local Lipschitz step

For the datum size `L` and the bound `B` on the size `phi43Size` of the lifts:

* `stepBg B`: the derivative constant of the restarted forcing (`derivHyp_zeta_enlarged`);
* `stepDW B`: the factor turning the distance `δ` of the lifts into the window `Γ`-difference
  constant;
* `stepBd B`: the derivative constant of the difference of two forcings, per unit `δ`;
* `stepB B`: the size bound at which the restart compositions are applied (dominates `B`, `stepBg B`,
  `stepBd B`);
* `stepLψ N κ B`: the potential bound of `Ψ(s)`; `stepL N κ L B = L + stepLψ N κ B` bounds the datum
  `u(s) - Ψ(s)`;
* `stepTime`, `stepK`: the time and the Lipschitz constant of the step.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential RegularityStructures.Phi43.Composition

/-- The derivative constant of the restarted forcing. -/
def stepBg (B : ℝ) : ℝ := max 1 (chainG B) * B

/-- The window `Γ`-difference factor. -/
def stepDW (B : ℝ) : ℝ := max 1 (gammaDiffChainConst (Fintype.card SymbolF) B 1 16)

/-- The derivative constant of the difference of two forcings, per unit distance of the lifts. -/
def stepBd (B : ℝ) : ℝ := stepDW B * (max 1 (max (chainG B) (chainG B)) * max B 1)

/-- The size bound of the restart compositions. -/
def stepB (B : ℝ) : ℝ := max B (max (stepBg B) (stepBd B))

/-- The potential bound of `Ψ(s)`. -/
def stepLψ (N : ℕ) (κ : Kappa) (B : ℝ) : ℝ :=
  r4ModelConst (phi43RegularityStructureF κ) κ.1 * (max 1 (chainG B) * B) *
    (potKernelConst (potTail N) + potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise))) +
    2 * B

/-- The bound of the datum `u(s) - Ψ(s)`. -/
def stepL (N : ℕ) (κ : Kappa) (L B : ℝ) : ℝ := L + stepLψ N κ B

variable (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - η)
  (N : ℕ) (hN : 3 ≤ N)

/-- **The time of the local Lipschitz step.** -/
def stepTime (L B : ℝ) : ℝ :=
  compTime κ η hη₁ hκη N hN (forcingGc N κ) (stepL N κ L B) (stepB B)

/-- **The constant of the local Lipschitz step.** -/
def stepK (L B : ℝ) : ℝ :=
  (1 + compK' κ η hη₁ hκη N hN (forcingGc N κ) (stepL N κ L B) (stepB B)) *
    (8 + stepDW B * (max 1 (chainG B) * max B 1 * l8Const N κ))

end RegularityStructures.Phi43.LocalLipschitz

end

public section

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential RegularityStructures.Phi43.Composition

theorem one_le_stepDW (B : ℝ) : 1 ≤ stepDW B := le_max_left _ _

theorem le_stepB (B : ℝ) : B ≤ stepB B := le_max_left _ _

theorem stepBg_le_stepB (B : ℝ) : stepBg B ≤ stepB B :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem stepBd_le_stepB (B : ℝ) : stepBd B ≤ stepB B :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem stepBg_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ stepBg B :=
  mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB

theorem stepBd_nonneg (B : ℝ) : 0 ≤ stepBd B :=
  mul_nonneg (zero_le_one.trans (one_le_stepDW B))
    (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_right _ _)))

theorem stepLψ_nonneg (N : ℕ) (κ : Kappa) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ stepLψ N κ B := by
  unfold stepLψ
  have h1 := r4ModelConst_F_nonneg κ
  have h2 : 0 ≤ max 1 (chainG B) * B := mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB
  have h3 : 0 ≤ potKernelConst (potTail N) +
      potK1Const N ((phi43RegularityStructureF κ).deg (.old .noise)) :=
    add_nonneg (potKernelConst_pos (isUnitKernel_potTail N)).le (potK1Const_nonneg N _)
  positivity

theorem le_stepL (N : ℕ) (κ : Kappa) {L B : ℝ} (hB : 0 ≤ B) : L ≤ stepL N κ L B :=
  le_add_of_nonneg_right (stepLψ_nonneg N κ hB)

theorem l8Const_nonneg (N : ℕ) (κ : Kappa) : 0 ≤ l8Const N κ := by
  unfold l8Const
  exact mul_nonneg ((r4ModelConst_F_nonneg κ).trans (le_max_left _ _))
    (add_nonneg (potKernelConst_pos (isUnitKernel_potTail N)).le (potK1Const_nonneg N _))

end RegularityStructures.Phi43.LocalLipschitz

end

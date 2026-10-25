/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorBox
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRemainder
public import RegularityStructures.Analysis.Heat.Schauder.TaylorTySupport

/-!
# The generator commutes with the Taylor remainder

`parabolicGenerator (remJ s m J φ) = remJ s m J (parabolicGenerator φ)` for smooth `φ`
(`parabolicGenerator_remJ`), because `parabolicGenerator` commutes with shifts, derivatives and
linear combinations.  Hence the `L¹` bound of `remJ` applies to `L (remJ φ)` with `φ` replaced by
`L φ`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem parabolicGenerator_tayOp {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : ParabolicSpace) (s : ℝ) (m : ℕ) :
    parabolicGenerator (tayOp e s m φ) = tayOp e s m (parabolicGenerator φ) := by
  rw [tayOp_eq, tayOp_eq,
    parabolicGenerator_finset_sum _ fun p _ => contDiff_const.mul (contDiff_iterate_dirDeriv hφ e p)]
  funext w
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [parabolicGenerator_const_mul (contDiff_iterate_dirDeriv hφ e p)]
  simp only
  congr 1
  have : ∀ n : ℕ, parabolicGenerator ((dirDeriv e)^[n] φ) = (dirDeriv e)^[n] (parabolicGenerator φ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', parabolicGenerator_dirDeriv (contDiff_iterate_dirDeriv hφ e n),
        ih, Function.iterate_succ_apply']
  rw [this]

theorem parabolicGenerator_tyOp (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) :
    ∀ (J : List (Fin 4)) {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ →
      parabolicGenerator (tyOp s m J φ) = tyOp s m J (parabolicGenerator φ)
  | [], _, _ => rfl
  | _ :: J, _, hφ => by
    simp only [tyOp]
    rw [parabolicGenerator_tyOp s m J (contDiff_tayOp hφ _ _ _), parabolicGenerator_tayOp hφ]

theorem parabolicGenerator_remJ (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) (J : List (Fin 4))
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    parabolicGenerator (remJ s m J φ) = remJ s m J (parabolicGenerator φ) := by
  have hS : ContDiff ℝ ∞ fun w => φ (w + disp s J) := hφ.comp (contDiff_id.add contDiff_const)
  have : remJ s m J φ = fun w => φ (w + disp s J) - tyOp s m J φ w := rfl
  rw [this, parabolicGenerator_sub' hS (contDiff_tyOp s m J hφ), parabolicGenerator_shift,
    parabolicGenerator_tyOp s m J hφ]
  rfl

end RegularityStructures

end

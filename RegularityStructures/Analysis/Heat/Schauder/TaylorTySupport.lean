/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorTy
public import RegularityStructures.Analysis.Heat.Schauder.TaylorOp
public import RegularityStructures.Analysis.Heat.Schauder.TaylorOpIntegral

/-!
# Support of the Taylor operators

Smoothness and compact support of `tayOp` and `tyOp` applied to compactly supported smooth functions.
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem hasCompactSupport_tayOp {φ : ParabolicSpace → ℝ} (hφ : HasCompactSupport φ)
    (e : ParabolicSpace) (s : ℝ) (m : ℕ) : HasCompactSupport (tayOp e s m φ) := by
  rw [tayOp_eq]
  have : ∀ p ∈ Finset.range (m + 1), HasCompactSupport
      (fun w => (((Nat.factorial p : ℕ) : ℝ)⁻¹ * s ^ p) * (dirDeriv e)^[p] φ w) := fun p _ =>
    (hasCompactSupport_iterate_dirDeriv hφ e p).mul_left
  exact hasCompactSupport_finset_sum' _ this

theorem contDiff_tyOp (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) :
    ∀ (J : List (Fin 4)) {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → ContDiff ℝ ∞ (tyOp s m J φ)
  | [], _, hφ => hφ
  | _ :: J, _, hφ => contDiff_tyOp s m J (contDiff_tayOp hφ _ _ _)

theorem hasCompactSupport_tyOp (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) :
    ∀ (J : List (Fin 4)) {φ : ParabolicSpace → ℝ}, HasCompactSupport φ →
      HasCompactSupport (tyOp s m J φ)
  | [], _, hφ => hφ
  | _ :: J, _, hφ => hasCompactSupport_tyOp s m J (hasCompactSupport_tayOp hφ _ _ _)

end RegularityStructures

end

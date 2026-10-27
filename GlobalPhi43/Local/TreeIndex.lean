/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! The finite tree index and leaf degrees used in the local stopping estimate. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

/-- The nine entries of the tree list L, with distinct recentered tags. -/
inductive LocalTree
  | J | V | W | Y | Z | XV | A | B | D
  deriving DecidableEq

instance : Fintype LocalTree :=
  ⟨{.J, .V, .W, .Y, .Z, .XV, .A, .B, .D}, by
    intro τ
    cases τ <;> simp⟩

instance : Nonempty LocalTree := ⟨.J⟩

/-- Number of noise leaves n_tau. -/
def LocalTree.leaves : LocalTree → ℕ
  | .J => 1 | .V => 2 | .W => 3 | .Y => 2 | .Z => 3
  | .XV => 2 | .A => 4 | .B => 4 | .D => 5

/-- The actual exponent in the smallness tests and the final tree roots. -/
def LocalTree.degree (κ : ℝ) (τ : LocalTree) : ℝ :=
  (τ.leaves : ℝ) * (1 / 2 - κ)

theorem LocalTree.leaves_pos (τ : LocalTree) : 0 < τ.leaves := by
  cases τ <;> norm_num [LocalTree.leaves]

theorem LocalTree.degree_pos {κ : ℝ} (hκ : κ < 1 / 2) (τ : LocalTree) :
    0 < τ.degree κ := by
  exact mul_pos (by exact_mod_cast τ.leaves_pos) (sub_pos.mpr hκ)

end GlobalPhi43.Local

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox

/-!
# The increment bound for the lattice approximations

Hairer (arXiv:1303.5113v4), (7.5): for a test function `ψ = φ^λ_x` with `x` in the time slab and
`64 λ ≤ w(x)`, and `8 · 2^{-n} ≤ λ`,
`|S_{n+1} f ψ - S_n f ψ| ≤ C K₀ C_f (2^{-n})^γ w(x)^{η-γ}`.
-/

public section

open Set
open scoped ContDiff

namespace RegularityStructures

private theorem parabolicNorm_sub_le_trans (a b c : ParabolicSpace) :
    parabolicNorm (a - c) ≤ parabolicNorm (a - b) + parabolicNorm (b - c) := by
  have : a - c = (a - b) + (b - c) := by abel
  rw [this]
  exact parabolicNorm_add_le _ _

/-- The cells meeting the support of `φ^λ_x` lie in a box around `x`. -/
theorem mem_latticeBox_of_rescaledTestFunction_mul_latticeCell_ne_zero {φ : ParabolicSpace → ℝ}
    (hφ : ∀ w, 1 < parabolicNorm w → φ w = 0) {lam : ℝ} (hlam : 0 < lam) {x : ParabolicSpace}
    {m : ℕ} (hm : 8 * ((2 : ℝ) ^ m)⁻¹ ≤ lam) {k : LatticeIndex} {w : ParabolicSpace}
    (h : rescaledTestFunction φ lam x w * latticeCell m k w ≠ 0) :
    k ∈ latticeBox m x ((2 * lam) ^ 2) (2 * lam) := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have hw : parabolicNorm (w - x) ≤ lam := by
    by_contra hc
    exact h1 (rescaledTestFunction_eq_zero hφ hlam (not_le.1 hc))
  refine mem_latticeBox_of_parabolicNorm_le ?_
  have := parabolicNorm_sub_le_trans (latticePoint m k) w x
  have e := parabolicNorm_sub_comm (latticePoint m k) w
  linarith [parabolicNorm_sub_latticePoint_le h2]

end RegularityStructures

end

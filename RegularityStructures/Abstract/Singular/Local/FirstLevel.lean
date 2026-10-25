/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Local.Increment
public import RegularityStructures.Abstract.RegularityStructure

/-!
# The first level of the lattice approximation

Hairer (arXiv:1303.5113v4), (7.3): for `ψ = φ^λ_x` with `x` in the time slab, `64 λ ≤ w(x)` and
`8 · 2^{-n} ≤ λ ≤ 16 · 2^{-n}`,
`|S_n f ψ - ⟨Π_x f(x), ψ⟩| ≤ C K₀ C_f λ^γ w(x)^{η-γ}`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑_{deg i < γ} 2^{γ - deg i} 2^{|deg i|}`. -/
def firstLevelSumConst (𝒯 : RegularityStructure ι) (γ : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
    (2 : ℝ) ^ (γ - 𝒯.deg i) * (2 : ℝ) ^ |𝒯.deg i|

end RegularityStructures

end

public section

open Set
open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem firstLevelSumConst_nonneg (𝒯 : RegularityStructure ι) (γ : ℝ) :
    0 ≤ firstLevelSumConst 𝒯 γ :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Cardinality of the box of level-`n` lattice points within `2 λ` of `x`, when
`2^n λ ≤ 16`. -/
theorem card_latticeBox_two_mul_le {n : ℕ} {x : ParabolicSpace} {lam : ℝ} (hlam : 0 < lam)
    (hu : (2 : ℝ) ^ n * lam ≤ 16) :
    ((latticeBox n x ((2 * lam) ^ 2) (2 * lam)).card : ℝ) ≤ 2050 * 66 ^ 3 := by
  have h := card_latticeBox_le (n := n) (x := x) (rt := (2 * lam) ^ 2) (rs := 2 * lam)
    (by positivity) (by positivity)
  have hu0 : (0 : ℝ) ≤ (2 : ℝ) ^ n * lam := by positivity
  have e1 : 2 * (4 : ℝ) ^ n * (2 * lam) ^ 2 = 8 * ((2 : ℝ) ^ n * lam) ^ 2 := by
    have : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
    rw [this]; ring
  have e2 : 2 * (2 : ℝ) ^ n * (2 * lam) = 4 * ((2 : ℝ) ^ n * lam) := by ring
  rw [e1, e2] at h
  refine h.trans ?_
  set u := (2 : ℝ) ^ n * lam
  have a1 : 8 * u ^ 2 + 2 ≤ 2050 := by nlinarith
  have a2 : 4 * u + 2 ≤ 66 := by linarith
  gcongr

end RegularityStructures

end

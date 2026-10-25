/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.LatticeApprox.Defs
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Local estimates for the lattice reconstruction of singular modelled distributions

Hairer (arXiv:1303.5113v4), Prop. 7.2 and (6.6), on the time slab: for `f` with
`SingularBoundOn timeZeroDist γ η Cf (timeSlab T)`, `x` in the slab and `ψ = φ^λ_x`
(`64 λ ≤ w(x)`, `ψ = 0` after time `T`):

* `exists_abs_latticeApprox_succ_sub_le`: increment bound (7.5);
* `exists_abs_latticeApprox_sub_pairing_le`: first level (7.3);
* `tendsto_latticeApprox_latticeRecon`: convergence of `S_n f ψ` to `⟨R f, ψ⟩`;
* `exists_abs_latticeRecon_sub_pairing_le`: the local bound (6.6).

These versions do not assume `0 ≤ C_f`: if some degree is below `γ`, then `0 ≤ C_f` follows from
the bound at `x`; otherwise `T_{<γ} = 0`, `f = 0` and all the quantities vanish.
-/

public section

open Set Filter
open scoped Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}

theorem pairing_regPi_zero (x : ParabolicSpace) (g : ParabolicSpace → ℝ) :
    parabolicSemigroup.pairing (M.regPi x 0) g = 0 := by
  have h : M.regPi x 0 = fun _ _ => 0 := by
    funext t y
    have := M.regPi_smul x 0 0 t y
    simpa using this
  rw [h]
  unfold RegularisingSemigroup.pairing
  simp only [zero_mul, MeasureTheory.integral_zero]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

theorem eq_zero_of_no_index (hno : ¬ ∃ i, 𝒯.deg i < γ) {f : ParabolicSpace → ι → ℝ}
    (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (z : ParabolicSpace) : f z = 0 := by
  funext i
  exact (mem_lowerSubspace).1 (hfT z) i (not_lt.1 fun h => hno ⟨i, h⟩)

theorem latticeApprox_eq_zero_of_no_index (hno : ¬ ∃ i, 𝒯.deg i < γ)
    {f : ParabolicSpace → ι → ℝ} (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (ψ : ParabolicSpace → ℝ) (n : ℕ) : M.latticeApprox f ψ n = 0 := by
  unfold latticeApprox
  simp only [eq_zero_of_no_index hno hfT, pairing_regPi_zero, finsum_zero]

theorem latticeRecon_eq_zero_of_no_index (hno : ¬ ∃ i, 𝒯.deg i < γ)
    {f : ParabolicSpace → ι → ℝ} (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (ψ : ParabolicSpace → ℝ) : M.latticeRecon f ψ = 0 := by
  unfold latticeRecon
  rw [show M.latticeApprox f ψ = fun _ => 0 from
    funext (latticeApprox_eq_zero_of_no_index M hno hfT ψ)]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

end RegularityStructures.Model

end

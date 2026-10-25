/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.ApproxPoly
public import RegularityStructures.Abstract.Polynomial.Model.Reg
public import RegularityStructures.Analysis.Parabolic.MomentBump

/-!
# Injectivity of `τ ↦ (Q_t Π_x τ)_{t>0}` on polynomials

A polynomial `(· - x)^τ` all of whose regularisations `Q_t (· - x)^τ`, `t > 0`, vanish is zero
(`polyReg_injective`): by the approximate identity (`PolyBounded.tendsto_apply_nhdsGT`) `polyEval x τ`
vanishes identically, so does its coefficient polynomial. Also `polyReg` is linear in `τ`
(`polyReg_eq_sum`). Input of [Hai14, Lemma 5.16].
-/

public section

open Filter
open scoped Topology

namespace RegularityStructures

variable {N : ℕ}

theorem polyReg_eq_sum (x : ParabolicSpace) (σ : PolyIndex N → ℝ) (t : ℝ) (z : ParabolicSpace) :
    polyReg x σ t z = ∑ k, σ k * polyReg x (Pi.single k 1) t z := by
  have h := map_sum (polyRegLin N x) (fun k => σ k • (Pi.single k 1 : PolyIndex N → ℝ))
    Finset.univ
  rw [← eq_sum_single σ] at h
  have h2 := congrArg (fun F : parabolicSemigroup.distributions =>
    (F : ℝ → ParabolicSpace → ℝ) t z) h
  simp only [polyRegLin_apply, Submodule.coe_sum, Finset.sum_apply, map_smul,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h2
  rw [h2]

/-- `polyEval x τ ≡ 0` forces `τ = 0`. -/
theorem eq_zero_of_polyEval_eq_zero (x : ParabolicSpace) {τ : PolyIndex N → ℝ}
    (h : ∀ z, polyEval x τ z = 0) : τ = 0 := by
  have hp : toPoly N τ = 0 := by
    refine eq_zero_of_evalParabolic_eq_zero_on_open (U := Set.univ) isOpen_univ
      Set.univ_nonempty fun z _ => ?_
    have := h (z + x)
    simpa [polyEval, evalParabolic] using this
  rw [← ofPoly_toPoly τ, hp, map_zero]

/-- Target 2: injectivity of `τ ↦ (Q_t (· - x)^τ)_{t>0}` on polynomial coefficient vectors. -/
theorem polyReg_injective (x : ParabolicSpace) {τ : PolyIndex N → ℝ}
    (h : ∀ t : ℝ, 0 < t → ∀ z, polyReg x τ t z = 0) : τ = 0 := by
  refine eq_zero_of_polyEval_eq_zero x fun z => ?_
  have hb : ∀ u, |polyEval x τ u| ≤
      ((∑ k, |τ k|) * (1 + parabolicNorm x) ^ N) * (1 + parabolicNorm u) ^ N := fun u =>
    (abs_polyEval_le x τ u).trans (le_of_eq (by ring))
  have ht := tendsto_apply_parabolicSemigroup_nhdsGT (continuous_polyEval x τ) hb z
  have h0 : Tendsto (fun s => parabolicSemigroup.apply s (polyEval x τ) z) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : (0 : ℝ) < s := hs
    rw [← polyReg_of_pos x τ hs]
    exact (h s hs z).symm
  exact tendsto_nhds_unique ht h0

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.Pieces
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Vanishing of the lattice reconstruction in the past

If `ψ` vanishes for `t ≥ 0` and the germ `f` vanishes for `t ≤ 0`, every lattice approximation
`S_n f ψ` is zero (cells are causal: `z_{n,k}` lies strictly before every point of the support of
`χ_{n,k}`), hence so is the reconstruction.
-/

public section

open Filter
open scoped Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup)

theorem regPi_zero (x : ParabolicSpace) (t : ℝ) (z : ParabolicSpace) :
    M.regPi x 0 t z = 0 := by
  have := M.regPi_smul x 0 (0 : ι → ℝ) t z
  simpa using this

theorem latticeApprox_eq_zero_of_causal {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ}
    (hψ : ∀ w : ParabolicSpace, 0 ≤ w.1 → ψ w = 0) (hf : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0)
    (n : ℕ) : M.latticeApprox f ψ n = 0 := by
  unfold latticeApprox
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  by_cases h : ∃ w, ψ w * latticeCell n k w ≠ 0
  · obtain ⟨w, hw⟩ := h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hw
    have hw0 : w.1 < 0 := by
      by_contra hc
      exact h1 (hψ w (not_lt.1 hc))
    have hp : (latticePoint n k).1 ≤ 0 := by
      have := (latticeCell_ne_zero h2).1.1
      linarith
    rw [hf _ hp]
    have : M.regPi (latticePoint n k) 0 = fun _ _ => 0 := by
      funext t z; exact M.regPi_zero _ t z
    rw [this]
    unfold RegularisingSemigroup.pairing
    simp only [zero_mul, MeasureTheory.integral_zero]
    exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq
  · push Not at h
    have : (fun w => ψ w * latticeCell n k w) = fun _ => 0 := funext h
    rw [this]
    exact pairing_zero_test _ _

theorem latticeRecon_eq_zero_of_causal {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ}
    (hψ : ∀ w : ParabolicSpace, 0 ≤ w.1 → ψ w = 0) (hf : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0) :
    M.latticeRecon f ψ = 0 := by
  unfold latticeRecon
  have : M.latticeApprox f ψ = fun _ => 0 := funext (M.latticeApprox_eq_zero_of_causal hψ hf)
  rw [this]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

end RegularityStructures.Model

end

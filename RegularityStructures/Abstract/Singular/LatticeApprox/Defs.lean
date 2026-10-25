/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.ModelPairing.Increment
public import RegularityStructures.Analysis.Parabolic.Lattice.Partition
public import RegularityStructures.Analysis.Parabolic.Lattice.Count
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Lattice approximation of the reconstruction of a singular modelled distribution

`S_n f ψ = ∑_k ⟨Π_{z_{n,k}} f(z_{n,k}), ψ χ_{n,k}⟩` with `χ_{n,k} = latticeCell n k` and
`⟨R f, ψ⟩ = lim_n S_n f ψ` (Hairer, arXiv:1303.5113v4, proof of Prop. 7.2, with a lattice
partition of unity instead of wavelets).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup)

/-- `S_n f ψ = ∑_k ⟨Π_{z_{n,k}} f(z_{n,k}), ψ χ_{n,k}⟩` (a finite sum for compactly supported `ψ`). -/
def latticeApprox (f : ParabolicSpace → ι → ℝ) (ψ : ParabolicSpace → ℝ) (n : ℕ) : ℝ :=
  ∑ᶠ k, parabolicSemigroup.pairing (M.regPi (latticePoint n k) (f (latticePoint n k)))
    (fun w => ψ w * latticeCell n k w)

/-- `⟨R f, ψ⟩ = lim_n S_n f ψ`. -/
def latticeRecon (f : ParabolicSpace → ι → ℝ) (ψ : ParabolicSpace → ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (M.latticeApprox f ψ)

end RegularityStructures.Model

end

public section

open Filter

namespace RegularityStructures

theorem pairing_zero_test {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
    (K : RegularisingSemigroup E μ) (Λ : ℝ → E → ℝ) : K.pairing Λ (fun _ => 0) = 0 := by
  unfold RegularisingSemigroup.pairing
  simp only [mul_zero, MeasureTheory.integral_zero]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup)

theorem latticeApprox_eq_sum {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ} {n : ℕ}
    {s : Finset LatticeIndex} (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) :
    M.latticeApprox f ψ n = ∑ k ∈ s, parabolicSemigroup.pairing
      (M.regPi (latticePoint n k) (f (latticePoint n k))) (fun w => ψ w * latticeCell n k w) := by
  unfold latticeApprox
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  by_contra hks
  refine hk ?_
  have : (fun w => ψ w * latticeCell n k w) = fun _ => 0 := by
    funext w
    by_contra h
    exact hks (hs k w h)
  simp only [this]
  exact pairing_zero_test _ _

/-- A cell index `k` with `ψ χ_{n,k} ≠ 0` for `ψ` supported in `B(x, R)` has its lattice point
within `R + 8 · 2^{-n}` of `x`. -/
theorem exists_finset_support_mul_latticeCell {ψ : ParabolicSpace → ℝ} {x : ParabolicSpace}
    {R : ℝ} (hψ : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (n : ℕ) :
    ∃ s : Finset LatticeIndex, ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s := by
  refine ⟨latticeBox n x ((R + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2) (R + 8 * ((2 : ℝ) ^ n)⁻¹), fun k w h => ?_⟩
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have hw : parabolicNorm (w - x) ≤ R := by
    by_contra hc; exact h1 (hψ w (not_le.1 hc))
  have hk := parabolicNorm_sub_latticePoint_le h2
  refine mem_latticeBox_of_parabolicNorm_le ?_
  have e : latticePoint n k - x = (w - x) + (latticePoint n k - w) := by abel
  rw [e]
  refine (parabolicNorm_add_le _ _).trans ?_
  rw [parabolicNorm_sub_comm (latticePoint n k)]
  linarith

end Model

end RegularityStructures

end

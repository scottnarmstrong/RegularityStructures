/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.Pieces
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Comparison of the lattice approximation with a single model vector (weighted model)

Weighted version, for a `Model.GrowthModel`.

For `τ ∈ T_{<γ}` and `ψ` supported in `B(x, R)`,
`S_n f ψ - ⟨Π_x τ, ψ⟩ = ∑_k ⟨Π_{z_{n,k}} (f(z_{n,k}) - Γ_{z_{n,k} x} τ), ψ χ_{n,k}⟩`
(Hairer, arXiv:1303.5113v4, proof of Prop. 7.2).
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- `⟨Π_x τ, ψ⟩ = ∑_k ⟨Π_x τ, ψ χ_{n,k}⟩` for `ψ` smooth supported in `B(x, R)`, `R ≤ 1`. -/
theorem pairing_regPi_eq_sum_latticeCell_growth {ψ : ParabolicSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {x : ParabolicSpace} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hsupp : ∀ w, R < parabolicNorm (w - x) → ψ w = 0)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {n : ℕ} {s : Finset LatticeIndex} (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) :
    parabolicSemigroup.pairing (M.regPi x τ) ψ =
      ∑ k ∈ s, parabolicSemigroup.pairing (M.regPi x τ) (fun w => ψ w * latticeCell n k w) := by
  have hc : ∀ k, ∃ A, IsScaledTest (fun w => ψ w * latticeCell n k w) x R A := fun k =>
    exists_isScaledTest (hψ.mul (contDiff_latticeCell n k)) hR hR1 fun w hw => by
      rw [hsupp w hw, zero_mul]
  have e : ψ = ∑ k ∈ s, fun w => ψ w * latticeCell n k w := by
    funext w
    rw [Finset.sum_apply]
    exact eq_sum_latticeCell_mul hs w (ψ w) id
  conv_lhs => rw [e]
  exact M.pairing_regPi_finset_sum_of_scaled_growth G hdeg hτ
    (fun k w => ψ w * latticeCell n k w) s (fun _ => R) (fun k => (hc k).choose)
    fun k _ => (hc k).choose_spec

theorem latticeApprox_sub_pairing_eq_growth {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    {x : ParabolicSpace} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hsupp : ∀ w, R < parabolicNorm (w - x) → ψ w = 0)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {n : ℕ} (hn : 3 ≤ n) {s : Finset LatticeIndex}
    (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) :
    M.latticeApprox f ψ n - parabolicSemigroup.pairing (M.regPi x τ) ψ =
      ∑ k ∈ s, parabolicSemigroup.pairing
        (M.regPi (latticePoint n k) (f (latticePoint n k) - M.gammaMap (latticePoint n k) x τ))
        (fun w => ψ w * latticeCell n k w) := by
  rw [M.pairing_regPi_eq_sum_latticeCell_growth hψ hR hR1 hsupp G hdeg hτ hs,
    M.latticeApprox_eq_sum hs, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hA : ∃ A, IsScaledTest (fun w => ψ w * latticeCell n k w) (latticePoint n k)
      (8 * ((2 : ℝ) ^ n)⁻¹) A :=
    exists_isScaledTest_of_latticeCell (hψ.mul (contDiff_latticeCell n k)) hn fun w h =>
      right_ne_zero_of_mul h
  have hΓ : M.gammaMap (latticePoint n k) x τ ∈ lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace hτ
  rw [M.pairing_regPi_eq_gammaMap x (latticePoint n k) τ,
    ← M.pairing_regPi_sub_of_scaled_growth G hdeg (hf _) hΓ hA.choose_spec]

end RegularityStructures.Model

end

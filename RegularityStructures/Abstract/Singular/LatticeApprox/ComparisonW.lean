/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.ComparisonG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Comparison of the lattice approximation with a single model vector (window setting)

Window version of `RegularityStructures.Abstract.Singular.LatticeApprox.ComparisonG`; identities
only, qualitative growth model.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}

theorem latticeApprox_sub_pairing_eq_win {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    {x : ParabolicSpace} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hsupp : ∀ w, R < parabolicNorm (w - x) → ψ w = 0)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {n : ℕ} (hn : 3 ≤ n) {s : Finset LatticeIndex}
    (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) :
    M.latticeApprox f ψ n - parabolicSemigroup.pairing (M.regPi x τ) ψ =
      ∑ k ∈ s, parabolicSemigroup.pairing
        (M.regPi (latticePoint n k) (f (latticePoint n k) - M.gammaMap (latticePoint n k) x τ))
        (fun w => ψ w * latticeCell n k w) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.latticeApprox_sub_pairing_eq_growth hψ hf hR hR1 hsupp G hdeg hτ hn hs

end RegularityStructures.Model

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.TelescopeG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Telescoping of the lattice approximations (window setting)

Window version of `RegularityStructures.Abstract.Singular.LatticeApprox.TelescopeG`: the identity
uses only the existence of the model pairings, hence only the *qualitative* growth model `hgrowth`
(no constant of it enters).
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}

theorem latticeApprox_succ_sub_eq_win {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {n : ℕ} (hn : 3 ≤ n)
    {s' s : Finset LatticeIndex}
    (hs' : ∀ k w, ψ w * latticeCell (n + 1) k w ≠ 0 → k ∈ s')
    (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) :
    M.latticeApprox f ψ (n + 1) - M.latticeApprox f ψ n =
      ∑ k ∈ s', ∑ l ∈ s, parabolicSemigroup.pairing
        (M.regPi (latticePoint (n + 1) k) (f (latticePoint (n + 1) k) -
          M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l))))
        (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  exact M.latticeApprox_succ_sub_eq_growth hψ hf G hdeg hn hs' hs

end RegularityStructures.Model

end

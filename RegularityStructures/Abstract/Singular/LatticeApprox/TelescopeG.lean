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
# Telescoping of the lattice approximations (weighted model)

Weighted version: the model bounds `PiBoundOn`, `GammaBoundOn` are
replaced by `Model.GrowthModel` (the identity itself needs only the existence of the pairings).

Hairer (arXiv:1303.5113v4, (7.4)-type identity): for smooth compactly supported `ψ`,
`S_{n+1} f ψ - S_n f ψ = ∑_k ∑_l ⟨Π_{z_{n+1,k}} (f(z_{n+1,k}) - Γ_{z_{n+1,k} z_{n,l}} f(z_{n,l})),
ψ χ_{n+1,k} χ_{n,l}⟩`.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

theorem latticeApprox_succ_sub_eq_growth {f : ParabolicSpace → ι → ℝ} {ψ : ParabolicSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {n : ℕ} (hn : 3 ≤ n)
    {s' s : Finset LatticeIndex}
    (hs' : ∀ k w, ψ w * latticeCell (n + 1) k w ≠ 0 → k ∈ s')
    (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) :
    M.latticeApprox f ψ (n + 1) - M.latticeApprox f ψ n =
      ∑ k ∈ s', ∑ l ∈ s, parabolicSemigroup.pairing
        (M.regPi (latticePoint (n + 1) k) (f (latticePoint (n + 1) k) -
          M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l))))
        (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) := by
  have hn1 : 3 ≤ n + 1 := by omega
  have hcd : ∀ k l, ContDiff ℝ ∞
      (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) := fun k l =>
    (hψ.mul (contDiff_latticeCell _ k)).mul (contDiff_latticeCell n l)
  -- scaled at the fine point
  have hA : ∀ k l, ∃ A, IsScaledTest (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w)
      (latticePoint (n + 1) k) (8 * ((2 : ℝ) ^ (n + 1))⁻¹) A := fun k l =>
    exists_isScaledTest_of_latticeCell (hcd k l) hn1 fun w h =>
      right_ne_zero_of_mul (left_ne_zero_of_mul h)
  -- scaled at the coarse point
  have hB : ∀ k l, ∃ A, IsScaledTest (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w)
      (latticePoint n l) (8 * ((2 : ℝ) ^ n)⁻¹) A := fun k l =>
    exists_isScaledTest_of_latticeCell (hcd k l) (by omega) fun w h => right_ne_zero_of_mul h
  have step1 : ∀ k, parabolicSemigroup.pairing
      (M.regPi (latticePoint (n + 1) k) (f (latticePoint (n + 1) k)))
        (fun w => ψ w * latticeCell (n + 1) k w) = ∑ l ∈ s, parabolicSemigroup.pairing
      (M.regPi (latticePoint (n + 1) k) (f (latticePoint (n + 1) k)))
        (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) := fun k => by
    have e : (fun w => ψ w * latticeCell (n + 1) k w) =
        ∑ l ∈ s, fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w := by
      funext w
      rw [Finset.sum_apply]
      exact eq_sum_latticeCell_mul hs w _ fun h => by simp [h]
    rw [e]
    exact M.pairing_regPi_finset_sum_of_scaled_growth G hdeg (hf _)
      (fun l w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) s
      (fun _ => 8 * ((2 : ℝ) ^ (n + 1))⁻¹) (fun l => (hA k l).choose)
      fun l _ => (hA k l).choose_spec
  have step2 : ∀ l, parabolicSemigroup.pairing
      (M.regPi (latticePoint n l) (f (latticePoint n l)))
        (fun w => ψ w * latticeCell n l w) = ∑ k ∈ s', parabolicSemigroup.pairing
      (M.regPi (latticePoint n l) (f (latticePoint n l)))
        (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) := fun l => by
    have e : (fun w => ψ w * latticeCell n l w) =
        ∑ k ∈ s', fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w := by
      funext w
      rw [Finset.sum_apply]
      rw [eq_sum_latticeCell_mul hs' w (ψ w * latticeCell n l w) fun h => by simp [h]]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact M.pairing_regPi_finset_sum_of_scaled_growth G hdeg (hf _)
      (fun k w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) s'
      (fun _ => 8 * ((2 : ℝ) ^ n)⁻¹) (fun k => (hB k l).choose)
      fun k _ => (hB k l).choose_spec
  rw [M.latticeApprox_eq_sum hs', M.latticeApprox_eq_sum hs]
  simp only [step1, step2]
  rw [Finset.sum_comm (s := s) (t := s'), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hΓ : M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l)) ∈
      lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace (hf _)
  rw [M.pairing_regPi_eq_gammaMap (latticePoint n l) (latticePoint (n + 1) k),
    ← M.pairing_regPi_sub_of_scaled_growth G hdeg (hf _) hΓ (hA k l).choose_spec]

end RegularityStructures.Model

end

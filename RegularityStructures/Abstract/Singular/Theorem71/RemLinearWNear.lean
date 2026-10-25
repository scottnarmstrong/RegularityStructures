/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.PairingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.LinearApproxG
public import RegularityStructures.Abstract.Singular.Remainder.Linear
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG

/-!
# Linearity of the remainder terms, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, the pairings `⟨R f, D^k r(z − ·)⟩` with the
derivatives of a remainder kernel `r` (`z₀ ≤ T`) and the remainder vector `remVecG` are additive and
homogeneous in `f`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ η α C₁ C₂ CPi CGam T : ℝ}
  {f f₁ f₂ : ParabolicSpace → ι → ℝ} {r : ParabolicSpace → ℝ}

private theorem cell_supp_win (ψ : ParabolicSpace → ℝ) (j : LatticeIndex) (w : ParabolicSpace)
    (hw : 1 < parabolicNorm (w - latticePoint 3 j)) : ψ w * latticeCell 3 j w = 0 := by
  rw [latticeCell_eq_zero_of_one_lt hw, mul_zero]

theorem remPairing_add_win_near (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T)
    (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T) (hr : RemKernel r)
    (k : Fin 4 →₀ ℕ) {z : ParabolicSpace} (hz : z.1 ≤ T) :
    M.remPairing (f₁ + f₂) (fun y => lineIter (multiDirs k) r (z - y)) =
      M.remPairing f₁ (fun y => lineIter (multiDirs k) r (z - y)) +
        M.remPairing f₂ (fun y => lineIter (multiDirs k) r (z - y)) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S₁.hgrowth
  set ψ : ParabolicSpace → ℝ := fun y => lineIter (multiDirs k) r (z - y) with hψ
  have r₁ := S₁.remSumm_lineIter_win hr k hz
  have r₂ := S₂.remSumm_lineIter_win hr k hz
  have hcell : ∀ j : LatticeIndex, M.latticeRecon (f₁ + f₂) (fun y => ψ y * latticeCell 3 j y) =
      M.latticeRecon f₁ (fun y => ψ y * latticeCell 3 j y) +
        M.latticeRecon f₂ (fun y => ψ y * latticeCell 3 j y) := fun j =>
    (M.latticeRecon_add_fun_growth S₁.hfT S₂.hfT G S₁.hdeg
      (r₁.contDiff.mul (contDiff_latticeCell 3 j)) (cell_supp_win ψ j) (r₁.tendsto j)
      (r₂.tendsto j)).2
  unfold remPairing
  simp only [hcell]
  exact r₁.summable.tsum_add r₂.summable

theorem remPairing_smul_win_near (S : LayerSettingWNear M f γ η α C₁ CPi CGam T)
    (hr : RemKernel r) (c : ℝ) (k : Fin 4 →₀ ℕ) {z : ParabolicSpace}
    (hz : z.1 ≤ T) :
    M.remPairing (c • f) (fun y => lineIter (multiDirs k) r (z - y)) =
      c * M.remPairing f (fun y => lineIter (multiDirs k) r (z - y)) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  set ψ : ParabolicSpace → ℝ := fun y => lineIter (multiDirs k) r (z - y) with hψ
  have r₁ := S.remSumm_lineIter_win hr k hz
  have hcell : ∀ j : LatticeIndex, M.latticeRecon (c • f) (fun y => ψ y * latticeCell 3 j y) =
      c * M.latticeRecon f (fun y => ψ y * latticeCell 3 j y) := fun j =>
    (M.latticeRecon_smul_fun_growth S.hfT G S.hdeg c
      (r₁.contDiff.mul (contDiff_latticeCell 3 j)) (cell_supp_win ψ j) (r₁.tendsto j)).2
  unfold remPairing
  simp only [hcell]
  exact tsum_mul_left

variable {N' : ℕ} {P : PolynomialSector 𝒯 N'}

theorem remVecG_add_win_near (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T)
    (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T) (hr : RemKernel r)
    {x : ParabolicSpace} (hx : x.1 ≤ T) :
    M.remVecG r P γ (f₁ + f₂) x = M.remVecG r P γ f₁ x + M.remVecG r P γ f₂ x := by
  classical
  unfold remVecG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun kk _ => ?_
  by_cases hk : polyDeg N' kk < γ + 2
  · simp only [hk, ite_true]
    rw [remPairing_add_win_near S₁ S₂ hr kk.1 hx, add_div, add_smul]
  · simp [hk]

theorem remVecG_smul_win_near (S : LayerSettingWNear M f γ η α C₁ CPi CGam T)
    (hr : RemKernel r) (c : ℝ) {x : ParabolicSpace} (hx : x.1 ≤ T) :
    M.remVecG r P γ (c • f) x = c • M.remVecG r P γ f x := by
  classical
  unfold remVecG
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun kk _ => ?_
  by_cases hk : polyDeg N' kk < γ + 2
  · simp only [hk, ite_true]
    rw [remPairing_smul_win_near S hr c kk.1 hx, smul_smul, mul_div_assoc]
  · simp [hk]

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullEntryMomentSub
public import Phi43.BPHZ.GammaFullEntryMoment
public import Phi43.BPHZ.GammaFullDet
import Mathlib.Tactic

/-!
# The deterministic `Γ`-entries of the canonical model at the full cutoff `γ = 1 + 3κ`

Let `Z = canonicalModelOfLift N κ C f` and `D_Γ^full = gammaFullDeterministic`. For all `i, j`
with `deg i < γ`, `deg j < deg i` and `(i, j) ∈ D_Γ^full`, and ALL `x, y : ParabolicSpace`,
`|Γ_{yx} e_i (j)| ≤ 1 · d(y, x)^(deg i - deg j)`
(`abs_gammaMap_entry_le_of_mem_gammaFullDeterministic`), and the entries of two such models agree
(`gammaMap_entry_eq_of_mem_gammaFullDeterministic`). These are the deterministic `Γ`-hypotheses
of the Kolmogorov bound for the model norms; the random entries `(i, j) ∉ D_Γ^full` are treated
through their parameters (`gammaShift_entry_lintegral_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {C : RenormalisationConstants} {f : SpaceTime → ℝ}

/-- The spatial shifts of `Γ_{yx}` are bounded by `d(y, x)`. -/
theorem abs_gammaFullParam_shift_le (hf : IsSmoothOnSpaceTime f) (y x : ParabolicSpace)
    (k : Fin 3) : |(gammaFullParam N κ C f y x).shift k.succ| ≤ parabolicSemigroup.scaleDist y x := by
  rw [gammaFullParam_shift hf, parabolicCoords_succ_eq, parabolicCoords_succ_eq]
  have h : y.2 k - x.2 k = (y - x).2 k := rfl
  rw [h]
  have := Finset.single_le_sum (f := fun j => |(y - x).2 j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ k)
  have h3 := Real.sqrt_nonneg |(y - x).1|
  change |(y - x).2 k| ≤ parabolicNorm (y - x)
  unfold parabolicNorm
  linarith

/-- **The deterministic `Γ`-entries of the canonical model.** -/
theorem abs_gammaMap_entry_le_of_mem_gammaFullDeterministic (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {i j : Symbol} (hp : (i, j) ∈ gammaFullDeterministic)
    (hlt : homogeneity κ j < homogeneity κ i) (y x : ParabolicSpace) :
    |(canonicalModelOfLift N κ C f).gammaMap y x (Pi.single i (1 : ℝ) : Symbol → ℝ) j| ≤
      1 * parabolicSemigroup.scaleDist y x ^ (homogeneity κ i - homogeneity κ j) := by
  rw [canonicalModelOfLift_gammaMap_single_apply hf hg]
  exact abs_structureGroupMap_entry_le_of_mem_gammaFullDeterministic κ _
    (parabolicSemigroup.scaleDist_nonneg y x) (abs_gammaFullParam_shift_le hf y x) hp hlt

/-- **The deterministic `Γ`-entries do not depend on the model.** -/
theorem gammaMap_entry_eq_of_mem_gammaFullDeterministic {f' : SpaceTime → ℝ}
    {C' : RenormalisationConstants} (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hf' : IsSmoothOnSpaceTime f') (hg' : Statements.HasPhi43NoiseGrowth f') {i j : Symbol}
    (hp : (i, j) ∈ gammaFullDeterministic) (hlt : homogeneity κ j < homogeneity κ i)
    (y x : ParabolicSpace) :
    (canonicalModelOfLift N κ C f).gammaMap y x (Pi.single i (1 : ℝ) : Symbol → ℝ) j =
      (canonicalModelOfLift N κ C' f').gammaMap y x (Pi.single i (1 : ℝ) : Symbol → ℝ) j := by
  have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hlt
  rw [canonicalModelOfLift_gammaMap_single_apply hf hg,
    canonicalModelOfLift_gammaMap_single_apply hf' hg']
  refine structureGroupMap_entry_eq_of_mem_gammaFullDeterministic _ _ (fun k => ?_) hp hne
  rw [gammaFullParam_shift hf, gammaFullParam_shift hf']

end RegularityStructures.Phi43

end

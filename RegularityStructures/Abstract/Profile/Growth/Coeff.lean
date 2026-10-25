/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Analysis.Shell
public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Integration.Sector.Coeff
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Coefficients of `J(x)` with polynomial growth, for a general shell profile

Weighted bound on the coefficients of `J(x)` for a general shell profile.  For a kernel
profile `h` (`ShellProfile h N`) and weighted model bounds (`Model.GrowthModel`),
`jCoeffP M h x i k = ∑_n ⟨Π_x e_i, D^k K_n(x − ·)⟩` converges absolutely and

  `|jCoeffP M h x i k| ≤ jCoeffConstInP 𝒯 V γ h i k · 2^{p+q} C_Π max(C_Γ, 1) ρΠ(x) ρΓ(x)`

for `|k|_𝔰 < deg i + 2`, `e_i ∈ V` (`abs_jCoeff_le_growthP`).

Source: [Hai14] = arXiv:1303.5113v4, (5.11), (5.16), proof of Theorem 5.12.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {V : Submodule ℝ (ι → ℝ)}

section J

variable (M : Model 𝒯 parabolicSemigroup) {h : ParabolicSpace → ℝ} {N : ℕ}
  (hh : ShellProfile h N) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
  (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (x : ParabolicSpace) (i : ι)
  (k : Fin 4 →₀ ℕ)

include hh G

theorem summable_jCoeff_terms_growthP (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) :
    Summable fun n : ℕ => parabolicSemigroup.pairing
      (fun t y => M.regPi x (Pi.single i 1) t y)
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) := by
  have hρx := G.moderateP.pos x
  have hρG := G.moderateG.pos x
  have hC : 0 ≤ max CGam 1 * CPi * Fintype.card ι * (ρP x * ρG x) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      G.piBound_nonneg) (Nat.cast_nonneg _)) (mul_nonneg hρx.le hρG.le)
  exact summable_pairing_lineIter_scaledShell_growth (M.regPi_mem x _)
    (fun _ hu => M.measurable_regPi x _ hu) hh.contDiff hh.eq_zero k
    (degreesBelowLeIn_bounds 𝒯 V hdeg i) hC
    (add_nonneg G.moderateP.nonneg_exp G.nonnegG)
    (M.isLocalOrderGrowth_regPi_single_in hV hVb G.moderateP G.moderateG.one_le G.nonnegG
      G.piBound G.gammaBound G.piBound_nonneg hVi hi x) hk

end J

end RegularityStructures

end

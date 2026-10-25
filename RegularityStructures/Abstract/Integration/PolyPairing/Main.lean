/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyPairing.Vanish
public import RegularityStructures.Abstract.Integration.PolyPairing.VanishShell
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Integration.Realising.RealisesKernel
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.DerivativePairing
public import RegularityStructures.Analysis.Semigroup.ConsistencyLimit

/-!
# The pairings `⟨Π_y X^l, D^k K_n(y - ·)⟩` vanish

For `K_n = annShell N n` (annihilating polynomials of degree `< N`) and a polynomial `X^l`,
`|l|_𝔰 < N' ≤ N`, the pairing `⟨Π_y X^l, D^k K_n(y - ·)⟩ = ∫ (w - y)^l D^k K_n(y - w) dw`
vanishes (`derivShellPairing_polyReg_eq_zero`); for a polynomially compatible model the same holds
for `Π_y e_{P.emb l}` (`derivShellPairing_regPi_emb_eq_zero`). This is why, in [Hai14, proof of
Theorem 5.12], the condition `|k|_𝔰 ≠ deg i + 2` is only needed for non-polynomial `i`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem derivShellPairing_polyReg_eq_zero {N N' : ℕ} (hN : N' ≤ N) (y : ParabolicSpace)
    (l : PolyIndex N') (k : Fin 4 →₀ ℕ) (n : ℕ) :
    derivShellPairing (polyReg y (Pi.single l 1)) (annKernel0 N) k y n = 0 := by
  unfold derivShellPairing
  set G := lineIter (multiDirs k) (scaledShell (annKernel0 N) n) with hG
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_lineIter (contDiff_scaledShell (contDiff_annKernel0 N) n) _
  have hGc : HasCompactSupport G :=
    hasCompactSupport_lineIter (hasCompactSupport_scaledShell
      (fun _ hz => annKernel0_eq_zero N hz) n) _
  have hb : ∀ u, |polyEval y (Pi.single l 1 : PolyIndex N' → ℝ) u| ≤
      ((∑ k, |(Pi.single l 1 : PolyIndex N' → ℝ) k|) * (1 + parabolicNorm y) ^ N') *
        (1 + parabolicNorm u) ^ N' := fun u =>
    (abs_polyEval_le y _ u).trans (le_of_eq (by ring))
  have hφ : Continuous (fun w => G (y - w)) :=
    hGs.continuous.comp (continuous_const.sub continuous_id)
  have hφc : HasCompactSupport (fun w => G (y - w)) :=
    hGc.comp_homeomorph (Homeomorph.subLeft y)
  rw [pairing_eq_integral_of_bound (continuous_polyEval y _) hb hφ hφc
    (Λ := polyReg y (Pi.single l 1)) (fun s hs => polyReg_of_pos y _ hs)]
  exact integral_polyEval_mul_lineIter_annShell hN n k y l

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem Model.derivShellPairing_regPi_emb_eq_zero {M : Model 𝒯 parabolicSemigroup}
    {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P) {N : ℕ} (hN : N' ≤ N)
    (y : ParabolicSpace) {i : ι} (hi : i ∈ Set.range P.emb) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n = 0 := by
  obtain ⟨l, rfl⟩ := hi
  have : (fun t z => M.regPi y (Pi.single (P.emb l) 1) t z) = polyReg y (Pi.single l 1) := by
    funext t z
    exact hM y l t z
  rw [this]
  exact derivShellPairing_polyReg_eq_zero hN y l k n

end RegularityStructures

end

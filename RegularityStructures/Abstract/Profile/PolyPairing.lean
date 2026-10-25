/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
public import RegularityStructures.Abstract.Integration.PolyPairing.Vanish
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.Derivative

/-!
# The pairings `⟨Π_y X^l, D^k K_n(y - ·)⟩` vanish, for a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.PolyPairing.Vanish`. For a
profile `h` with `ShellProfile h N` (vanishing moments of parabolic degree `< N`),
`K_n = scaledShell h n` and a polynomial `X^l`, `|l|_𝔰 < N' ≤ N`, the pairing
`⟨Π_y X^l, D^k K_n(y - ·)⟩ = ∫ (w - y)^l D^k K_n(y - w) dw` vanishes
(`derivShellPairing_polyReg_eq_zeroP`); for a polynomially compatible model the same holds for
`Π_y e_{P.emb l}` (`Model.derivShellPairing_regPi_emb_eq_zeroP`).

Source: [Hai14] = arXiv:1303.5113v4, proof of Theorem 5.12, (5.44)–(5.50).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

variable {h : ParabolicSpace → ℝ} {N : ℕ}

theorem integral_monoFn_mul_lineIter_shell_eq_zeroP (hh : ShellProfile h N) (n : ℕ)
    (k : Fin 4 →₀ ℕ) (l : Fin 4 → ℕ) (hl : fnWeight l < N) :
    ∫ z, monoFn l z * lineIter (multiDirs k) (scaledShell h n) z = 0 := by
  refine integral_monoFn_mul_lineIter_eq_zero_of_moments
    (contDiff_scaledShell hh.contDiff n) (hasCompactSupport_scaledShell hh.eq_zero n)
    (fun l' hl' => ?_) ((Finsupp.toMultiset k).toList) l hl
  have h1 := integral_monoFn_mul_scaledShell h (Finsupp.equivFunOnFinite.symm l') n
  have h2 := hh.moment
    ⟨Finsupp.equivFunOnFinite.symm l', by rw [fnWeight_equivFunOnFinite]; exact hl'⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm] at h1 h2
  rw [h1, h2, mul_zero]

/-- `∫ (w - y)^l D^k K_n(y - w) dw = 0` for `|l|_𝔰 < N`. -/
theorem integral_polyEval_mul_lineIter_shellP {N' : ℕ} (hh : ShellProfile h N) (hN : N' ≤ N)
    (n : ℕ) (k : Fin 4 →₀ ℕ) (y : ParabolicSpace) (l : PolyIndex N') :
    ∫ w, polyEval y (Pi.single l 1) w * lineIter (multiDirs k) (scaledShell h n) (y - w) = 0 := by
  have : (volume : Measure ParabolicSpace).IsAddHaarMeasure :=
    (inferInstance : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure)
  have hl : fnWeight (l.1 : Fin 4 → ℕ) < N := by
    have h1 := l.2
    rw [← fnWeight_equivFunOnFinite] at *
    have : (Finsupp.equivFunOnFinite.symm (l.1 : Fin 4 → ℕ)) = l.1 := by ext; rfl
    rw [this]; omega
  have hsub := integral_sub_left_eq_self
    (fun v => monoFn (l.1 : Fin 4 → ℕ) (-v) * lineIter (multiDirs k) (scaledShell h n) v) volume y
  simp only [neg_sub] at hsub
  have e : ∀ w, polyEval y (Pi.single l 1) w * lineIter (multiDirs k) (scaledShell h n) (y - w) =
      monoFn (l.1 : Fin 4 → ℕ) (w - y) * lineIter (multiDirs k) (scaledShell h n) (y - w) :=
    fun w => by rw [polyEval_single, evalParabolic_monomial_eq]
  simp_rw [e]
  rw [hsub]
  simp_rw [monoFn_neg, mul_assoc]
  rw [integral_const_mul, integral_monoFn_mul_lineIter_shell_eq_zeroP hh n k _ hl, mul_zero]

theorem derivShellPairing_polyReg_eq_zeroP {N' : ℕ} (hh : ShellProfile h N) (hN : N' ≤ N)
    (y : ParabolicSpace) (l : PolyIndex N') (k : Fin 4 →₀ ℕ) (n : ℕ) :
    derivShellPairing (polyReg y (Pi.single l 1)) h k y n = 0 := by
  unfold derivShellPairing
  set G := lineIter (multiDirs k) (scaledShell h n) with hG
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _
  have hGc : HasCompactSupport G :=
    hasCompactSupport_lineIter (hasCompactSupport_scaledShell hh.eq_zero n) _
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
  exact integral_polyEval_mul_lineIter_shellP hh hN n k y l

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem Model.derivShellPairing_regPi_emb_eq_zeroP {M : Model 𝒯 parabolicSemigroup}
    {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P) (hh : ShellProfile h N) (hN : N' ≤ N)
    (y : ParabolicSpace) {i : ι} (hi : i ∈ Set.range P.emb) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) h k y n = 0 := by
  obtain ⟨l, rfl⟩ := hi
  have : (fun t z => M.regPi y (Pi.single (P.emb l) 1) t z) = polyReg y (Pi.single l 1) := by
    funext t z
    exact hM y l t z
  rw [this]
  exact derivShellPairing_polyReg_eq_zeroP hh hN y l k n

end RegularityStructures

end

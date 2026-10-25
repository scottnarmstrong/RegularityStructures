/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.PolyPairing
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel
public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear

/-!
# Taylor-kernel pairings of polynomials vanish

For a shell profile `h` (`ShellProfile h N`) and a polynomial `P = ∑ σ_m (· - x)^m` of parabolic
degree `< N' ≤ N`, centred at an arbitrary point `x`:

* `integral_polyEval_mul_lineIter_shell_eq_zero`:
  `∫ P(w) D^k K_n(y - w) dw = 0` (the centre of `P` need not be `y`);
* `pairing_polyReg_taylorKernel_eq_zero`: `⟨Π_x P, K^r_{n;xy}⟩ = 0` for the Taylor kernel
  `K^r_{n;xy}` of every order `r`.

Hence the realising germ of a polynomial (`I X^k = 0`) vanishes (used for the instance on which the
`Φ⁴₃` fixed-point hypotheses are satisfiable). Source: [Hai14] = arXiv:1303.5113v4, (5.14), proof of
Theorem 5.12.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

variable {h : ParabolicSpace → ℝ} {N N' : ℕ}

theorem integral_polyEval_mul_lineIter_shell_eq_zero (hh : ShellProfile h N) (hN : N' ≤ N)
    (n : ℕ) (k : Fin 4 →₀ ℕ) (x y : ParabolicSpace) (σ : PolyIndex N' → ℝ) :
    ∫ w, polyEval x σ w * lineIter (multiDirs k) (scaledShell h n) (y - w) = 0 := by
  set G := lineIter (multiDirs k) (scaledShell h n) with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _
  have hGc : HasCompactSupport G :=
    hasCompactSupport_lineIter (hasCompactSupport_scaledShell hh.eq_zero n) _
  have hφ : Continuous (fun w => G (y - w)) :=
    hGs.continuous.comp (continuous_const.sub continuous_id)
  have hφc : HasCompactSupport (fun w => G (y - w)) :=
    hGc.comp_homeomorph (Homeomorph.subLeft y)
  have hint : ∀ τ : PolyIndex N' → ℝ, ∀ c : ParabolicSpace,
      Integrable fun w => polyEval c τ w * G (y - w) := fun τ c =>
    ((continuous_polyEval c τ).mul hφ).integrable_of_hasCompactSupport hφc.mul_left
  have hpt : ∀ w, polyEval x σ w = polyEval y (polyTranslate (parabolicCoords (y - x)) σ) w :=
    fun w => (polyEval_polyTranslate y x σ w).symm
  simp_rw [hpt]
  set σ' := polyTranslate (parabolicCoords (y - x)) σ with hσ'
  have hsum : ∀ w, polyEval y σ' w * G (y - w) =
      ∑ m, σ' m * (polyEval y (Pi.single m 1 : PolyIndex N' → ℝ) w * G (y - w)) := fun w => by
    rw [polyEval_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [polyEval_single, mul_assoc]
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun m _ => (hint (Pi.single m 1) y).const_mul _)]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [integral_const_mul, hG, integral_polyEval_mul_lineIter_shellP hh hN n k y m, mul_zero]

theorem pairing_polyReg_taylorKernel_eq_zero (hh : ShellProfile h N) (hN : N' ≤ N) (n : ℕ)
    (r : ℝ) (x y : ParabolicSpace) (σ : PolyIndex N' → ℝ) :
    parabolicSemigroup.pairing (polyReg x σ) (taylorKernel h n r x y) = 0 := by
  have hb : ∀ u, |polyEval x σ u| ≤
      ((∑ k, |σ k|) * (1 + parabolicNorm x) ^ N') * (1 + parabolicNorm u) ^ N' := fun u =>
    (abs_polyEval_le x σ u).trans (le_of_eq (by ring))
  have hφ := continuous_taylorKernel_right hh.contDiff n r x y
  have hφc := hasCompactSupport_taylorKernel hh.contDiff hh.eq_zero n r x y
  rw [pairing_eq_integral_of_bound (continuous_polyEval x σ) hb hφ hφc
    (Λ := polyReg x σ) (fun s hs => polyReg_of_pos x σ hs)]
  have hG : ∀ k : Fin 4 →₀ ℕ, Continuous fun w =>
      lineIter (multiDirs k) (scaledShell h n) (x - w) := fun k =>
    (contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _).continuous.comp
      (continuous_const.sub continuous_id)
  have hGc : ∀ k : Fin 4 →₀ ℕ, HasCompactSupport fun w =>
      lineIter (multiDirs k) (scaledShell h n) (x - w) := fun k =>
    (hasCompactSupport_lineIter (hasCompactSupport_scaledShell hh.eq_zero n) _).comp_homeomorph
      (Homeomorph.subLeft x)
  have hint : ∀ k : Fin 4 →₀ ℕ, Integrable fun w =>
      polyEval x σ w * lineIter (multiDirs k) (scaledShell h n) (x - w) := fun k =>
    ((continuous_polyEval x σ).mul (hG k)).integrable_of_hasCompactSupport (hGc k).mul_left
  have hK : Integrable fun w => polyEval x σ w * scaledShell h n (y - w) :=
    ((continuous_polyEval x σ).mul ((contDiff_scaledShell hh.contDiff n).continuous.comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((hasCompactSupport_scaledShell hh.eq_zero n).comp_homeomorph
        (Homeomorph.subLeft y)).mul_left
  have e : ∀ w, polyEval x σ w * taylorKernel h n r x y w =
      polyEval x σ w * scaledShell h n (y - w) - ∑ k ∈ taylorIdx r,
        (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
          (polyEval x σ w * lineIter (multiDirs k) (scaledShell h n) (x - w)) := fun w => by
    unfold taylorKernel
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_sub hK (integrable_finsetSum _ fun k _ => (hint k).const_mul _),
    integral_finsetSum _ fun k _ => (hint k).const_mul _]
  have h0 := integral_polyEval_mul_lineIter_shell_eq_zero hh hN n 0 x y σ
  simp only [multiDirs, Finsupp.toMultiset_zero, Multiset.toList_zero, List.map_nil,
    lineIter_nil] at h0
  rw [h0, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, integral_polyEval_mul_lineIter_shell_eq_zero hh hN n k x x σ, mul_zero]

end RegularityStructures

end

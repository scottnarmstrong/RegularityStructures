/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesTaylor
public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileDeriv

/-!
# The Taylor-remainder kernel at scale `n = 0`, and the bounds for all scales
At `n = 0` the kernel `K^{k,σ}_{0;yx}` lives in `B(x, 2)`, so it is not a scaled test function
(`radius ≤ 1` is required).  It is `w ↦ P_{y−x}(x − w)` for the Taylor profile `P` of
`G = D^k K` and satisfies `‖D^j ψ‖ ≤ C d^σ` for `j ≤ 4`, `d = ‖y − x‖ ≤ 1`.  The layer bound for
test functions supported in `B(x, 2)` and the model pairing bound for the kernel at scale `0`
give, for all scales `n ≥ 0`:
* `exists_abs_latticeRecon_dTaylor_all_le`: `|⟨R f, K^{k,σ}_{n;yx}⟩| ≤ C K₀ C_f d^σ (2^n)^{σ+|k|−2−α∧η}`;
* `exists_abs_pairing_dTaylor_all_le`: `|⟨Π_x e_i, K^{k,σ}_{n;yx}⟩| ≤ C K₀ d^σ (2^n)^{σ+|k|−2−deg i}`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

/-- The data of the Taylor kernel at scale `0`: smoothness, support in `B(x, 2)` and derivative
bounds `C d^σ`. -/
theorem exists_dTaylor_zero_data (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y : ParabolicSpace), 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ 1 →
      ContDiff ℝ ∞ (dTaylorKernel h k 0 σ x y) ∧
      (∀ w, 2 < parabolicNorm (w - x) → dTaylorKernel h k 0 σ x y w = 0) ∧
      ∀ j ≤ 4, ∀ w, ‖iteratedFDeriv ℝ j (dTaylorKernel h k 0 σ x y) w‖ ≤
        C * parabolicNorm (y - x) ^ σ := by
  have hcs : HasCompactSupport h :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun _ hz => hh.eq_zero _ (not_le.1 hz)
  have hGs : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter hh.contDiff _
  obtain ⟨C₁, hC₁, hb⟩ := exists_norm_iteratedFDeriv_taylorProfile_le hGs
    (hasCompactSupport_lineIter hcs _) hσ
  refine ⟨256 * (C₁ + 1), by positivity, fun x y hd hd1 => ?_⟩
  have e : dTaylorKernel h k 0 σ x y = fun w => taylorProfile (lineIter (multiDirs k) h) σ (y - x)
      (x + (-ContinuousLinearMap.id ℝ ParabolicSpace) w) := by
    funext w
    rw [dTaylorKernel_eq_profile hh.contDiff]
    simp [parabolicDilate_one, sub_eq_add_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (contDiff_taylorProfile hGs σ (y - x)).comp
      (contDiff_const.add (-ContinuousLinearMap.id ℝ ParabolicSpace).contDiff)
  · intro w hw
    refine dTaylorKernel_eq_zero hh.contDiff hh.eq_zero k 0 σ (x := x) (y := y) (w := w)
      (by simpa using hd1) (by simpa using hw)
  · intro j hj w
    have hn : ‖-ContinuousLinearMap.id ℝ ParabolicSpace‖ ≤ 4 := by
      rw [norm_neg]
      exact (ContinuousLinearMap.norm_id_le).trans (by norm_num)
    have hD : ∀ j ≤ 4, ∀ u, ‖iteratedFDeriv ℝ j (taylorProfile (lineIter (multiDirs k) h) σ
        (y - x)) u‖ ≤ (C₁ + 1) * parabolicNorm (y - x) ^ σ := fun j hj u =>
      (hb (y - x) hd1 j hj u).trans (by
        have := Real.rpow_nonneg (parabolicNorm_nonneg (y - x)) σ
        nlinarith)
    rw [e]
    have := norm_iteratedFDeriv_comp_affine_le (contDiff_taylorProfile hGs σ (y - x)) hD x
      (-ContinuousLinearMap.id ℝ ParabolicSpace) hn hj w
    exact this.trans (le_of_eq (by ring))

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Combinatorics
public import RegularityStructures.Abstract.Datum.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary inequalities for the Taylor remainder estimates

* `rpow_mul_rpow_le`: `ρ^{α - w} r^w ≤ ρ^{α - μ} r^μ` for `0 ≤ r ≤ ρ`, `0 ≤ μ ≤ w`;
* `abs_coord_le`: the coordinates of `w` satisfy `|w₀| ≤ ‖w‖_𝔰²` and `|wᵢ| ≤ ‖w‖_𝔰`, hence
  `∏ᵢ |cᵢ|^{kᵢ} ≤ ‖w‖_𝔰^{wt k}` (`prod_abs_coord_pow_le`);
* `rpow_half_le`: a bound `t^{(η - W)/2}` for `t ≥ ρ²` is a bound `ρ^{η - W}`.
-/

public section

open scoped ContDiff

namespace RegularityStructures.Datum

theorem rpow_mul_rpow_le {ρ r μ w : ℝ} (α : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r) (hrρ : r ≤ ρ)
    (hμ : 0 ≤ μ) (hw : μ ≤ w) : ρ ^ (α - w) * r ^ w ≤ ρ ^ (α - μ) * r ^ μ := by
  rcases hr.eq_or_lt with rfl | hr0
  · rcases hμ.eq_or_lt with rfl | hμ0
    · have : w = 0 ∨ 0 < w := by rcases hw.eq_or_lt with h | h <;> [left; right] <;> linarith
      rcases this with rfl | hw0
      · simp
      · rw [Real.zero_rpow hw0.ne']
        simpa using Real.rpow_nonneg hρ.le α
    · rw [Real.zero_rpow hμ0.ne', Real.zero_rpow (hμ0.trans_le hw).ne']
      simp
  · have h1 : ρ ^ (α - w) = ρ ^ (α - μ) * ρ ^ (μ - w) := by
      rw [← Real.rpow_add hρ]
      ring_nf
    have h2 : r ^ w = r ^ μ * r ^ (w - μ) := by
      rw [← Real.rpow_add hr0]
      ring_nf
    have h3 : ρ ^ (μ - w) * r ^ (w - μ) ≤ 1 := by
      have : ρ ^ (μ - w) = (ρ ^ (w - μ))⁻¹ := by
        rw [← Real.rpow_neg hρ.le]
        ring_nf
      rw [this, ← div_eq_inv_mul, ← Real.div_rpow hr hρ.le]
      exact Real.rpow_le_one (div_nonneg hr hρ.le) ((div_le_one hρ).2 hrρ) (by linarith)
    have hpos : 0 ≤ ρ ^ (α - μ) * r ^ μ :=
      mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg hr _)
    calc ρ ^ (α - w) * r ^ w
        = (ρ ^ (α - μ) * r ^ μ) * (ρ ^ (μ - w) * r ^ (w - μ)) := by rw [h1, h2]; ring
      _ ≤ (ρ ^ (α - μ) * r ^ μ) * 1 := mul_le_mul_of_nonneg_left h3 hpos
      _ = _ := mul_one _

theorem abs_fst_le_parabolicNorm_sq (w : ParabolicSpace) : |w.1| ≤ parabolicNorm w ^ 2 := by
  have h : Real.sqrt |w.1| ≤ parabolicNorm w :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  calc |w.1| = Real.sqrt |w.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ parabolicNorm w ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem abs_snd_le_parabolicNorm (w : ParabolicSpace) (j : Fin 3) : |w.2 j| ≤ parabolicNorm w := by
  have h : |w.2 j| ≤ ∑ i, |w.2 i| :=
    Finset.single_le_sum (f := fun i => |w.2 i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  exact h.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

theorem prod_abs_coord_pow_le (w : ParabolicSpace) (k : Fin 4 → ℕ) :
    ∏ i, |parabolicCoords w i| ^ k i ≤ parabolicNorm w ^ wt k := by
  have h0 : |parabolicCoords w 0| ≤ parabolicNorm w ^ 2 := abs_fst_le_parabolicNorm_sq w
  have h1 : ∀ j : Fin 3, |parabolicCoords w j.succ| ≤ parabolicNorm w := fun j => by
    have := abs_snd_le_parabolicNorm w j
    fin_cases j <;> simpa [parabolicCoords] using this
  have hr := parabolicNorm_nonneg w
  rw [Fin.prod_univ_four]
  have e0 : |parabolicCoords w 0| ^ k 0 ≤ parabolicNorm w ^ (2 * k 0) := by
    calc |parabolicCoords w 0| ^ k 0 ≤ (parabolicNorm w ^ 2) ^ k 0 :=
          pow_le_pow_left₀ (abs_nonneg _) h0 _
      _ = parabolicNorm w ^ (2 * k 0) := by rw [← pow_mul]
  have e1 : |parabolicCoords w 1| ^ k 1 ≤ parabolicNorm w ^ k 1 :=
    pow_le_pow_left₀ (abs_nonneg _) (h1 0) _
  have e2 : |parabolicCoords w 2| ^ k 2 ≤ parabolicNorm w ^ k 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (h1 1) _
  have e3 : |parabolicCoords w 3| ^ k 3 ≤ parabolicNorm w ^ k 3 :=
    pow_le_pow_left₀ (abs_nonneg _) (h1 2) _
  have n0 : 0 ≤ |parabolicCoords w 0| ^ k 0 := by positivity
  have n1 : 0 ≤ |parabolicCoords w 1| ^ k 1 := by positivity
  have n2 : 0 ≤ |parabolicCoords w 2| ^ k 2 := by positivity
  have n3 : 0 ≤ |parabolicCoords w 3| ^ k 3 := by positivity
  calc _ ≤ parabolicNorm w ^ (2 * k 0) * parabolicNorm w ^ k 1 * parabolicNorm w ^ k 2 *
        parabolicNorm w ^ k 3 :=
        mul_le_mul (mul_le_mul (mul_le_mul e0 e1 n1 (by positivity)) e2 n2 (by positivity)) e3 n3
          (by positivity)
    _ = parabolicNorm w ^ wt k := by
        rw [← pow_add, ← pow_add, ← pow_add]
        rfl

theorem rpow_half_le {t ρ e : ℝ} (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ t) (he : e ≤ 0) :
    t ^ (e / 2) ≤ ρ ^ e := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have h1 : t ^ (e / 2) ≤ (ρ ^ 2) ^ (e / 2) :=
    Real.rpow_le_rpow_of_nonpos hρ2 ht (by linarith)
  have h2 : (ρ ^ 2) ^ (e / 2) = ρ ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    congr 1
    push_cast
    ring
  rw [← h2]
  exact h1

end RegularityStructures.Datum

end

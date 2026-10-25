/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovLp
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The dyadic Kolmogorov reduction for the negative-order torus norm

The dyadic reduction is the deterministic part of the Kolmogorov argument.  It uses the
semigroup contraction on `C(T³)` and the scale decomposition of `(0, 1]`; compare Hairer
[Hai14, (2.1)--(2.3)].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

open PDE

/-- The dyadic scale `2⁻ⁿ`, written with natural powers to avoid logarithms. -/
def dyadicScale (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ n

theorem dyadicScale_pos (n : ℕ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

theorem dyadicScale_le_one (n : ℕ) : dyadicScale n ≤ 1 := by
  unfold dyadicScale
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  simpa using one_div_le_one_div_of_le (by norm_num) hp

theorem dyadicScale_succ (n : ℕ) : dyadicScale (n + 1) = dyadicScale n / 2 := by
  unfold dyadicScale
  rw [pow_succ]
  field_simp

theorem exists_mem_dyadicBlock {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ n : ℕ, s ∈ Ioc (dyadicScale (n + 1)) (dyadicScale n) := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (one_le_one_div hs hs1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_, ?_⟩
  · have h := (one_div_lt_one_div (by positivity : 0 < (2 : ℝ) ^ (n + 1))
        (by positivity : 0 < 1 / s)).2 hn'
    simpa [dyadicScale, one_div] using h
  · simpa [dyadicScale] using
      (le_one_div hs (by positivity : 0 < (2 : ℝ) ^ n)).2 hn

theorem heatSemigroup_sup_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (f : C(Torus3, ℝ)) :
    ⨆ x : Torus3, ‖heatSemigroup s f x‖ₑ ≤
      ⨆ x : Torus3, ‖heatSemigroup r f x‖ₑ := by
  have hpoint : ∀ x : Torus3,
      ‖heatSemigroup s f x‖ₑ ≤ ⨆ y : Torus3, ‖heatSemigroup r f y‖ₑ := by
    intro x
    have hs : 0 < s := hr.trans_le hrs
    have hdiff : 0 ≤ s - r := sub_nonneg.mpr hrs
    have hdecomp : heatOp (s - r) (heatOp r f) = heatOp s f := by
      rw [heatOp_heatOp hr.le hdiff]
      congr 1
      ring
    calc
      ‖heatSemigroup s f x‖ₑ = ‖heatOp s f x‖ₑ := by
        rw [heatOp_eq_heatSemigroup hs]
      _ = ‖heatOp (s - r) (heatOp r f) x‖ₑ := by rw [hdecomp]
      _ ≤ ‖heatOp r f‖ₑ := by
        apply enorm_le_iff_norm_le.2
        exact norm_heatOp_apply_le (s - r) (heatOp r f) x
      _ = ⨆ y : Torus3, ‖heatOp r f y‖ₑ := ContinuousMap.enorm_eq_iSup_enorm _
      _ = ⨆ y : Torus3, ‖heatSemigroup r f y‖ₑ := by
        apply iSup_congr
        intro y
        rw [heatOp_eq_heatSemigroup hr]
  exact iSup_le hpoint

theorem holderBesovENorm_le_dyadic_iSup {η : ℝ} (hη : η ≤ 0)
    (f : C(Torus3, ℝ)) :
    holderBesovENorm η f ≤
      ⨆ n : ℕ,
        ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ := by
  refine iSup₂_le fun s hs => ?_
  obtain ⟨n, hn⟩ := exists_mem_dyadicBlock hs.1 hs.2
  have hβ : 0 ≤ -η / 2 := by linarith
  have hweight : s ^ (-η / 2) ≤ (dyadicScale n) ^ (-η / 2) := by
    exact Real.rpow_le_rpow hs.1.le hn.2 hβ
  have hsup := heatSemigroup_sup_le
    (dyadicScale_pos (n + 1)) hn.1.le (f := f)
  calc
    ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x : Torus3, ‖heatSemigroup s f x‖ₑ ≤
        ENNReal.ofReal (s ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ := by
      gcongr
    _ ≤ ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ := by
      gcongr
    _ ≤ ⨆ n : ℕ,
        ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
          ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ :=
      le_iSup (fun n : ℕ => ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
        ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ) n

end RegularityStructures

end

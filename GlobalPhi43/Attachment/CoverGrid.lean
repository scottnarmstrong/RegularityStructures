module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! The literal half-open spatial grid and its closed-cube covering, including x=1. -/

public noncomputable section

open Set RegularityStructures

namespace GlobalPhi43.Attachment

/-- Grid centres in (lambda/2) Z^3 intersected with [0,1)^3. -/
@[expose] def coverGrid (lam : ℝ) : Set (Fin 3 → ℝ) :=
  {y | (∃ k : Fin 3 → ℤ, ∀ i, y i = (lam / 2) * (k i : ℝ)) ∧ ∀ i, y i ∈ Ico (0 : ℝ) 1}

/-- Choosing ceil(x/a)-1 for x>0 keeps the centre strictly below one even at x=1. -/
theorem exists_grid_coordinate {a x : ℝ} (ha : 0 < a) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℤ, 0 ≤ a * (k : ℝ) ∧ a * (k : ℝ) < 1 ∧ |x - a * (k : ℝ)| ≤ a := by
  by_cases hzero : x = 0
  · subst x
    exact ⟨0, by norm_num, by norm_num, by simpa using ha.le⟩
  have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
  let k : ℤ := ⌈x / a⌉ - 1
  have hc : 0 < (⌈x / a⌉ : ℤ) := Int.ceil_pos.mpr (div_pos hpos ha)
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hceil := Int.le_ceil (x / a)
  have hstrict := Int.ceil_lt_add_one (x / a)
  have he : (k : ℝ) = (⌈x / a⌉ : ℝ) - 1 := by simp only [k, Int.cast_sub, Int.cast_one]
  have hlo : a * (k : ℝ) < x := by
    rw [he]
    have hh := (mul_lt_mul_of_pos_left hstrict ha)
    have hdiv : a * (x / a) = x := mul_div_cancel₀ x ha.ne'
    nlinarith
  have hupper : x ≤ a * (k : ℝ) + a := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hceil ha.le
    have hdiv : a * (x / a) = x := mul_div_cancel₀ x ha.ne'
    nlinarith
  refine ⟨k, mul_nonneg ha.le (by exact_mod_cast hk), hlo.trans_le hx.2, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hlo.le)]
  linarith

/-- The closed cubes cover the whole closed fundamental cell, not merely [0,1)^3. -/
theorem exists_coverGrid_point {lam : ℝ} (hlam : 0 < lam) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    ∃ y ∈ coverGrid lam, ∀ i, |x i - y i| ≤ lam / 2 := by
  choose k hk0 hk1 hkdist using fun i => exists_grid_coordinate (half_pos hlam) (hx i)
  refine ⟨fun i => (lam / 2) * (k i : ℝ), ⟨⟨k, fun _ => rfl⟩, fun i => ⟨hk0 i, hk1 i⟩⟩,
    hkdist⟩

end GlobalPhi43.Attachment

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Abstract.Singular.Local.Weight

/-!
# Elementary facts for the series bound of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`
* `SlabPair`: a close pair of points `x, y` of the time slab, `0 < d = ‖y − x‖_𝔰`,
  `64 d ≤ W = min (‖x‖_P, ‖y‖_P)`; the weights are comparable (`W ≤ ‖x‖_P, ‖y‖_P ≤ 2 W`);
* real-variable lemmas: the scale identity `d^a u^p = d^{a−p} (u d)^p`, the weight comparison
  `w^e ≤ 2^{|e|} W^e`, monotonicity of `s^e` on either side of `s = 1`;
* the coordinates of `τ = f(y) − Γ_{yx} f(x)`: `|τ_i| ≤ C_f d^{γ−deg i} W^{η−γ}`, and the support of `τ`.
-/

public section

open Set

namespace RegularityStructures

/-- A close pair of points of the time slab: `0 < d = ‖y − x‖_𝔰` and `64 d ≤ W`, `W` the smaller
of the two singular weights. -/
structure SlabPair (T : ℝ) (x y : ParabolicSpace) : Prop where
  hx : x ∈ timeSlab T
  hy : y ∈ timeSlab T
  hd : 0 < parabolicNorm (y - x)
  hW : 64 * parabolicNorm (y - x) ≤
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y)

namespace SlabPair

variable {T : ℝ} {x y : ParabolicSpace}

theorem weight_x_pos (P : SlabPair T x y) : 0 < singularWeight timeZeroDist x :=
  KGammaSup.weight_pos P.hx

theorem weight_y_pos (P : SlabPair T x y) : 0 < singularWeight timeZeroDist y :=
  KGammaSup.weight_pos P.hy

theorem W_pos (P : SlabPair T x y) :
    0 < min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) :=
  lt_min P.weight_x_pos P.weight_y_pos

theorem W_le_one (_P : SlabPair T x y) :
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤ 1 :=
  (min_le_left _ _).trans (singularWeight_le_one _ _)

theorem W_le_x (_P : SlabPair T x y) :
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤
      singularWeight timeZeroDist x := min_le_left _ _

theorem W_le_y (_P : SlabPair T x y) :
    min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤
      singularWeight timeZeroDist y := min_le_right _ _

theorem d_le_W (P : SlabPair T x y) :
    parabolicNorm (y - x) ≤ min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) := by
  have := P.hW; have := P.hd; linarith

theorem x_le_two_W (P : SlabPair T x y) :
    singularWeight timeZeroDist x ≤
      2 * min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) := by
  have h := abs_singularWeight_timeZeroDist_sub_le x y
  rw [parabolicNorm_sub_comm] at h
  have hdx := le_min_iff.1 P.d_le_W
  have := abs_le.1 h
  rcases le_total (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with h1 | h1
  · rw [min_eq_left h1]; linarith [P.weight_x_pos]
  · rw [min_eq_right h1]; linarith [hdx.1, hdx.2]

theorem y_le_two_W (P : SlabPair T x y) :
    singularWeight timeZeroDist y ≤
      2 * min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) := by
  have h := abs_singularWeight_timeZeroDist_sub_le x y
  rw [parabolicNorm_sub_comm] at h
  have hdx := le_min_iff.1 P.d_le_W
  have := abs_le.1 h
  rcases le_total (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with h1 | h1
  · rw [min_eq_left h1]; linarith [hdx.1, hdx.2]
  · rw [min_eq_right h1]; linarith [P.weight_y_pos]

end SlabPair

/-- The scale identity `d^a u^p = d^{a−p} (u d)^p`. -/
theorem rpow_mul_rpow_scale {d u : ℝ} (hd : 0 < d) (hu : 0 < u) (a p : ℝ) :
    d ^ a * u ^ p = d ^ (a - p) * (u * d) ^ p := by
  rw [Real.rpow_sub hd, Real.mul_rpow hu.le hd.le]
  have : d ^ p ≠ 0 := (Real.rpow_pos_of_pos hd p).ne'
  field_simp

/-- Comparison of a weight `w ∈ [W, 2W]` with `W`: `w^e ≤ 2^{|e|} W^e`. -/
theorem rpow_weight_le {W w : ℝ} (hW : 0 < W) (h1 : W ≤ w) (h2 : w ≤ 2 * W) (e : ℝ) :
    w ^ e ≤ 2 ^ |e| * W ^ e := by
  have h2e : (1 : ℝ) ≤ 2 ^ |e| := Real.one_le_rpow (by norm_num) (abs_nonneg e)
  have hWe : 0 ≤ W ^ e := Real.rpow_nonneg hW.le e
  rcases le_total 0 e with he | he
  · calc w ^ e ≤ (2 * W) ^ e := Real.rpow_le_rpow (hW.le.trans h1) h2 he
      _ = 2 ^ e * W ^ e := Real.mul_rpow (by norm_num) hW.le
      _ ≤ 2 ^ |e| * W ^ e := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self e)) hWe
  · calc w ^ e ≤ W ^ e := Real.rpow_le_rpow_of_nonpos hW h1 he
      _ ≤ 2 ^ |e| * W ^ e := le_mul_of_one_le_left hWe h2e

theorem rpow_neg_le_of_one_le {s b e : ℝ} (hs : 1 ≤ s) (hb : b ≤ e) : s ^ (-e) ≤ s ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg hb)

theorem rpow_le_of_le_one {s a e : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (ha : a ≤ e) :
    s ^ e ≤ s ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hs0 hs1 ha

/-- A common positive lower bound for finitely many positive reals. -/
theorem exists_pos_le_finset {κ : Type*} (S : Finset κ) (g : κ → ℝ) (hg : ∀ i ∈ S, 0 < g i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ ≤ g i := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S g hne
    exact ⟨g j, hg j hj, hmin⟩
  · exact ⟨1, one_pos, fun i hi => absurd ⟨i, hi⟩ hne⟩

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The three scale regimes for one term of the sup bound

For one scale `n` put `t = 2^n w` (`w = ‖x‖_P`).  The term `T` of the sum for the `X^k` coefficient
of `𝒦_γ f(x)` has two expressions: `T = S + ∑_{i ∈ P₊} J_i` (the singular part plus the `J`-terms
with `|k| < deg i + 2`; useful for `t ≥ 64`) and `T = R − ∑_{i ∈ P₋} J_i` (the reconstruction minus
the `J`-terms with `deg i + 2 < |k|`; useful for `t < 64`).  If the pieces obey the bounds
`R ≲ t^{e₁}` (always), `R ≲ t^{a_R}` (for `t < 1`, from the time-Taylor remainder),
`S ≲ t^{-b}` (`t ≥ 64`), `J_i ≲ t^{e_i}` with `e_i ≤ -b` on `P₊` and `e_i ≥ a` on `P₋`, then
`|T| ≲ min (t^a) (t^{-b})`.
-/

public section

open Finset

namespace RegularityStructures.KGammaSup

theorem rpow_le_rpow_of_le_one {t a e : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (h : a ≤ e) :
    t ^ e ≤ t ^ a :=
  Real.rpow_le_rpow_of_exponent_ge ht0 ht1 h

theorem rpow_le_rpow_of_one_le {t a e : ℝ} (ht1 : 1 ≤ t) (h : e ≤ a) : t ^ e ≤ t ^ a :=
  Real.rpow_le_rpow_of_exponent_le ht1 h

/-- For `1 ≤ t ≤ 64`, `t^e ≤ 64^{|e|}`. -/
theorem rpow_le_sixtyFour_abs {t e : ℝ} (ht1 : 1 ≤ t) (ht : t ≤ 64) :
    t ^ e ≤ (64 : ℝ) ^ |e| :=
  calc t ^ e ≤ t ^ |e| := rpow_le_rpow_of_one_le ht1 (le_abs_self e)
    _ ≤ 64 ^ |e| := Real.rpow_le_rpow (by linarith) ht (abs_nonneg e)

theorem min_rpow_eq_of_le_one {t a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    min (t ^ a) (t ^ (-b)) = t ^ a :=
  min_eq_left ((rpow_le_rpow_of_le_one ht0 ht1 (by linarith : -b ≤ a)))

theorem min_rpow_eq_of_one_le {t a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ht1 : 1 ≤ t) :
    min (t ^ a) (t ^ (-b)) = t ^ (-b) :=
  min_eq_right (rpow_le_rpow_of_one_le ht1 (by linarith : -b ≤ a))

/-- The combination of the three regimes. -/
theorem abs_le_mul_min_of_pieces {κ : Type*} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (e : κ → ℝ) (Pp Pm : Finset κ) (hPp : ∀ i ∈ Pp, e i ≤ -b) (hPm : ∀ i ∈ Pm, a ≤ e i)
    {t Bc e₁ aR : ℝ} (ht : 0 < t) (hBc : 0 ≤ Bc) (haR : a ≤ aR)
    {R S T : ℝ} (J : κ → ℝ)
    (hT1 : T = S + ∑ i ∈ Pp, J i) (hT2 : T = R - ∑ i ∈ Pm, J i)
    (hR : |R| ≤ Bc * t ^ e₁) (hRs : t < 1 → |R| ≤ Bc * t ^ aR)
    (hS : 64 ≤ t → |S| ≤ Bc * t ^ (-b))
    (hJp : ∀ i ∈ Pp, |J i| ≤ Bc * t ^ e i) (hJm : ∀ i ∈ Pm, |J i| ≤ Bc * t ^ e i) :
    |T| ≤ Bc * ((1 + Pp.card + Pm.card) * 64 ^ (|e₁| + ∑ i ∈ Pm, |e i| + b)) *
      min (t ^ a) (t ^ (-b)) := by
  have hcard : (1 : ℝ) ≤ 1 + Pp.card + Pm.card := by
    have : (0 : ℝ) ≤ Pp.card + Pm.card := by positivity
    linarith
  have hP64 : (1 : ℝ) ≤ 64 ^ (|e₁| + ∑ i ∈ Pm, |e i| + b) :=
    Real.one_le_rpow (by norm_num) (by
      have : 0 ≤ ∑ i ∈ Pm, |e i| := sum_nonneg fun i _ => abs_nonneg _
      have := abs_nonneg e₁
      linarith)
  rcases lt_or_ge t 1 with h1 | h1
  · -- small `t`: `T = R - ∑_{Pm} J`
    rw [min_rpow_eq_of_le_one ha hb ht h1.le]
    have hR' : |R| ≤ Bc * t ^ a := (hRs h1).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_le_one ht h1.le haR) hBc)
    have hJ' : ∀ i ∈ Pm, |J i| ≤ Bc * t ^ a := fun i hi => (hJm i hi).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_le_one ht h1.le (hPm i hi)) hBc)
    have : |T| ≤ Bc * t ^ a * (1 + Pm.card) := by
      rw [hT2]
      calc |R - ∑ i ∈ Pm, J i| ≤ |R| + |∑ i ∈ Pm, J i| := abs_sub _ _
        _ ≤ Bc * t ^ a + ∑ i ∈ Pm, |J i| := add_le_add hR' (abs_sum_le_sum_abs _ _)
        _ ≤ Bc * t ^ a + ∑ _i ∈ Pm, Bc * t ^ a := add_le_add le_rfl (sum_le_sum hJ')
        _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
    refine this.trans ?_
    have hta : 0 ≤ Bc * t ^ a := mul_nonneg hBc (Real.rpow_nonneg ht.le _)
    have h2 : (1 + (Pm.card : ℝ)) ≤ (1 + Pp.card + Pm.card) * 64 ^ (|e₁| + ∑ i ∈ Pm, |e i| + b) := by
      have : (0 : ℝ) ≤ Pp.card := by positivity
      nlinarith
    calc Bc * t ^ a * (1 + Pm.card) ≤ Bc * t ^ a * ((1 + Pp.card + Pm.card) *
          64 ^ (|e₁| + ∑ i ∈ Pm, |e i| + b)) := mul_le_mul_of_nonneg_left h2 hta
      _ = _ := by ring
  · rw [min_rpow_eq_of_one_le ha hb h1]
    rcases lt_or_ge t 64 with h64 | h64
    · -- middle regime: `T = R - ∑_{Pm} J`, everything is `≲ Bc`
      set E₀ : ℝ := |e₁| + ∑ i ∈ Pm, |e i| with hE₀
      have hE₁ : |e₁| ≤ E₀ := by
        have : 0 ≤ ∑ i ∈ Pm, |e i| := sum_nonneg fun i _ => abs_nonneg _
        linarith
      have hEi : ∀ i ∈ Pm, |e i| ≤ E₀ := fun i hi => by
        have : |e i| ≤ ∑ j ∈ Pm, |e j| :=
          single_le_sum (f := fun j => |e j|) (fun j _ => abs_nonneg _) hi
        have := abs_nonneg e₁
        linarith
      have h64E : ∀ q : ℝ, |q| ≤ E₀ → t ^ q ≤ 64 ^ E₀ := fun q hq =>
        (rpow_le_sixtyFour_abs h1 h64.le).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq)
      have hR' : |R| ≤ Bc * 64 ^ E₀ :=
        hR.trans (mul_le_mul_of_nonneg_left (h64E e₁ hE₁) hBc)
      have hJ' : ∀ i ∈ Pm, |J i| ≤ Bc * 64 ^ E₀ := fun i hi => (hJm i hi).trans
        (mul_le_mul_of_nonneg_left (h64E (e i) (hEi i hi)) hBc)
      have h1' : |T| ≤ Bc * 64 ^ E₀ * (1 + Pm.card) := by
        rw [hT2]
        calc |R - ∑ i ∈ Pm, J i| ≤ |R| + |∑ i ∈ Pm, J i| := abs_sub _ _
          _ ≤ Bc * 64 ^ E₀ + ∑ i ∈ Pm, |J i| := add_le_add hR' (abs_sum_le_sum_abs _ _)
          _ ≤ Bc * 64 ^ E₀ + ∑ _i ∈ Pm, Bc * 64 ^ E₀ := add_le_add le_rfl (sum_le_sum hJ')
          _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
      refine h1'.trans ?_
      have hb64 : (1 : ℝ) ≤ 64 ^ b * t ^ (-b) := by
        have : (64 : ℝ) ^ (-b) ≤ t ^ (-b) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h64.le (by linarith)
        have h2 : (64 : ℝ) ^ b * 64 ^ (-b) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; simp
        calc (1 : ℝ) = 64 ^ b * 64 ^ (-b) := h2.symm
          _ ≤ 64 ^ b * t ^ (-b) := mul_le_mul_of_nonneg_left this (by positivity)
      have hpow : (64 : ℝ) ^ (E₀ + b) = 64 ^ E₀ * 64 ^ b := Real.rpow_add (by norm_num) _ _
      have hBE : 0 ≤ Bc * 64 ^ E₀ := by positivity
      calc Bc * 64 ^ E₀ * (1 + Pm.card)
          ≤ Bc * 64 ^ E₀ * (1 + Pm.card) * (64 ^ b * t ^ (-b)) := le_mul_of_one_le_right
            (by positivity) hb64
        _ ≤ Bc * ((1 + Pp.card + Pm.card) * 64 ^ (E₀ + b)) * t ^ (-b) := by
          rw [hpow]
          have : (0 : ℝ) ≤ Pp.card := by positivity
          have h3 : (1 + (Pm.card : ℝ)) ≤ 1 + Pp.card + Pm.card := by linarith
          have h4 : 0 ≤ Bc * 64 ^ E₀ * 64 ^ b * t ^ (-b) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h3 h4]
    · -- large regime: `T = S + ∑_{Pp} J`
      have hS' := hS h64
      have hJ' : ∀ i ∈ Pp, |J i| ≤ Bc * t ^ (-b) := fun i hi => (hJp i hi).trans
        (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_one_le h1 (hPp i hi)) hBc)
      have : |T| ≤ Bc * t ^ (-b) * (1 + Pp.card) := by
        rw [hT1]
        calc |S + ∑ i ∈ Pp, J i| ≤ |S| + |∑ i ∈ Pp, J i| := abs_add_le _ _
          _ ≤ Bc * t ^ (-b) + ∑ i ∈ Pp, |J i| := add_le_add hS' (abs_sum_le_sum_abs _ _)
          _ ≤ Bc * t ^ (-b) + ∑ _i ∈ Pp, Bc * t ^ (-b) := add_le_add le_rfl (sum_le_sum hJ')
          _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
      refine this.trans ?_
      have hta : 0 ≤ Bc * t ^ (-b) := mul_nonneg hBc (Real.rpow_nonneg ht.le _)
      have h2 : (1 + (Pp.card : ℝ)) ≤ (1 + Pp.card + Pm.card) *
          64 ^ (|e₁| + ∑ i ∈ Pm, |e i| + b) := by
        have : (0 : ℝ) ≤ Pm.card := by positivity
        nlinarith
      calc Bc * t ^ (-b) * (1 + Pp.card) ≤ Bc * t ^ (-b) * ((1 + Pp.card + Pm.card) *
          64 ^ (|e₁| + ∑ i ∈ Pm, |e i| + b)) := mul_le_mul_of_nonneg_left h2 hta
        _ = _ := by ring

end RegularityStructures.KGammaSup

end

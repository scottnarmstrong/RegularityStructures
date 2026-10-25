/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.Tactic

/-!
# Polynomial growth of a Taylor-remainder cocycle from its local bounds

Let `v(x, y)` and `γ_i(x, y)` be random variables on `ℝ⁴ × ℝ⁴` with
* the cocycle `v(x, y) = v(x, z) + v(z, y) + ∑ᵢ γ_i(x, z) (y - z)ᵢ`;
* the additivity `γ_i(x, y) = γ_i(x, z) + γ_i(z, y)`;
* `L^q` bounds `≤ A` for `v(x, y)`, `γ_i(x, y)` when `‖y - x‖_𝔰 ≤ 1/2`.

Then `‖v(x, x + k h)‖_q ≤ A (k + 3 k²/4)` for `‖h‖_𝔰 ≤ 1/2`
(`eLpNorm_chain_le`), and so `‖v(x, y)‖_q ≤ 128 A ‖y - x‖_𝔰^4` for `‖y - x‖_𝔰 ≥ 1/2`
(`eLpNorm_far_le`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The `L^q` bound of the additive cocycle `γ` along an arithmetic progression. -/
theorem eLpNorm_gamma_chain_le {q : ℝ≥0∞} (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A)
    (γ : ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (hadd : ∀ x z y ω, γ x y ω = γ x z ω + γ z y ω)
    (hnear : ∀ x y, parabolicNorm (y - x) ≤ 1 / 2 → eLpNorm (γ x y) q P ≤ ENNReal.ofReal A)
    (x h : ParabolicSpace) (hh : parabolicNorm h ≤ 1 / 2) (k : ℕ) :
    eLpNorm (γ x (x + (k : ℝ) • h)) q P ≤ ENNReal.ofReal (A * k) := by
  have h0 : ∀ ω, γ x x ω = 0 := fun ω => by
    have := hadd x x x ω
    linarith
  induction k with
  | zero =>
    have : γ x (x + ((0 : ℕ) : ℝ) • h) = fun _ => 0 := by
      funext ω
      simpa using h0 ω
    rw [this]
    simp
  | succ k ih =>
    have e : γ x (x + ((k + 1 : ℕ) : ℝ) • h) = γ x (x + (k : ℝ) • h) +
        γ (x + (k : ℝ) • h) (x + ((k + 1 : ℕ) : ℝ) • h) := by
      funext ω
      exact hadd x (x + (k : ℝ) • h) _ ω
    have hstep : parabolicNorm ((x + ((k + 1 : ℕ) : ℝ) • h) - (x + (k : ℝ) • h)) ≤ 1 / 2 := by
      have : (x + ((k + 1 : ℕ) : ℝ) • h) - (x + (k : ℝ) • h) = h := by
        push_cast
        module
      rw [this]; exact hh
    rw [e]
    refine (eLpNorm_add_le hq).trans ?_
    refine (add_le_add ih (hnear _ _ hstep)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) hA]
    congr 1
    push_cast
    ring

/-- The `L^q` bound of the cocycle `v` along an arithmetic progression. -/
theorem eLpNorm_chain_le {q : ℝ≥0∞} (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A)
    (v : ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (γ : Fin 3 → ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (hcoc : ∀ x z y ω, v x y ω = v x z ω + v z y ω +
      ∑ i, γ i x z ω * (y.2 i - z.2 i))
    (hadd : ∀ i x z y ω, γ i x y ω = γ i x z ω + γ i z y ω)
    (hnv : ∀ x y, parabolicNorm (y - x) ≤ 1 / 2 → eLpNorm (v x y) q P ≤ ENNReal.ofReal A)
    (hnγ : ∀ i x y, parabolicNorm (y - x) ≤ 1 / 2 → eLpNorm (γ i x y) q P ≤ ENNReal.ofReal A)
    (x h : ParabolicSpace) (hh : parabolicNorm h ≤ 1 / 2) (k : ℕ) :
    eLpNorm (v x (x + (k : ℝ) • h)) q P ≤ ENNReal.ofReal (A * (k + 3 * (k : ℝ) ^ 2 / 4)) := by
  have h0 : ∀ ω, v x x ω = 0 := fun ω => by
    have := hcoc x x x ω
    simp at this
    linarith
  induction k with
  | zero =>
    have : v x (x + ((0 : ℕ) : ℝ) • h) = fun _ => 0 := by
      funext ω
      simpa using h0 ω
    rw [this]
    simp
  | succ k ih =>
    have hstep : parabolicNorm ((x + ((k + 1 : ℕ) : ℝ) • h) - (x + (k : ℝ) • h)) ≤ 1 / 2 := by
      have : (x + ((k + 1 : ℕ) : ℝ) • h) - (x + (k : ℝ) • h) = h := by
        push_cast
        module
      rw [this]; exact hh
    have e : v x (x + ((k + 1 : ℕ) : ℝ) • h) = (v x (x + (k : ℝ) • h) +
        v (x + (k : ℝ) • h) (x + ((k + 1 : ℕ) : ℝ) • h)) +
        ∑ i, (fun ω => γ i x (x + (k : ℝ) • h) ω * h.2 i) := by
      funext ω
      rw [hcoc x (x + (k : ℝ) • h) _ ω]
      simp only [Pi.add_apply, Finset.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      simp
      ring
    have hγk := fun i => eLpNorm_gamma_chain_le hq hA (γ i) (hadd i) (hnγ i) x h hh k
    have hterm : ∀ i : Fin 3, eLpNorm (fun ω => γ i x (x + (k : ℝ) • h) ω * h.2 i) q P ≤
        ENNReal.ofReal (A * k / 2) := by
      intro i
      have hhi : |h.2 i| ≤ 1 / 2 := by
        refine le_trans ?_ hh
        unfold parabolicNorm
        have := Finset.single_le_sum (f := fun j => |h.2 j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
        have := Real.sqrt_nonneg |h.1|
        linarith
      have e2 : (fun ω => γ i x (x + (k : ℝ) • h) ω * h.2 i) =
          (h.2 i) • γ i x (x + (k : ℝ) • h) := by
        funext ω; simp [mul_comm]
      rw [e2]
      refine eLpNorm_const_smul_le.trans ?_
      refine (mul_le_mul' (le_of_eq (Real.enorm_eq_ofReal_abs _)) (hγk i)).trans ?_
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 0 ≤ A * k := by positivity
      nlinarith
    rw [e]
    refine (eLpNorm_add_le hq).trans ?_
    refine (add_le_add (eLpNorm_add_le hq) (eLpNorm_sum_le hq)).trans ?_
    refine (add_le_add (add_le_add ih (hnv _ _ hstep))
      (Finset.sum_le_sum fun i _ => hterm i)).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : ((3 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (A * k / 2) = ENNReal.ofReal (3 * (A * k / 2)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [h3, ← ENNReal.ofReal_add (by positivity) hA,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    nlinarith [mul_nonneg hA hk0, mul_nonneg hA (sq_nonneg (k : ℝ))]

/-- `‖(1/n) d‖_𝔰 ≤ n^(-1/2) ‖d‖_𝔰` for `n ≥ 1`. -/
theorem parabolicNorm_smul_inv_le {n : ℕ} (hn : 1 ≤ n) (d : ParabolicSpace) :
    parabolicNorm (((n : ℝ)⁻¹) • d) ≤ ((n : ℝ)⁻¹.sqrt) * parabolicNorm d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  have hc0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hsc : (n : ℝ)⁻¹ ≤ Real.sqrt ((n : ℝ)⁻¹) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  unfold parabolicNorm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply, abs_mul,
    abs_of_nonneg hc0]
  rw [Real.sqrt_mul hc0, mul_add, Finset.mul_sum]
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum fun i _ => ?_
  calc (n : ℝ)⁻¹ * |d.2 i| ≤ Real.sqrt ((n : ℝ)⁻¹) * |d.2 i| :=
        mul_le_mul_of_nonneg_right hsc (abs_nonneg _)
    _ ≤ _ := le_rfl

/-- **Polynomial growth of the cocycle**: `‖v(x, y)‖_q ≤ 128 A ‖y - x‖_𝔰^4` for
`‖y - x‖_𝔰 > 1/2`. -/
theorem eLpNorm_far_le {q : ℝ≥0∞} (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A)
    (v : ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (γ : Fin 3 → ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (hcoc : ∀ x z y ω, v x y ω = v x z ω + v z y ω +
      ∑ i, γ i x z ω * (y.2 i - z.2 i))
    (hadd : ∀ i x z y ω, γ i x y ω = γ i x z ω + γ i z y ω)
    (hnv : ∀ x y, parabolicNorm (y - x) ≤ 1 / 2 → eLpNorm (v x y) q P ≤ ENNReal.ofReal A)
    (hnγ : ∀ i x y, parabolicNorm (y - x) ≤ 1 / 2 → eLpNorm (γ i x y) q P ≤ ENNReal.ofReal A)
    (x y : ParabolicSpace) (hr : 1 / 2 < parabolicNorm (y - x)) :
    eLpNorm (v x y) q P ≤ ENNReal.ofReal (128 * A * parabolicNorm (y - x) ^ 4) := by
  set r := parabolicNorm (y - x) with hrdef
  have hr0 : 0 < r := by linarith
  set n : ℕ := ⌈4 * r ^ 2⌉₊ with hn
  have hn4 : 4 * r ^ 2 ≤ n := Nat.le_ceil _
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) < n := by nlinarith
    exact_mod_cast this.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnle : (n : ℝ) ≤ 8 * r ^ 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 4 * r ^ 2 by positivity)
    rw [← hn] at this
    nlinarith
  set h : ParabolicSpace := ((n : ℝ)⁻¹) • (y - x) with hh
  have hhn : parabolicNorm h ≤ 1 / 2 := by
    refine (parabolicNorm_smul_inv_le hn1 (y - x)).trans ?_
    rw [← hrdef]
    have hs : 2 * r ≤ Real.sqrt n := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have hsq : Real.sqrt ((n : ℝ)⁻¹) = (Real.sqrt n)⁻¹ := by
      rw [Real.sqrt_inv]
    rw [hsq]
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    rw [inv_mul_le_iff₀ hsp]
    linarith
  have hy : x + (n : ℝ) • h = y := by
    rw [hh, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    abel
  have key := eLpNorm_chain_le hq hA v γ hcoc hadd hnv hnγ x h hhn n
  rw [hy] at key
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 : (n : ℝ) + 3 * (n : ℝ) ^ 2 / 4 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
  have h2 : (n : ℝ) ^ 2 ≤ 64 * r ^ 4 := by nlinarith
  nlinarith [mul_nonneg hA hn0.le]

end RegularityStructures

end

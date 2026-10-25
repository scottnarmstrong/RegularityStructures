/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Diff
public import RegularityStructures.Analysis.Heat.Schauder.Shell
public import RegularityStructures.Analysis.Heat.Schauder.ShellIntegral
public import RegularityStructures.Analysis.Heat.Schauder.Lip

/-!
# Increment bounds for the heat shells

Scaling of the generator on the heat shells (`parabolicGenerator_heatShell`) and the `L¹` bounds on
the increments of the shells (`exists_heatShell_diff_bounds`).

Source: [Hai14, Lemma 5.5].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem parabolicGenerator_sub_shift {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (e w : ParabolicSpace) :
    parabolicGenerator (fun w => f w - f (w - e)) w =
      parabolicGenerator f w - parabolicGenerator f (w - e) := by
  have hk : ∀ k : ℕ, ContDiff ℝ k f := fun k => hf.of_le (by exact_mod_cast le_top)
  have hs : ∀ k : ℕ, ContDiff ℝ k (fun w => f (w - e)) := fun k =>
    (hk k).comp (contDiff_id.sub contDiff_const)
  have E : ∀ (k : ℕ) (v : ParabolicSpace),
      iteratedFDeriv ℝ k (fun w => f w - f (w - e)) w (fun _ => v) =
        iteratedFDeriv ℝ k f w (fun _ => v) - iteratedFDeriv ℝ k f (w - e) (fun _ => v) := by
    intro k v
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := w) (i := k) (f := f)
      (g := fun w => f (w - e)) (hk k).contDiffAt (hs k).contDiffAt
    rw [iteratedFDeriv_comp_sub] at this
    have h2 : (fun w => f w - f (w - e)) = f - fun w => f (w - e) := rfl
    rw [h2, this]
    rfl
  unfold parabolicGenerator
  simp only [E, Finset.sum_sub_distrib]
  ring

/-- Pointwise scaling of the generator of the `n`-th shell: `L (heatShell n) w =
(2^n)^7 · L (heatShell 0) (S^{2^n} w)`. -/
theorem parabolicGenerator_heatShell (n : ℕ) (w : ParabolicSpace) :
    parabolicGenerator (heatShell n) w =
      ((2 : ℝ) ^ n) ^ 7 * parabolicGenerator (heatShell 0) (parabolicDilate (2 ^ n) w) := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hc : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.2 h2
  have hfun : heatShell n = fun w => ((2 : ℝ) ^ n)⁻¹ ^ 2 *
      rescaledTestFunction (heatShell 0) (((2 : ℝ) ^ n)⁻¹) 0 w := funext (heatShell_eq_mul_rescaled n)
  have hsm := contDiff_rescaledTestFunction (contDiff_heatShell 0) (((2 : ℝ) ^ n)⁻¹) 0
  rw [hfun, parabolicGenerator_const_mul hsm]
  beta_reduce
  rw [parabolicGenerator_rescaledTestFunction (contDiff_heatShell 0) hc]
  unfold rescaledTestFunction
  simp only [sub_zero, inv_inv]
  field_simp

/-- Scaling of an `L¹` increment under `S^N`. -/
theorem integral_abs_scaled_sub (g : ParabolicSpace → ℝ) {N : ℝ} (hN : 0 < N) (c : ℝ)
    (e : ParabolicSpace) :
    ∫ w, |c * (g (parabolicDilate N w) - g (parabolicDilate N w - parabolicDilate N e))| =
      |c| * (N ^ 5)⁻¹ * ∫ u, |g u - g (u - parabolicDilate N e)| := by
  have := integral_comp_parabolicDilate (fun u => |g u - g (u - parabolicDilate N e)|) hN
  simp only [abs_mul]
  rw [integral_const_mul, this]
  ring

theorem exists_heatShell_diff_bounds :
    ∃ M₀ M₁ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ ∀ (n : ℕ) (e : ParabolicSpace),
      parabolicNorm e * 2 ^ n ≤ 1 →
      (∫ w, |heatShell n w - heatShell n (w - e)| ≤
          M₀ * ((2 : ℝ) ^ n)⁻¹ * parabolicNorm e) ∧
      (∫ w, |parabolicGenerator (fun w => heatShell n w - heatShell n (w - e)) w| ≤
          M₁ * ((2 : ℝ) ^ n) ^ 3 * parabolicNorm e) := by
  have hs0 : ∀ w, 1 < parabolicNorm w → heatShell 0 w = 0 := fun w hw =>
    heatShell_eq_zero (by simpa using hw)
  have hLs0 : ∀ w, 1 < parabolicNorm w → parabolicGenerator (heatShell 0) w = 0 := fun w hw =>
    parabolicGenerator_eq_zero_of_lt (lam := 1) (fun w hw => hs0 w hw) hw
  obtain ⟨M₀, hM₀, h0⟩ := exists_integral_abs_sub_le (contDiff_heatShell 0) hs0
  obtain ⟨M₁, hM₁, h1⟩ := exists_integral_abs_sub_le
    (contDiff_parabolicGenerator (contDiff_heatShell 0)) hLs0
  refine ⟨M₀, M₁, hM₀, hM₁, fun n e he => ?_⟩
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have ha : parabolicNorm (parabolicDilate (2 ^ n) e) = 2 ^ n * parabolicNorm e :=
    parabolicNorm_parabolicDilate hN.le e
  have ha1 : parabolicNorm (parabolicDilate (2 ^ n) e) ≤ 1 := by rw [ha]; linarith
  have e1 : ∀ w, |heatShell n w - heatShell n (w - e)| =
      |((2 : ℝ) ^ n) ^ 3 * (heatShell 0 (parabolicDilate (2 ^ n) w) -
        heatShell 0 (parabolicDilate (2 ^ n) w - parabolicDilate (2 ^ n) e))| := by
    intro w
    rw [heatShell_eq_scale n w, heatShell_eq_scale n (w - e), parabolicDilate_sub]
    ring_nf
  have e2 : ∀ w, |parabolicGenerator (fun w => heatShell n w - heatShell n (w - e)) w| =
      |((2 : ℝ) ^ n) ^ 7 * (parabolicGenerator (heatShell 0) (parabolicDilate (2 ^ n) w) -
        parabolicGenerator (heatShell 0) (parabolicDilate (2 ^ n) w - parabolicDilate (2 ^ n) e))| := by
    intro w
    rw [parabolicGenerator_sub_shift (contDiff_heatShell n), parabolicGenerator_heatShell n w,
      parabolicGenerator_heatShell n (w - e), parabolicDilate_sub]
    ring_nf
  have hpos3 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 3 := by positivity
  have hpos7 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 7 := by positivity
  constructor
  · simp_rw [e1]
    rw [integral_abs_scaled_sub _ hN, abs_of_pos hpos3]
    have := h0 _ ha1
    rw [ha] at this
    calc ((2 : ℝ) ^ n) ^ 3 * (((2 : ℝ) ^ n) ^ 5)⁻¹ * ∫ u, |heatShell 0 u -
          heatShell 0 (u - parabolicDilate (2 ^ n) e)|
        ≤ ((2 : ℝ) ^ n) ^ 3 * (((2 : ℝ) ^ n) ^ 5)⁻¹ * (M₀ * (2 ^ n * parabolicNorm e)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  · simp_rw [e2]
    rw [integral_abs_scaled_sub _ hN, abs_of_pos hpos7]
    have := h1 _ ha1
    rw [ha] at this
    calc ((2 : ℝ) ^ n) ^ 7 * (((2 : ℝ) ^ n) ^ 5)⁻¹ * ∫ u, |parabolicGenerator (heatShell 0) u -
          parabolicGenerator (heatShell 0) (u - parabolicDilate (2 ^ n) e)|
        ≤ ((2 : ℝ) ^ n) ^ 7 * (((2 : ℝ) ^ n) ^ 5)⁻¹ * (M₁ * (2 ^ n * parabolicNorm e)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.ShellPairing
public import RegularityStructures.Analysis.Heat.Schauder.ShellPairingBound
public import RegularityStructures.Analysis.Heat.Schauder.Diff
public import RegularityStructures.Analysis.Heat.Schauder.DiffBound
public import RegularityStructures.Analysis.Heat.Schauder.Support

/-!
# Increment of the shell pairings

For `‖x - y‖_𝔰 ≤ 2^{-n}/4`,
`|⟨Λ, heatShell n (x - ·)⟩ - ⟨Λ, heatShell n (y - ·)⟩| ≤ c₃ C ‖x - y‖_𝔰 2^{-(α+1) n}`
(`exists_abs_pairing_heatShell_sub_le`): the difference is paired with
`heatShell n (x - ·) - heatShell n (y - ·)`, whose `L¹` norm (and that of its generator image)
is `≲ 2^n ‖x - y‖_𝔰` times that of a single shell.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem integrable_mul_heatShell_sub {Λ : ℝ → ParabolicSpace → ℝ} {α C : ℝ}
    (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hloc : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (n : ℕ) (x : ParabolicSpace) :
    Integrable fun y => Λ s y * heatShell n (x - y) := by
  have hφ : Continuous fun y => heatShell n (x - y) :=
    (contDiff_heatShell n).continuous.comp (continuous_const.sub continuous_id)
  have hsupp : HasCompactSupport fun y => heatShell n (x - y) :=
    hasCompactSupport_of_eq_zero (c := 1) one_pos x fun y hy => by
      refine heatShell_eq_zero (lt_of_le_of_lt ?_ (by rwa [parabolicNorm_sub_comm]))
      exact pow_le_one₀ (by norm_num) (by norm_num)
  exact (hφ.integrable_of_hasCompactSupport hsupp).bdd_mul (c := C * s ^ (α / 4))
    (hΛm s hs.1).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hloc s hs y)

theorem exists_abs_pairing_heatShell_sub_le {α : ℝ} (hα : -2 < α) :
    ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ},
      Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
      (∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) →
      ∀ (n : ℕ) (x y : ParabolicSpace), parabolicNorm (x - y) * 2 ^ n ≤ 1 / 4 →
        |parabolicSemigroup.pairing Λ (fun z => heatShell n (x - z)) -
            parabolicSemigroup.pairing Λ (fun z => heatShell n (y - z))| ≤
          c₃ * C * parabolicNorm (x - y) * (2 : ℝ) ^ (-(α + 1) * n) := by
  obtain ⟨M₀, M₁, hM₀, hM₁, hM⟩ := exists_heatShell_diff_bounds
  refine ⟨(1 + 4 / (α + 4)) * (M₀ + M₁), ?_, ?_⟩
  · have : 0 < α + 4 := by linarith
    positivity
  intro Λ C hΛ hΛm hC hloc n x y hxy
  set e := x - y with he
  set d := parabolicNorm e with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlam : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  have hlam1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hdn : d * 2 ^ n ≤ 1 := by linarith
  obtain ⟨hb0, hb1⟩ := hM n e hdn
  set h : ParabolicSpace → ℝ := fun w => heatShell n w - heatShell n (w - e) with hh
  have hhs : ContDiff ℝ ∞ h :=
    (contDiff_heatShell n).sub ((contDiff_heatShell n).comp (contDiff_id.sub contDiff_const))
  set q : ℝ := (2 : ℝ)⁻¹ ^ n with hq
  have hNq : (2 : ℝ) ^ n * q = 1 := by rw [hq, inv_pow]; field_simp
  have hdq : d ≤ q / 4 := by
    have := mul_le_mul_of_nonneg_right hxy hlam.le
    nlinarith
  have hsupp : ∀ w, q < parabolicNorm w → h w = 0 := by
    intro w hw
    have h1 : heatShell n w = 0 := heatShell_eq_zero_of_gt (by linarith)
    have h2 : heatShell n (w - e) = 0 := by
      refine heatShell_eq_zero_of_gt ?_
      have := parabolicNorm_add_le (w - e) e
      rw [sub_add_cancel] at this
      linarith
    simp [hh, h1, h2]
  have hrp : q ^ (-(4 : ℝ)) = ((2 : ℝ) ^ n) ^ 4 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    simp [hq, inv_pow]
  have hB1 : ∫ w, |parabolicGenerator h w| ≤ (M₁ * (2 ^ n)⁻¹ * d) * q ^ (-(4 : ℝ)) := by
    refine hb1.trans (le_of_eq ?_)
    rw [hrp]; field_simp; rfl
  have key := tendsto_and_abs_pairing_reflect_le hΛ hΛm (by linarith : -4 < α) hC hloc hhs
    hlam hlam1 hsupp hb0 hB1 x
  -- identify the pairing of the increment
  have hT1 := (tendsto_and_abs_pairing_heatShell_le hΛ hΛm hα hC hloc n x).1
  have hT2 := (tendsto_and_abs_pairing_heatShell_le hΛ hΛm hα hC hloc n y).1
  have hfun : ∀ z, h (x - z) = heatShell n (x - z) - heatShell n (y - z) := by
    intro z
    simp only [hh]
    congr 2
    rw [he]; abel
  have hlim : Filter.Tendsto (fun s => ∫ z, Λ s z * h (x - z)) (nhdsWithin 0 (Ioi 0))
      (nhds (parabolicSemigroup.pairing Λ (fun z => heatShell n (x - z)) -
        parabolicSemigroup.pairing Λ (fun z => heatShell n (y - z)))) := by
    refine (hT1.sub hT2).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs
    have hs' : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    simp only [hfun, mul_sub]
    rw [integral_sub (integrable_mul_heatShell_sub hΛm hloc hs' n x)
      (integrable_mul_heatShell_sub hΛm hloc hs' n y)]
  have hEq := tendsto_nhds_unique key.1 hlim
  rw [← hEq]
  refine key.2.trans (le_of_eq ?_)
  have hqα : q ^ α = (2 : ℝ) ^ (-α * n) := two_inv_pow_rpow n α
  have hexp : (2 : ℝ) ^ (-(α + 1) * n) = (2 : ℝ) ^ (-α * n) * (2 ^ n)⁻¹ := by
    have : (2 : ℝ) ^ (-(α + 1) * n) = (2 : ℝ) ^ (-α * n + -(n : ℝ)) := by congr 1; ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [hqα, hexp]
  ring

end RegularityStructures

end

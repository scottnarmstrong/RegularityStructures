/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceWindowIdentification
public import Phi43.Stochastic.StochasticHeatConvergenceWindowDerivativeBounds
public import Phi43.Stochastic.StochasticHeatConvergenceShiftedModeBounds
public import Phi43.ClassicalSolution.PeriodiseSupport
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import Phi43.RegularisedNoise.Properties
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Almost-sure polynomial derivative growth for regularised noise

This is the global time-patching part of [Hai14, Proposition 9.5].  A single
white-noise coefficient bound is obtained for all integer translates of one fixed
finite Fourier window.  The translated-window identification theorem then gives
local series representations, whose deterministic derivative majorants yield the
polynomial lift bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace RegularityStructures.Phi43

private theorem growth_floor_window (t : ℝ) :
    |t - (Int.floor t : ℝ)| < 1 := by
  rw [abs_lt]
  constructor
  · linarith [Int.floor_le t]
  · linarith [Int.lt_floor_add_one t]

private theorem growth_floor_abs_le (t : ℝ) :
    |(Int.floor t : ℝ)| ≤ |t| + 1 := by
  rw [abs_le]
  constructor
  · have h := Int.sub_one_lt_floor t
    linarith [neg_le_abs t]
  · exact (Int.floor_le t).trans (by linarith [le_abs_self t])

private theorem growth_floor_weight_le (t r : ℝ)
    (hr : 0 ≤ r) (hrt : Real.sqrt |t| ≤ r) :
    1 + (Int.floor t : ℝ) ^ 2 ≤ 2 * (1 + r) ^ 4 := by
  have hsqrt : |t| ≤ r ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg |t|) hr).mpr hrt
    simpa only [Real.sq_sqrt (abs_nonneg t)] using h
  have hn : |(Int.floor t : ℝ)| ≤ (1 + r) ^ 2 := by
    have h₁ := growth_floor_abs_le t
    have h₂ : |t| + 1 ≤ (1 + r) ^ 2 := by
      nlinarith [sq_nonneg r]
    exact h₁.trans (h₂.trans_eq (by ring))
  have hn2 : (Int.floor t : ℝ) ^ 2 ≤ (1 + r) ^ 4 := by
    have hsq := (sq_le_sq (a := (Int.floor t : ℝ))
      (b := (1 + r) ^ 2)).2 (by
        rw [abs_of_nonneg (sq_nonneg (1 + r))]
        exact hn)
    calc
      (Int.floor t : ℝ) ^ 2 ≤ ((1 + r) ^ 2) ^ 2 := hsq
      _ = (1 + r) ^ 4 := by ring
  have hA : 1 ≤ (1 + r) ^ 4 := one_le_pow₀ (by linarith)
  nlinarith

private theorem growth_derivative_bound_of_window
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ z : SpaceTime, R < |z.1| → Phi z = 0)
    (hR0 : 0 ≤ R) (hN : 0 < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1)
    (hL : 1 ≤ b - a) {X : Sum WindowFrequency WindowFrequency → ℝ}
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hX : ∀ i, |X i| ≤ C₀ * smoothVersionFrequencyNormSq (i.elim id id) ^ 3)
    (q : ℕ) (z : ParabolicSpace) :
    ‖iteratedFDeriv ℝ q (fun w : ParabolicSpace =>
      ∑' i, X i * smoothVersionWindowSeriesTerm Phi a b i
        (w.1, torusProj w.2)) z‖ ≤
      C₀ * ∑' i, stochasticHeatWindowDerivativeMajorant Phi a b q i := by
  exact norm_iteratedFDeriv_smoothVersion_windowSeries_le hPhi hR hR0 hN ha hb hL
    hC₀ hX q z

theorem regularisedNoise_ae_hasPhi43NoiseGrowth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (ξ : Ω → SpaceTime → ℝ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) :
    ∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω) := by
  obtain ⟨R₀, hR₀⟩ := timeSupport_periodise ρ hρ hε.1
  let R : ℝ := max R₀ 0
  have hR : ∀ z : SpaceTime, R < |z.1| → periodise ρ ε z = 0 := by
    intro z hz
    exact hR₀ z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hPhi : IsSmoothOnSpaceTime (periodise ρ ε) :=
    isSmoothOnSpaceTime_periodise ρ hρ hε.1
  let N : ℝ := 1
  let a : ℝ := -N - R - 1
  let b : ℝ := N + R + 1
  have hN : 0 < N := by simp [N]
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have ha : a = -N - R - 1 := rfl
  have hb : b = N + R + 1 := rfl
  have hL : 1 ≤ b - a := by
    dsimp [a, b, N]
    linarith [hRnonneg]
  have hab : a < b := by
    dsimp [a, b, N]
    linarith
  have hmode := whiteNoise_ae_shifted_modes_bound (P := P) hW hab
  have hseries_n (n : ℤ) :
      ∀ᵐ w ∂P, ∀ z : SpaceTime, |z.1| < N →
        ξ w (z + ((n : ℝ), 0)) =
          ∑' i, W (stochasticHeatShiftedWindowMode a b n i) w *
            smoothVersionWindowSeriesTerm (periodise ρ ε) a b i z := by
    let Wn : (SpaceTime → ℝ) → Ω → ℝ := fun h w => W (fun q => h (q - ((n : ℝ), 0))) w
    let ξn : Ω → SpaceTime → ℝ := fun w z => ξ w (z + ((n : ℝ), 0))
    have hWn : IsWhiteNoise P Wn := by
      simpa [Wn] using isWhiteNoise_shift_time (P := P) hW (n : ℝ)
    have hξn : IsRegularisedNoise P Wn ρ ε ξn := by
      simpa [Wn, ξn] using isRegularisedNoise_shift_time (P := P) hξ (n : ℝ)
    have hmode_n : ∀ᵐ w ∂P, ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ i,
        |Wn (smoothVersionWindowPhysicalMode a b i) w| ≤
          Cn * smoothVersionFrequencyNormSq (i.elim id id) ^ 3 := by
      filter_upwards [hmode] with w hw
      obtain ⟨Cw, hCw, hbw⟩ := hw
      refine ⟨Cw * (1 + (n : ℝ) ^ 2), ?_, ?_⟩
      · positivity
      · intro i
        have hi := hbw n i
        change |W (stochasticHeatShiftedWindowMode a b n i) w| ≤
          (Cw * (1 + (n : ℝ) ^ 2)) *
            smoothVersionFrequencyNormSq (i.elim id id) ^ 3
        simpa only [stochasticHeatShiftedModeWeight, mul_assoc] using hi
    have hs := whiteNoise_fixedWindowSeries_eqOn_ae_of_mode_bound
      (P := P) hWn hPhi hR (by exact le_max_right _ _) hN ha hb hξn.1
      (fun z => (hξn.2 z).2) hmode_n
    have hmode_eq (i : Sum WindowFrequency WindowFrequency) :
        stochasticHeatShiftedWindowMode a b n i =
          (fun q => smoothVersionWindowPhysicalMode a b i (q - ((n : ℝ), 0))) := rfl
    filter_upwards [hs] with w hw z hz
    simp_rw [hmode_eq]
    simpa [Wn, ξn] using hw z hz
  have hseries : ∀ᵐ w ∂P, ∀ n : ℤ, ∀ z : SpaceTime, |z.1| < N →
      ξ w (z + ((n : ℝ), 0)) =
        ∑' i, W (stochasticHeatShiftedWindowMode a b n i) w *
          smoothVersionWindowSeriesTerm (periodise ρ ε) a b i z := by
    apply ae_all_iff.2
    intro n
    exact hseries_n n
  filter_upwards [hmode, hseries] with ω hω hseries
  obtain ⟨C, hC, hbound⟩ := hω
  let X (n : ℤ) (i : Sum WindowFrequency WindowFrequency) : ℝ :=
    W (stochasticHeatShiftedWindowMode a b n i) ω
  have hX : ∀ n i, |X n i| ≤
      (C * (1 + (n : ℝ) ^ 2)) *
        smoothVersionFrequencyNormSq (i.elim id id) ^ 3 := by
    intro n i
    have h := hbound n i
    simpa [X, stochasticHeatShiftedModeWeight, mul_assoc] using h
  obtain ⟨M, hMnonneg, hMq⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℕ, q ≤ 4 →
      (∑' i, stochasticHeatWindowDerivativeMajorant (periodise ρ ε) a b q i) ≤ M := by
    let Mq : ℕ → ℝ := fun q =>
      ∑' i, stochasticHeatWindowDerivativeMajorant (periodise ρ ε) a b q i
    let M : ℝ := ∑ q ∈ Finset.range 5, Mq q
    have hMq0 : ∀ q, 0 ≤ Mq q := by
      intro q
      exact tsum_nonneg fun i =>
        stochasticHeatWindowDerivativeMajorant_nonneg (periodise ρ ε) a b q i
    refine ⟨M, ?_, ?_⟩
    · dsimp [M]
      exact Finset.sum_nonneg fun q hq => hMq0 q
    · intro q hq
      have hqmem : q ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
      have h := Finset.single_le_sum (s := Finset.range 5)
        (f := Mq) (fun j _ => hMq0 j) hqmem
      simpa [M, Mq] using h
  rw [Statements.HasPhi43NoiseGrowth]
  refine ⟨2 * C * M, 4, ?_⟩
  intro k hk z
  let n : ℤ := Int.floor z.1
  have hzwindow : |z.1 - (n : ℝ)| < N := by
    simpa [n, N] using growth_floor_window z.1
  let F : ParabolicSpace → ℝ := fun w => ξ ω (w.1, torusProj w.2)
  let S : ParabolicSpace → ℝ := fun w =>
    ∑' i, X n i * smoothVersionWindowSeriesTerm (periodise ρ ε) a b i
      (w.1 - (n : ℝ), torusProj w.2)
  have hFS : F =ᶠ[𝓝 z] S := by
    have hopen : IsOpen {w : ParabolicSpace |
        |w.1 - (n : ℝ)| < N} := by
      exact isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hzwindow] with w hw
    have he := hseries n (w.1 - (n : ℝ), torusProj w.2) hw
    simpa [F, S] using he
  have hderiv_eq := (hFS.iteratedFDeriv ℝ k).eq_of_nhds
  have hXn : ∀ i, |X n i| ≤
      (C * (1 + (n : ℝ) ^ 2)) *
        smoothVersionFrequencyNormSq (i.elim id id) ^ 3 := hX n
  have hcoef : 0 ≤ C * (1 + (n : ℝ) ^ 2) := by positivity
  have hderiv := growth_derivative_bound_of_window hPhi hR
    (le_max_right _ _) hN ha hb hL hcoef hXn k
      (z.1 - (n : ℝ), z.2)
  have hshift : ‖iteratedFDeriv ℝ k S z‖ =
      ‖iteratedFDeriv ℝ k (fun w : ParabolicSpace =>
        ∑' i, X n i * smoothVersionWindowSeriesTerm (periodise ρ ε) a b i
          (w.1, torusProj w.2)) (z - ((n : ℝ), 0))‖ := by
    let H : ParabolicSpace → ℝ := fun w =>
      ∑' i, X n i * smoothVersionWindowSeriesTerm (periodise ρ ε) a b i
        (w.1, torusProj w.2)
    have hS : S = fun w : ParabolicSpace => H (w - ((n : ℝ), 0)) := by
      funext w
      apply tsum_congr
      intro i
      congr 2
      all_goals simp
    have hcomp := iteratedFDeriv_comp_sub (𝕜 := ℝ) k ((n : ℝ), 0) z (f := H)
    rw [hS]
    simpa only [H] using congrArg (fun A => ‖A‖) hcomp
  have hbound_deriv : ‖iteratedFDeriv ℝ k S z‖ ≤
      (C * (1 + (n : ℝ) ^ 2)) *
        (∑' i, stochasticHeatWindowDerivativeMajorant (periodise ρ ε) a b k i) := by
    rw [hshift]
    have hzsub : z - ((n : ℝ), 0) = (z.1 - (n : ℝ), z.2) := by
      ext <;> simp
    rw [hzsub]
    exact hderiv
  have hr : Real.sqrt |z.1| ≤ parabolicNorm z := by
    unfold parabolicNorm
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg (fun _ _ => abs_nonneg (z.2 _)))
  have hweight := growth_floor_weight_le z.1 (parabolicNorm z)
    (parabolicNorm_nonneg z) hr
  have hMqk := hMq k hk
  calc
    ‖iteratedFDeriv ℝ k F z‖ = ‖iteratedFDeriv ℝ k S z‖ := by rw [hderiv_eq]
    _ ≤ (C * (1 + (n : ℝ) ^ 2)) *
        (∑' i, stochasticHeatWindowDerivativeMajorant (periodise ρ ε) a b k i) :=
      hbound_deriv
    _ ≤ (C * (1 + (n : ℝ) ^ 2)) * M :=
      mul_le_mul_of_nonneg_left hMqk hcoef
    _ ≤ (2 * C * M) * (1 + parabolicNorm z) ^ 4 := by
      have hC0 : 0 ≤ C := hC
      have hM0 : 0 ≤ M := hMnonneg
      have hpar : 0 ≤ parabolicNorm z := parabolicNorm_nonneg z
      have hA0 : 0 ≤ 1 + parabolicNorm z := by linarith
      have hweight' := mul_le_mul_of_nonneg_left hweight (mul_nonneg hC0 hM0)
      nlinarith [hweight']

end RegularityStructures.Phi43

end

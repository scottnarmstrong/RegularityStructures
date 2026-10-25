/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierCancellation
public import Phi43.Stochastic.StochasticHeatConvergenceBareDisplacement
public import Phi43.Stochastic.StochasticHeatConvergenceCenteredAveraging
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Uniform Gaussian bounds across mollifiers

The cancellation estimate uses the sum of the two profile masses and their parabolic moments. Its
constant is independent of both scales and of the probability space. This supplies the
cross-mollifier Gaussian input to the convergence of the noise potentials (`phi43Noise_cauchy`),
following [Hai14, Proposition 9.5, (9.14)--(9.17)].
-/

public noncomputable section

open MeasureTheory Real ProbabilityTheory

namespace RegularityStructures.Phi43

theorem stochasticHeatKernel_cross_difference_sq_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' s : ℝ},
      0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → 0 < s → s ≤ 1 → ∀ z : SpaceTime,
      (∫ w : SpaceTime,
        (stochasticHeatKernel ρ ε s z w - stochasticHeatKernel ρ' ε' s z w) ^ 2) ≤
        C * (max ε ε') ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨D, hD, hdisp⟩ := bareHeatRegularisedKernel_centered_displacement_sq_bound hθ hθ1
  obtain ⟨M, hM, hmoment⟩ := integral_abs_periodise_cross_sub_parabolic_moment_bound ρ ρ' hρ hρ' hθ
  let N : ℝ := (∫ y : ParabolicSpace, |ρ y|) + ∫ y : ParabolicSpace, |ρ' y|
  have hN : 0 ≤ N := add_nonneg (integral_nonneg fun y => abs_nonneg _)
    (integral_nonneg fun y => abs_nonneg _)
  have hconst : 0 ≤ N * D * M :=
    mul_nonneg (mul_nonneg hN hD) hM
  refine ⟨N * D * M, hconst, ?_⟩
  intro ε ε' s hε hε1 hε' hε'1 hs hs1 z
  let f : SpaceTime → ℝ := fun w => bareHeatRegularisedKernel s (z - w)
  let p : SpaceTime → ℝ := fun v => periodise ρ ε v - periodise ρ' ε' v
  have hfm : Measurable f :=
    (measurable_bareHeatRegularisedKernel s).comp (measurable_const.sub measurable_id)
  have hf2 : MemLp f 2 := memLp_comp_sub_left_spaceTime (memLp_bareHeatRegularisedKernel hs) z
  have hpm : Measurable p := (measurable_periodise ρ hρ).sub (measurable_periodise ρ' hρ')
  have hp1 : Integrable p := (integrable_periodise ρ hρ hε).sub (integrable_periodise ρ' hρ' hε')
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  obtain ⟨B', hB'⟩ := bounded_periodise ρ' hρ' hε'
  have hpB : ∀ v : SpaceTime, |p v| ≤ B + B' := by
    intro v
    have htriangle : |p v| ≤ |periodise ρ ε v| + |periodise ρ' ε' v| := by
      simpa only [p, sub_zero, zero_sub, abs_neg] using
        abs_sub_le (periodise ρ ε v) 0 (periodise ρ' ε' v)
    exact htriangle.trans (add_le_add (hB v) (hB' v))
  have hcenter := integral_centered_add_averaging_sq_le hfm hf2 hpm hp1 hpB
  have hprod := integrable_centered_add_translation_square_weight hfm hf2 hpm hp1
  have hinner : Integrable (fun v : SpaceTime => |p v| *
      ∫ w : SpaceTime, (f (w + v) - f w) ^ 2) := by
    apply hprod.integral_prod_left.congr
    filter_upwards [] with v
    rw [integral_mul_const]
    ring
  have hwi := integrable_abs_periodise_cross_sub_parabolic_moment ρ ρ' hρ hρ' hε hε1 hε' hε'1 hθ
  have hmajor : Integrable (fun v : SpaceTime => |p v| *
      (D * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)))) := by
    apply (hwi.const_mul (D * s ^ (-(1 / 2 + θ / 2 : ℝ)))).congr
    filter_upwards [] with v
    dsimp [p]
    ring
  have harg (w v : SpaceTime) : z - w - v = z - (w + v) := by abel
  have hdispv (v : SpaceTime) :
      (∫ w : SpaceTime, (f (w + v) - f w) ^ 2) ≤
        D * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
    have heq : (∫ w : SpaceTime, (f (w + v) - f w) ^ 2) =
        ∫ w : SpaceTime, (bareHeatRegularisedKernel s (z - w - v) -
          bareHeatRegularisedKernel s (z - w)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [harg]
    rw [heq]
    exact hdisp hs hs1 z v
  have hinnerbound : (∫ v : SpaceTime, |p v| *
      ∫ w : SpaceTime, (f (w + v) - f w) ^ 2) ≤
      (D * s ^ (-(1 / 2 + θ / 2 : ℝ))) * (M * (max ε ε') ^ θ) := by
    calc
      _ ≤ ∫ v : SpaceTime, |p v| *
          (D * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ))) :=
        integral_mono hinner hmajor (fun v => mul_le_mul_of_nonneg_left (hdispv v) (abs_nonneg _))
      _ = (D * s ^ (-(1 / 2 + θ / 2 : ℝ))) *
          ∫ v : SpaceTime, |p v| * torusParabolicSize v ^ θ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with v
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmoment hε hε1 hε' hε'1)
        (mul_nonneg hD (rpow_nonneg hs.le _))
  have hmass : (∫ v : SpaceTime, |p v|) ≤ N :=
    integral_abs_periodise_cross_sub_le ρ ρ' hρ hρ' hε hε1 hε' hε'1
  have heq (w : SpaceTime) : stochasticHeatKernel ρ ε s z w - stochasticHeatKernel ρ' ε' s z w =
      ∫ v : SpaceTime, (f (w + v) - f w) * p v := by
    rw [stochasticHeatKernel_cross_difference_eq_centered ρ ρ' hρ hρ' hε hε1 hε' hε'1 hs]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [harg]
  calc
    _ = ∫ w : SpaceTime, (∫ v : SpaceTime, (f (w + v) - f w) * p v) ^ 2 := by simp_rw [heq]
    _ ≤ (∫ v : SpaceTime, |p v|) *
        ∫ v : SpaceTime, |p v| * ∫ w : SpaceTime, (f (w + v) - f w) ^ 2 := hcenter
    _ ≤ (N) * ((D * s ^ (-(1 / 2 + θ / 2 : ℝ))) * (M * (max ε ε') ^ θ)) :=
      mul_le_mul hmass hinnerbound
        (integral_nonneg fun v => mul_nonneg (abs_nonneg _) (integral_nonneg fun w => sq_nonneg _))
        hN
    _ = (N * D * M) * (max ε ε') ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by ring
    _ ≤ (N * D * M) * (max ε ε') ^ θ * s ^ (-(1 / 2 + θ : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_ge hs hs1 (by linarith only [hθ]))
        (mul_nonneg hconst (rpow_nonneg (hε.le.trans (le_max_left _ _)) _))

theorem stochasticHeatField_cross_difference_even_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' s : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → 0 < s → s ≤ 1 →
      ∀ z : SpaceTime,
      (∫ ω, |stochasticHeatField W ρ ε s z ω -
        stochasticHeatField W ρ' ε' s z ω| ^ (2 * m) ∂P) ≤
        C * (max ε ε') ^ ((m : ℝ) * θ) *
          s ^ (-((m : ℝ) / 2 + (m : ℝ) * θ)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := stochasticHeatKernel_cross_difference_sq_bound_uniform ρ ρ' hρ hρ' hθ hθ1
  let M : ℝ := ∫ u : ℝ, |u| ^ (2 * m) ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg fun u => pow_nonneg (abs_nonneg _) _
  refine ⟨M * C₀ ^ m, mul_nonneg hM (pow_nonneg hC₀ _), ?_⟩
  intro Ω _ P W hW ε ε' s hε hε1 hε' hε'1 hs hs1 z
  have hm : MemLp (stochasticHeatKernel ρ ε s z) 2 :=
    memLp_stochasticHeatKernel_of_integrable_square ρ hρ hε hs z
      (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ hρ hε hs z)
  have hm' : MemLp (stochasticHeatKernel ρ' ε' s z) 2 :=
    memLp_stochasticHeatKernel_of_integrable_square ρ' hρ' hε' hs z
      (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ' hρ' hε' hs z)
  have hmoment := stochasticHeat_pairing_even_abs_moment_le hW
    (hm.sub hm') (hbound hε hε1 hε' hε'1 hs hs1 z) m
  have hleft : (∫ ω, |stochasticHeatField W ρ ε s z ω -
      stochasticHeatField W ρ' ε' s z ω| ^ (2 * m) ∂P) =
      ∫ ω, |W (stochasticHeatKernel ρ ε s z - stochasticHeatKernel ρ' ε' s z) ω| ^ (2 * m) ∂P := by
    apply integral_congr_ae
    filter_upwards [whiteNoise_pairing_sub_ae hW hm hm'] with ω hω
    exact congrArg (fun a : ℝ => |a| ^ (2 * m)) hω
  have hepow : ((max ε ε') ^ θ) ^ m = (max ε ε') ^ ((m : ℝ) * θ) := by
    rw [← rpow_natCast, ← rpow_mul (hε.le.trans (le_max_left _ _))]
    congr 1
    ring
  have hspow : (s ^ (-(1 / 2 + θ : ℝ))) ^ m =
      s ^ (-((m : ℝ) / 2 + (m : ℝ) * θ)) := by
    rw [← rpow_natCast, ← rpow_mul hs.le]
    congr 1
    ring
  rw [hleft]
  simpa only [mul_pow, hepow, hspow, mul_assoc, M] using hmoment

end RegularityStructures.Phi43

end


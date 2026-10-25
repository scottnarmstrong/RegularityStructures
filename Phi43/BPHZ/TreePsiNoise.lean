/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiDeterministic
public import Phi43.RegularisedNoise.Properties
public import Phi43.Stochastic.WhiteNoiseCovariance
public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Probability.GaussianVector

/-!
# Second-moment facts for a regularised noise version

For a regularised noise `ξ` of the white noise `W`, every `ξ ω x` is square integrable with
`E[ξ(u) ξ(v)] = ∫ M u M v` and `E[ξ(x) W h] = ∫ M x h`, where `M x = mollifierAt ρ ε x`.  Consequently
`E|ξ(x) ξ(y)| ≤ V` and `E|ξ(x) W h| ≤ (V + ‖h‖²)/2` uniformly in the coordinates, with
`V = ∫ (ρ_ε^♯)²`.  These feed the integrability hypotheses of stochastic Fubini.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- Each coordinate of a regularised noise is square integrable. -/
theorem treePsi_noise_memLp (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) : MemLp (fun ω => ξ ω x) 2 P := by
  have hvec := hW.2 1 (fun _ => mollifierAt ρ ε x) (fun _ => memLp_mollifierAt ρ hρ hε x)
  exact (memLp_congr_ae (hξ.2 x).2).2 (hvec.memLp_two_apply 0)

/-- `E[ξ(u) ξ(v)] = ∫ M u M v`. -/
theorem treePsi_noise_mul_integral (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (u v : SpaceTime) :
    ∫ ω, ξ ω u * ξ ω v ∂P = ∫ w, mollifierAt ρ ε u w * mollifierAt ρ ε v w := by
  calc ∫ ω, ξ ω u * ξ ω v ∂P
      = ∫ ω, W (mollifierAt ρ ε u) ω * W (mollifierAt ρ ε v) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [(hξ.2 u).2, (hξ.2 v).2] with ω hu hv
        rw [hu, hv]
    _ = _ := whiteNoise_pairing_mul_integral hW (memLp_mollifierAt ρ hρ hε u)
        (memLp_mollifierAt ρ hρ hε v)

/-- `E[ξ(x) W h] = ∫ M x h`. -/
theorem treePsi_noise_whiteNoise_integral (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {h : SpaceTime → ℝ}
    (hh : MemLp h 2) (x : SpaceTime) :
    ∫ ω, ξ ω x * W h ω ∂P = ∫ v, mollifierAt ρ ε x v * h v := by
  calc ∫ ω, ξ ω x * W h ω ∂P = ∫ ω, W (mollifierAt ρ ε x) ω * W h ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [(hξ.2 x).2] with ω hx
        rw [hx]
    _ = _ := whiteNoise_pairing_mul_integral hW (memLp_mollifierAt ρ hρ hε x) hh

/-- The common variance `V = ∫ (ρ_ε^♯)²` of the coordinates of `ξ`. -/
theorem treePsi_noise_sq_integral (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) :
    ∫ ω, ξ ω x * ξ ω x ∂P = ∫ w, periodise ρ ε w * periodise ρ ε w := by
  rw [treePsi_noise_mul_integral hρ hε hW hξ]
  exact integral_comp_sub_left_spaceTime (fun w => periodise ρ ε w * periodise ρ ε w) x

/-- Uniform `L¹` bound for products of two coordinates. -/
theorem treePsi_noise_abs_mul_le (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    ∫ ω, |ξ ω x * ξ ω y| ∂P ≤ ∫ w, periodise ρ ε w * periodise ρ ε w := by
  have hx : Integrable (fun ω => ξ ω x * ξ ω x) P :=
    (treePsi_noise_memLp hρ hε hW hξ x).integrable_mul (treePsi_noise_memLp hρ hε hW hξ x)
  have hy : Integrable (fun ω => ξ ω y * ξ ω y) P :=
    (treePsi_noise_memLp hρ hε hW hξ y).integrable_mul (treePsi_noise_memLp hρ hε hW hξ y)
  have hxy : Integrable (fun ω => ξ ω x * ξ ω y) P :=
    (treePsi_noise_memLp hρ hε hW hξ x).integrable_mul (treePsi_noise_memLp hρ hε hW hξ y)
  have hmaj : Integrable (fun ω => (ξ ω x * ξ ω x + ξ ω y * ξ ω y) / 2) P :=
    (hx.add hy).div_const 2
  calc ∫ ω, |ξ ω x * ξ ω y| ∂P ≤ ∫ ω, (ξ ω x * ξ ω x + ξ ω y * ξ ω y) / 2 ∂P := by
        refine integral_mono hxy.abs hmaj fun ω => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|ξ ω x| - |ξ ω y|), abs_mul_abs_self (ξ ω x),
          abs_mul_abs_self (ξ ω y)]
    _ = _ := by
        rw [integral_div, integral_add hx hy, treePsi_noise_sq_integral hρ hε hW hξ,
          treePsi_noise_sq_integral hρ hε hW hξ]
        ring

/-- Uniform `L¹` bound for the product of a coordinate with a white-noise pairing. -/
theorem treePsi_noise_abs_mul_whiteNoise_le (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {h : SpaceTime → ℝ}
    (hh : MemLp h 2) (x : SpaceTime) :
    ∫ ω, |ξ ω x * W h ω| ∂P ≤
      ((∫ w, periodise ρ ε w * periodise ρ ε w) + ∫ v, h v * h v) / 2 := by
  have hWm : MemLp (W h) 2 P := by
    have hvec := hW.2 1 (fun _ => h) (fun _ => hh)
    exact hvec.memLp_two_apply 0
  have hx : Integrable (fun ω => ξ ω x * ξ ω x) P :=
    (treePsi_noise_memLp hρ hε hW hξ x).integrable_mul (treePsi_noise_memLp hρ hε hW hξ x)
  have hy : Integrable (fun ω => W h ω * W h ω) P := hWm.integrable_mul hWm
  have hxy : Integrable (fun ω => ξ ω x * W h ω) P :=
    (treePsi_noise_memLp hρ hε hW hξ x).integrable_mul hWm
  have hmaj : Integrable (fun ω => (ξ ω x * ξ ω x + W h ω * W h ω) / 2) P :=
    (hx.add hy).div_const 2
  calc ∫ ω, |ξ ω x * W h ω| ∂P ≤ ∫ ω, (ξ ω x * ξ ω x + W h ω * W h ω) / 2 ∂P := by
        refine integral_mono hxy.abs hmaj fun ω => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|ξ ω x| - |W h ω|), abs_mul_abs_self (ξ ω x),
          abs_mul_abs_self (W h ω)]
    _ = _ := by
        rw [integral_div, integral_add hx hy, treePsi_noise_sq_integral hρ hε hW hξ,
          whiteNoise_pairing_mul_integral hW hh hh]

end RegularityStructures.Phi43

end

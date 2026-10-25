/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiNoise

/-!
# Stochastic Fubini for a regularised noise and an integrable kernel

For a regularised noise `ξ` of `W` (smooth in space-time, a version of `W (mollifierAt ρ ε x)`),
and an integrable kernel `k`, the pathwise integral `ω ↦ ∫ k x ξ ω x dx` agrees almost surely with
`W (v ↦ ∫ k x (mollifierAt ρ ε x v) dx)`.  The proof computes that the `L²(P)` distance vanishes,
using only the jointly measurable version `ξ` in product-measure calculations.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ} {k : SpaceTime → ℝ}

private theorem ae_zero_of_sq (D : Ω → ℝ) (hD : Integrable (fun ω => D ω ^ 2) P)
    (hzero : ∫ ω, D ω ^ 2 ∂P = 0) : D =ᵐ[P] 0 := by
  have hsq := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg (D ω)) hD).mp hzero
  filter_upwards [hsq] with ω hω
  exact sq_eq_zero_iff.mp hω

/-- Integrability of `k x * ξ ω x` on `Ω × ℝ×T³`. -/
private theorem integrable_single (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hk : Integrable k) :
    Integrable (Function.uncurry fun (ω : Ω) (x : SpaceTime) => k x * ξ ω x)
      (P.prod volume) := by
  have := hW.isProbabilityMeasure
  have hjoint := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  refine integrable_uncurry_mul_of_bound hk (Y := ξ) hjoint.aestronglyMeasurable
    (fun x => ?_) (M := ((∫ w, periodise ρ ε w * periodise ρ ε w) + 1) / 2) fun x => ?_
  · exact (treePsi_noise_memLp hρ hε hW hξ x).integrable one_le_two
  · have hm := treePsi_noise_memLp hρ hε hW hξ x
    have hx : Integrable (fun ω => ξ ω x * ξ ω x) P := hm.integrable_mul hm
    have hmaj : Integrable (fun ω => (ξ ω x * ξ ω x + 1) / 2) P :=
      (hx.add (integrable_const 1)).div_const 2
    calc ∫ ω, |ξ ω x| ∂P ≤ ∫ ω, (ξ ω x * ξ ω x + 1) / 2 ∂P := by
          refine integral_mono ((hm.integrable one_le_two).abs) hmaj fun ω => ?_
          nlinarith [sq_nonneg (|ξ ω x| - 1), abs_mul_abs_self (ξ ω x)]
      _ = _ := by
          rw [integral_div, integral_add hx (integrable_const 1),
            treePsi_noise_sq_integral hρ hε hW hξ]
          simp

/-- Integrability of `k x * k y * ξ x * ξ y`. -/
private theorem integrable_double (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hk : Integrable k) :
    Integrable (Function.uncurry fun (ω : Ω) (p : SpaceTime × SpaceTime) =>
      (k p.1 * k p.2) * (ξ ω p.1 * ξ ω p.2)) (P.prod (volume.prod volume)) := by
  have := hW.isProbabilityMeasure
  have hjoint := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have h1 : Measurable (fun q : Ω × (SpaceTime × SpaceTime) => ξ q.1 q.2.1) :=
    hjoint.comp (measurable_fst.prodMk measurable_snd.fst)
  have h2 : Measurable (fun q : Ω × (SpaceTime × SpaceTime) => ξ q.1 q.2.2) :=
    hjoint.comp (measurable_fst.prodMk measurable_snd.snd)
  exact integrable_uncurry_mul_of_bound (hk.mul_prod hk)
    (Y := fun ω p => ξ ω p.1 * ξ ω p.2) (h1.mul h2).aestronglyMeasurable
    (fun p => (treePsi_noise_memLp hρ hε hW hξ p.1).integrable_mul
      (treePsi_noise_memLp hρ hε hW hξ p.2))
    (M := ∫ w, periodise ρ ε w * periodise ρ ε w)
    (fun p => treePsi_noise_abs_mul_le hρ hε hW hξ p.1 p.2)

/-- Integrability of `k x * ξ x * W h`. -/
private theorem integrable_cross (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hk : Integrable k) {h : SpaceTime → ℝ}
    (hh : MemLp h 2) :
    Integrable (Function.uncurry fun (ω : Ω) (x : SpaceTime) => k x * (ξ ω x * W h ω))
      (P.prod volume) := by
  have := hW.isProbabilityMeasure
  have hjoint := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have hWm : MemLp (W h) 2 P := (hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0
  have hWj : Measurable (fun q : Ω × SpaceTime => W h q.1) := (hW.1 h hh).comp measurable_fst
  exact integrable_uncurry_mul_of_bound hk (Y := fun ω x => ξ ω x * W h ω)
    (hjoint.mul hWj).aestronglyMeasurable
    (fun x => (treePsi_noise_memLp hρ hε hW hξ x).integrable_mul hWm)
    (M := ((∫ w, periodise ρ ε w * periodise ρ ε w) + ∫ v, h v * h v) / 2)
    (fun x => treePsi_noise_abs_mul_whiteNoise_le hρ hε hW hξ hh x)

/-- **Stochastic Fubini** for a regularised noise: for an integrable kernel `k`,
`∫ k x ξ(x) dx = W (v ↦ ∫ k x (mollifierAt ρ ε x v) dx)` almost surely. -/
theorem treePsi_stochasticFubini_ae (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hk : Integrable k) :
    (fun ω => ∫ x, k x * ξ ω x) =ᵐ[P] W (treePsiConv ρ ε k) := by
  have := hW.isProbabilityMeasure
  have hh := treePsi_memLp_conv hρ hε hk
  have hA := integrable_single hρ hε hW hξ hk
  have hAA := integrable_double hρ hε hW hξ hk
  have hcr := integrable_cross hρ hε hW hξ hk hh
  have hWm : MemLp (W (treePsiConv ρ ε k)) 2 P :=
    (hW.2 1 (fun _ => treePsiConv ρ ε k) (fun _ => hh)).memLp_two_apply 0
  have hdd := treePsi_det_double hρ hε hk
  have hdc := treePsi_det_cross hρ hε hk
  let A : Ω → ℝ := fun ω => ∫ x, k x * ξ ω x
  let B : Ω → ℝ := W (treePsiConv ρ ε k)
  have hsq : ∀ ω, A ω ^ 2 = ∫ p : SpaceTime × SpaceTime,
      (k p.1 * k p.2) * (ξ ω p.1 * ξ ω p.2) := by
    intro ω
    have := integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun x => k x * ξ ω x) (fun x => k x * ξ ω x)
    rw [sq]
    refine this.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_))
    simp only
    ring
  have hA2 : Integrable (fun ω => A ω ^ 2) P := by
    refine hAA.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hsq ω).symm
  have hA2eq : ∫ ω, A ω ^ 2 ∂P = ∫ v, treePsiConv ρ ε k v ^ 2 := by
    calc ∫ ω, A ω ^ 2 ∂P
        = ∫ ω, (∫ p : SpaceTime × SpaceTime, (k p.1 * k p.2) * (ξ ω p.1 * ξ ω p.2)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hsq)
      _ = ∫ p : SpaceTime × SpaceTime, (∫ ω, (k p.1 * k p.2) * (ξ ω p.1 * ξ ω p.2) ∂P) :=
          integral_integral_swap hAA
      _ = ∫ p : SpaceTime × SpaceTime,
            k p.1 * k p.2 * ∫ w, mollifierAt ρ ε p.1 w * mollifierAt ρ ε p.2 w := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only
          rw [integral_const_mul, treePsi_noise_mul_integral hρ hε hW hξ]
      _ = ∫ x, ∫ y, k x * k y * ∫ w, mollifierAt ρ ε x w * mollifierAt ρ ε y w := by
          refine integral_prod _ ?_
          have := hAA.integral_prod_right
          refine this.congr (Filter.Eventually.of_forall fun p => ?_)
          simp only [Function.uncurry_apply_pair]
          rw [integral_const_mul, treePsi_noise_mul_integral hρ hε hW hξ]
      _ = _ := hdd
  have hB2 : Integrable (fun ω => B ω ^ 2) P := by
    have : Integrable (fun ω => B ω * B ω) P := hWm.integrable_mul hWm
    simpa only [sq] using this
  have hB2eq : ∫ ω, B ω ^ 2 ∂P = ∫ v, treePsiConv ρ ε k v ^ 2 := by
    simp only [B, sq]
    exact whiteNoise_pairing_mul_integral hW hh hh
  have hAB : ∀ ω, A ω * B ω = ∫ x, k x * (ξ ω x * W (treePsiConv ρ ε k) ω) := by
    intro ω
    simp only [A, B]
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  have hABi : Integrable (fun ω => A ω * B ω) P :=
    hcr.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => (hAB ω).symm)
  have hABeq : ∫ ω, A ω * B ω ∂P = ∫ v, treePsiConv ρ ε k v ^ 2 := by
    calc ∫ ω, A ω * B ω ∂P
        = ∫ ω, (∫ x, k x * (ξ ω x * W (treePsiConv ρ ε k) ω)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hAB)
      _ = ∫ x, (∫ ω, k x * (ξ ω x * W (treePsiConv ρ ε k) ω) ∂P) := integral_integral_swap hcr
      _ = ∫ x, k x * ∫ v, mollifierAt ρ ε x v * treePsiConv ρ ε k v := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [integral_const_mul, treePsi_noise_whiteNoise_integral hρ hε hW hξ hh]
      _ = _ := hdc
  have hD2 : Integrable (fun ω => (A ω - B ω) ^ 2) P := by
    refine ((hA2.add hB2).sub (hABi.const_mul 2)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hAB2 : Integrable (fun ω => A ω ^ 2 + B ω ^ 2) P := hA2.add hB2
  have hD0 : ∫ ω, (A ω - B ω) ^ 2 ∂P = 0 := by
    calc ∫ ω, (A ω - B ω) ^ 2 ∂P = ∫ ω, ((A ω ^ 2 + B ω ^ 2) - 2 * (A ω * B ω)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      _ = (∫ ω, (A ω ^ 2 + B ω ^ 2) ∂P) - ∫ ω, 2 * (A ω * B ω) ∂P :=
          integral_sub hAB2 (hABi.const_mul 2)
      _ = 0 := by
          rw [integral_add hA2 hB2, integral_const_mul, hA2eq, hB2eq, hABeq]
          ring
  filter_upwards [ae_zero_of_sq (fun ω => A ω - B ω) hD2 hD0] with ω hω
  exact sub_eq_zero.mp hω

end RegularityStructures.Phi43

end

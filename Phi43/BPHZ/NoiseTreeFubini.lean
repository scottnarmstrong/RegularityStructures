/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.NoiseTreeYoung
public import Phi43.Stochastic.WhiteNoiseCovariance
public import Phi43.Stochastic.AnnealedNoiseTorus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Stochastic Fubini for a jointly measurable version of the noise

Let `Ξ(ω, w)` be jointly measurable and, for every `w`, almost surely equal to `W (K(w - ·))`.
The raw family `(ω, w) ↦ W (K(w - ·)) ω` need not be jointly measurable, so the existing
stochastic Fubini theorem cannot be applied to it; here the pathwise integral `∫ ψ(w) Ξ(ω, w) dw`
is compared with `W g`, `g(u) = ∫ ψ(w) K(w - u) dw`, by an orthogonality argument.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- A bounded integrable measurable function is square integrable. -/
theorem memLp_two_of_bounded_integrable {K : SpaceTime → ℝ} (hK : Measurable K)
    (hKi : Integrable K) {B : ℝ} (hKb : ∀ z, |K z| ≤ B) : MemLp K 2 := by
  rw [memLp_two_iff_integrable_sq hK.aestronglyMeasurable]
  refine (hKi.norm.const_mul B).mono' (hK.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq, ← abs_mul_abs_self]
  exact mul_le_mul_of_nonneg_right (hKb z) (abs_nonneg _) |>.trans_eq (by simp)

private theorem noise_J3 [IsProbabilityMeasure P] {ψ : SpaceTime → ℝ}
    {Ξ : Ω → SpaceTime → ℝ} {κ : ℝ} (hψm : Measurable ψ) (hψ1 : Integrable ψ)
    (hΞ : Measurable fun q : Ω × SpaceTime => Ξ q.1 q.2)
    (hsq : ∀ w, Integrable (fun ω => Ξ ω w ^ 2) P) (hκ : ∀ w, ∫ ω, Ξ ω w ^ 2 ∂P = κ) :
    Integrable (fun q : Ω × SpaceTime => |ψ q.2| * Ξ q.1 q.2 ^ 2) (P.prod volume) := by
  have hmeas : Measurable (fun q : Ω × SpaceTime => |ψ q.2| * Ξ q.1 q.2 ^ 2) :=
    (hψm.norm.comp measurable_snd).mul (hΞ.pow_const 2)
  have hn : ∀ w ω, ‖|ψ w| * Ξ ω w ^ 2‖ = |ψ w| * Ξ ω w ^ 2 := fun w ω =>
    Real.norm_of_nonneg (by positivity)
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall fun w => (hsq w).const_mul (|ψ w|), ?_⟩
  have : ∀ w, ∫ ω, ‖|ψ w| * Ξ ω w ^ 2‖ ∂P = |ψ w| * κ := fun w => by
    simp only [hn]
    rw [integral_const_mul, hκ]
  simp only [this]
  exact hψ1.norm.mul_const κ

/-- Joint-version data used by the stochastic Fubini argument. -/
private structure JointData (P : Measure Ω) (ψ : SpaceTime → ℝ) (Ξ : Ω → SpaceTime → ℝ)
    (κ : ℝ) : Prop where
  ψm : Measurable ψ
  ψ1 : Integrable ψ
  Ξm : Measurable fun q : Ω × SpaceTime => Ξ q.1 q.2
  sq : ∀ w, Integrable (fun ω => Ξ ω w ^ 2) P
  κ : ∀ w, ∫ ω, Ξ ω w ^ 2 ∂P = κ

variable {ψ : SpaceTime → ℝ} {Ξ : Ω → SpaceTime → ℝ} {κ : ℝ}

private theorem noise_A_measurable (h : JointData P ψ Ξ κ) :
    Measurable fun ω => ∫ w, ψ w * Ξ ω w := by
  have hm : Measurable (fun q : Ω × SpaceTime => ψ q.2 * Ξ q.1 q.2) :=
    (h.ψm.comp measurable_snd).mul h.Ξm
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem noise_A_sq_integrable [IsProbabilityMeasure P] (h : JointData P ψ Ξ κ) :
    Integrable (fun ω => (∫ w, ψ w * Ξ ω w) ^ 2) P := by
  have hJ3 := noise_J3 h.ψm h.ψ1 h.Ξm h.sq h.κ
  set L : ℝ := ∫ w, |ψ w| with hL
  have hT : Integrable (fun ω => ∫ w, |ψ w| * Ξ ω w ^ 2) P := hJ3.integral_prod_left
  refine (hT.const_mul L).mono' ((noise_A_measurable h).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hJ3.prod_right_ae] with ω hω
  have hh : Integrable (fun w => |ψ w|) := h.ψ1.norm
  have hΞω : Measurable (Ξ ω) := h.Ξm.comp (measurable_const.prodMk measurable_id)
  have hf2h : Integrable (fun w => |Ξ ω w| ^ 2 * |ψ w|) := by
    refine hω.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [sq_abs]
    ring
  have hfh : Integrable (fun w => |Ξ ω w| * |ψ w|) := by
    refine ((hh.add hω).const_mul (1 / 2 : ℝ)).mono'
      ((hΞω.norm.mul h.ψm.norm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rw [← sq_abs (Ξ ω w)]
    nlinarith [mul_nonneg (abs_nonneg (ψ w)) (sq_nonneg (|Ξ ω w| - 1))]
  have hcs := noiseIntegral_mul_sq_le (μ := volume) (f := fun w => |Ξ ω w|)
    (h := fun w => |ψ w|) (fun _ => abs_nonneg _) hh hfh hf2h
  have habs : |∫ w, ψ w * Ξ ω w| ≤ ∫ w, |Ξ ω w| * |ψ w| := by
    have := norm_integral_le_integral_norm (μ := volume) (fun w => ψ w * Ξ ω w)
    simpa [abs_mul, mul_comm] using this
  have hsq : (∫ w, ψ w * Ξ ω w) ^ 2 ≤ (∫ w, |Ξ ω w| * |ψ w|) ^ 2 := by
    rw [← sq_abs (∫ w, ψ w * Ξ ω w)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine hsq.trans (hcs.trans_eq ?_)
  simp only [sq_abs, hL]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  ring

private theorem noise_mixed_fubini [IsProbabilityMeasure P] (h : JointData P ψ Ξ κ)
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ w, ψ w * Ξ ω w) * Z ω ∂P = ∫ w, ψ w * ∫ ω, Ξ ω w * Z ω ∂P := by
  have hJ3 := noise_J3 h.ψm h.ψ1 h.Ξm h.sq h.κ
  have hprod : Integrable (fun q : Ω × SpaceTime => Z q.1 ^ 2 * |ψ q.2|) (P.prod volume) :=
    hZ.integrable_sq.mul_prod h.ψ1.norm
  have hmeas : Measurable (fun q : Ω × SpaceTime => ψ q.2 * Ξ q.1 q.2 * Z q.1) :=
    ((h.ψm.comp measurable_snd).mul h.Ξm).mul (hZm.comp measurable_fst)
  have hJ4 : Integrable (Function.uncurry fun ω w => ψ w * Ξ ω w * Z ω) (P.prod volume) := by
    refine ((hJ3.add hprod).const_mul (1 / 2 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]
    show |ψ q.2 * Ξ q.1 q.2 * Z q.1| ≤
      1 / 2 * (|ψ q.2| * Ξ q.1 q.2 ^ 2 + Z q.1 ^ 2 * |ψ q.2|)
    rw [abs_mul, abs_mul, ← sq_abs (Ξ q.1 q.2), ← sq_abs (Z q.1)]
    have ha := abs_nonneg (ψ q.2)
    nlinarith [mul_nonneg ha (sq_nonneg (|Ξ q.1 q.2| - |Z q.1|))]
  calc ∫ ω, (∫ w, ψ w * Ξ ω w) * Z ω ∂P = ∫ ω, (∫ w, ψ w * Ξ ω w * Z ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (integral_mul_const (Z ω) _).symm
    _ = ∫ w, ∫ ω, ψ w * Ξ ω w * Z ω ∂P := integral_integral_swap hJ4
    _ = ∫ w, ψ w * ∫ ω, Ξ ω w * Z ω ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only [mul_assoc]
        exact integral_const_mul _ _

private theorem noise_kernel_fubini {K ψ v : SpaceTime → ℝ} (hK : Measurable K)
    (hKi : Integrable K) {B : ℝ} (hKb : ∀ z, |K z| ≤ B) (hψm : Measurable ψ)
    (hψ1 : Integrable ψ) (hψ2 : MemLp ψ 2) (hvm : Measurable v) (hv : MemLp v 2) :
    ∫ w, ψ w * ∫ u, K (w - u) * v u = ∫ u, (∫ w, ψ w * K (w - u)) * v u := by
  -- the absolute smeared test function is square integrable
  have hψa : MemLp (fun w => |ψ w|) 2 := hψ2.norm
  have hKa : Measurable (fun z => |K z|) := hK.norm
  obtain ⟨hgsq, -⟩ := noiseConv_sq_integral_le (K := fun z => |K z|) (ψ := fun w => |ψ w|)
    hKa hKi.norm (B := B) (fun z => by simpa using hKb z) hψm.norm hψa
  have hgm := measurable_noiseConv (K := fun z => |K z|) (ψ := fun w => |ψ w|) hKa hψm.norm
  have hgL2 : MemLp (fun u => ∫ w, |ψ w| * |K (w - u)|) 2 :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hgsq
  have hvg : Integrable (fun u => |v u| * ∫ w, |ψ w| * |K (w - u)|) :=
    hv.norm.integrable_mul hgL2
  have hmeas : Measurable (fun q : SpaceTime × SpaceTime => ψ q.2 * K (q.2 - q.1) * v q.1) :=
    ((hψm.comp measurable_snd).mul (hK.comp (measurable_snd.sub measurable_fst))).mul
      (hvm.comp measurable_fst)
  have hint : Integrable (Function.uncurry fun u w : SpaceTime => ψ w * K (w - u) * v u)
      (volume.prod volume) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun u => ?_, ?_⟩
    · have : Integrable (fun w => ψ w * K (w - u)) := by
        refine (hψ1.norm.const_mul B).mono'
          (hψm.mul (hK.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun w => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        calc |ψ w| * |K (w - u)| ≤ |ψ w| * B :=
              mul_le_mul_of_nonneg_left (hKb _) (abs_nonneg _)
          _ = B * ‖ψ w‖ := by rw [Real.norm_eq_abs]; ring
      exact this.mul_const (v u)
    · refine hvg.congr (Filter.Eventually.of_forall fun u => ?_)
      change |v u| * ∫ w, |ψ w| * |K (w - u)| =
        ∫ w, ‖ψ w * K (w - u) * v u‖
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      ring
  calc ∫ w, ψ w * ∫ u, K (w - u) * v u = ∫ w, ∫ u, ψ w * K (w - u) * v u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        ring
    _ = ∫ u, ∫ w, ψ w * K (w - u) * v u := (integral_integral_swap hint).symm
    _ = ∫ u, (∫ w, ψ w * K (w - u)) * v u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [integral_mul_const]

/-- **Stochastic Fubini for a jointly measurable version.**  If `Ξ` is jointly measurable and
`Ξ(·, w) = W (K(w - ·))` almost surely for every `w`, then `∫ ψ(w) Ξ(·, w) dw = W g` almost
surely, where `g(u) = ∫ ψ(w) K(w - u) dw` (which is square integrable). -/
theorem noise_pairing_ae_eq_whiteNoise_of_jointVersion
    {K ψ : SpaceTime → ℝ} {Ξ : Ω → SpaceTime → ℝ}
    (hW : IsWhiteNoise P W) (hK : Measurable K) (hKi : Integrable K) {B : ℝ}
    (hKb : ∀ z, |K z| ≤ B) (hψm : Measurable ψ) (hψ1 : Integrable ψ) (hψ2 : MemLp ψ 2)
    (hΞ : Measurable fun q : Ω × SpaceTime => Ξ q.1 q.2)
    (hΞW : ∀ w, (fun ω => Ξ ω w) =ᵐ[P] W (fun u => K (w - u))) :
    MemLp (fun u => ∫ w, ψ w * K (w - u)) 2 ∧
      (fun ω => ∫ w, ψ w * Ξ ω w) =ᵐ[P] W (fun u => ∫ w, ψ w * K (w - u)) := by
  have := hW.isProbabilityMeasure
  have hKL2 : MemLp K 2 := memLp_two_of_bounded_integrable hK hKi hKb
  have hkw : ∀ w, MemLp (fun u => K (w - u)) 2 := fun w => memLp_comp_sub_left_spaceTime hKL2 w
  have hkm : ∀ w, Measurable (fun u => K (w - u)) := fun w =>
    hK.comp (measurable_const.sub measurable_id)
  set g : SpaceTime → ℝ := fun u => ∫ w, ψ w * K (w - u) with hgdef
  have hgm : Measurable g := measurable_noiseConv hK hψm
  have hg : MemLp g 2 := (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
    (noiseConv_sq_integral_le hK hKi hKb hψm hψ2).1
  refine ⟨hg, ?_⟩
  have hΞm : ∀ w, Measurable (fun ω => Ξ ω w) := fun w =>
    hΞ.comp (measurable_id.prodMk measurable_const)
  have hΞL2 : ∀ w, MemLp (fun ω => Ξ ω w) 2 P := fun w =>
    ((whiteNoise_pairing_hasGaussianLaw hW (hkw w)).memLp_two).ae_eq (hΞW w).symm
  have hκ : ∀ w, ∫ ω, Ξ ω w ^ 2 ∂P = ∫ u, K u ^ 2 := fun w => by
    calc ∫ ω, Ξ ω w ^ 2 ∂P = ∫ ω, W (fun u => K (w - u)) ω ^ 2 ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hΞW w] with ω hω
          rw [hω]
      _ = ∫ u, K (w - u) ^ 2 := whiteNoise_pairing_sq_integral hW (hkw w)
      _ = ∫ u, K u ^ 2 := integral_sub_left_eq_self (fun u => K u ^ 2) volume w
  have hJ : JointData P ψ Ξ (∫ u, K u ^ 2) :=
    ⟨hψm, hψ1, hΞ, fun w => (hΞL2 w).integrable_sq, hκ⟩
  have hGL2 : MemLp (W g) 2 P := (whiteNoise_pairing_hasGaussianLaw hW hg).memLp_two
  have hGm : Measurable (W g) := hW.1 g hg
  have hAm := noise_A_measurable hJ
  have hAL2 : MemLp (fun ω => ∫ w, ψ w * Ξ ω w) 2 P :=
    (memLp_two_iff_integrable_sq hAm.aestronglyMeasurable).2 (noise_A_sq_integrable hJ)
  set A : Ω → ℝ := fun ω => ∫ w, ψ w * Ξ ω w with hAdef
  have hcov : ∀ w w', ∫ ω, Ξ ω w * Ξ ω w' ∂P = ∫ u, K (w - u) * K (w' - u) := fun w w' => by
    calc ∫ ω, Ξ ω w * Ξ ω w' ∂P =
          ∫ ω, W (fun u => K (w - u)) ω * W (fun u => K (w' - u)) ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hΞW w, hΞW w'] with ω h1 h2
          rw [h1, h2]
      _ = ∫ u, K (w - u) * K (w' - u) := whiteNoise_pairing_mul_integral hW (hkw w) (hkw w')
  have hcross : ∀ w, ∫ ω, Ξ ω w * W g ω ∂P = ∫ u, K (w - u) * g u := fun w => by
    calc ∫ ω, Ξ ω w * W g ω ∂P = ∫ ω, W (fun u => K (w - u)) ω * W g ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hΞW w] with ω hω
          rw [hω]
      _ = ∫ u, K (w - u) * g u := whiteNoise_pairing_mul_integral hW (hkw w) hg
  have hZL2 : MemLp (fun ω => A ω - W g ω) 2 P := hAL2.sub hGL2
  have e1 : ∀ w, ∫ ω, Ξ ω w * (A ω - W g ω) ∂P = 0 := by
    intro w
    have h1 : Integrable (fun ω => Ξ ω w * A ω) P := (hΞL2 w).integrable_mul hAL2
    have h2 : Integrable (fun ω => Ξ ω w * W g ω) P := (hΞL2 w).integrable_mul hGL2
    have hAΞ : ∫ ω, Ξ ω w * A ω ∂P = ∫ u, g u * K (w - u) := by
      calc ∫ ω, Ξ ω w * A ω ∂P = ∫ ω, A ω * Ξ ω w ∂P := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
            exact mul_comm _ _
        _ = ∫ w', ψ w' * ∫ ω, Ξ ω w' * Ξ ω w ∂P :=
            noise_mixed_fubini hJ (hΞm w) (hΞL2 w)
        _ = ∫ w', ψ w' * ∫ u, K (w' - u) * K (w - u) := by simp_rw [hcov]
        _ = ∫ u, g u * K (w - u) :=
            noise_kernel_fubini hK hKi hKb hψm hψ1 hψ2 (hkm w) (hkw w)
    calc ∫ ω, Ξ ω w * (A ω - W g ω) ∂P = ∫ ω, Ξ ω w * A ω ∂P - ∫ ω, Ξ ω w * W g ω ∂P := by
          rw [← integral_sub h1 h2]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          dsimp only
          ring
      _ = 0 := by
          rw [hAΞ, hcross]
          simp_rw [mul_comm (g _)]
          exact sub_self _
  have e2 : ∫ ω, A ω * (A ω - W g ω) ∂P = 0 := by
    have key := noise_mixed_fubini hJ (Z := fun ω => A ω - W g ω) (hAm.sub hGm) hZL2
    refine key.trans ?_
    simp only [e1, mul_zero, integral_zero]
  have e3 : ∫ ω, A ω * W g ω ∂P = ∫ u, g u * g u := by
    refine (noise_mixed_fubini hJ hGm hGL2).trans ?_
    calc ∫ w, ψ w * ∫ ω, Ξ ω w * W g ω ∂P = ∫ w, ψ w * ∫ u, K (w - u) * g u := by
          simp_rw [hcross]
      _ = ∫ u, g u * g u := noise_kernel_fubini hK hKi hKb hψm hψ1 hψ2 hgm hg
  have eG : ∫ ω, W g ω * W g ω ∂P = ∫ u, g u * g u := whiteNoise_pairing_mul_integral hW hg hg
  have hint1 : Integrable (fun ω => A ω * W g ω) P := hAL2.integrable_mul hGL2
  have hint2 : Integrable (fun ω => W g ω * W g ω) P := hGL2.integrable_mul hGL2
  have hint3 : Integrable (fun ω => A ω * (A ω - W g ω)) P := hAL2.integrable_mul hZL2
  have hzero : ∫ ω, (A ω - W g ω) ^ 2 ∂P = 0 := by
    have hrw : ∀ ω, (A ω - W g ω) ^ 2 =
        A ω * (A ω - W g ω) - (A ω * W g ω - W g ω * W g ω) := fun ω => by ring
    have hs : Integrable (fun ω => A ω * W g ω - W g ω * W g ω) P := hint1.sub hint2
    simp_rw [hrw]
    rw [integral_sub hint3 hs, integral_sub hint1 hint2, e2, e3, eG]
    ring
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - W g ω))
    hZL2.integrable_sq).1 hzero
  filter_upwards [h0] with ω hω
  have : (A ω - W g ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

end RegularityStructures.Phi43

end

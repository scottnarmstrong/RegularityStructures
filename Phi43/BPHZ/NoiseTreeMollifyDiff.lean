/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.NoiseTreeYoung
public import Phi43.BPHZ.NoiseTreeShiftIntegral

/-!
# `L²` distance between a mollification and the function

For a kernel `K` of total integral one and a bounded square-integrable `ψ`,

`∫ ((∫ ψ(w) K(w - u) dw) - ψ(u))² du ≤ ‖K‖₁ ∫ |K(s)| D(s) ds`, `D(s) = ∫ (ψ(u + s) - ψ u)² du`.

This is the weighted Cauchy-Schwarz inequality for `∫ (ψ(u + s) - ψ u) K(s) ds`, followed by
Tonelli.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {K ψ : SpaceTime → ℝ}

theorem integrable_shift_diff_sq_of_bounded (hψm : Measurable ψ)
    (hψ2 : Integrable (fun w => ψ w ^ 2)) (s : SpaceTime) :
    Integrable (fun u => (ψ (u + s) - ψ u) ^ 2) := by
  have hi' : Integrable (fun u => ψ (u + s) ^ 2) := hψ2.comp_add_right s
  exact (integral_le_of_measurable_le
    (G := fun u => (ψ (u + s) - ψ u) ^ 2) (H := fun u => 2 * ψ (u + s) ^ 2 + 2 * ψ u ^ 2)
    (((hψm.comp (measurable_id.add_const s)).sub hψm).pow_const 2)
    ((hi'.const_mul 2).add (hψ2.const_mul 2)) (fun u => sq_nonneg _)
    (fun u => by nlinarith [sq_nonneg (ψ (u + s) + ψ u)])).1

theorem integral_shift_diff_sq_le (hψm : Measurable ψ)
    (hψ2 : Integrable (fun w => ψ w ^ 2)) (s : SpaceTime) :
    ∫ u, (ψ (u + s) - ψ u) ^ 2 ≤ 4 * ∫ w, ψ w ^ 2 := by
  have hi' : Integrable (fun u => ψ (u + s) ^ 2) := hψ2.comp_add_right s
  obtain ⟨-, hle⟩ := integral_le_of_measurable_le
    (G := fun u => (ψ (u + s) - ψ u) ^ 2) (H := fun u => 2 * ψ (u + s) ^ 2 + 2 * ψ u ^ 2)
    (((hψm.comp (measurable_id.add_const s)).sub hψm).pow_const 2)
    ((hi'.const_mul 2).add (hψ2.const_mul 2)) (fun u => sq_nonneg _)
    (fun u => by nlinarith [sq_nonneg (ψ (u + s) + ψ u)])
  refine hle.trans ?_
  rw [integral_add (hi'.const_mul 2) (hψ2.const_mul 2), integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (μ := volume) (fun w => ψ w ^ 2) s]
  linarith

/-- The `L²` distance between the mollification `ψ ⋆ K̃` and `ψ`. -/
theorem noise_mollify_sub_sq_integral_le (hK : Measurable K) (hKi : Integrable K)
    (hK1 : ∫ z, K z = 1) (hψm : Measurable ψ) {Bψ : ℝ} (hψb : ∀ w, |ψ w| ≤ Bψ)
    (hψ2 : Integrable (fun w => ψ w ^ 2)) :
    Integrable (fun s => |K s| * ∫ u, (ψ (u + s) - ψ u) ^ 2) ∧
      ∫ u, ((∫ w, ψ w * K (w - u)) - ψ u) ^ 2 ≤
        (∫ z, |K z|) * ∫ s, |K s| * ∫ u, (ψ (u + s) - ψ u) ^ 2 := by
  have hB0 : 0 ≤ Bψ := (abs_nonneg _).trans (hψb 0)
  set M : ℝ := ∫ z, |K z| with hM
  have hM0 : 0 ≤ M := integral_nonneg fun z => abs_nonneg _
  have hKa : Integrable (fun s => |K s|) := hKi.norm
  have hKam : Measurable (fun s => |K s|) := hK.norm
  set D : SpaceTime → ℝ := fun s => ∫ u, (ψ (u + s) - ψ u) ^ 2 with hD
  have hD0 : ∀ s, 0 ≤ D s := fun s => integral_nonneg fun u => sq_nonneg _
  have hDle : ∀ s, D s ≤ 4 * ∫ w, ψ w ^ 2 := fun s => integral_shift_diff_sq_le hψm hψ2 s
  have hFm : Measurable (fun p : SpaceTime × SpaceTime => (ψ (p.2 + p.1) - ψ p.2) ^ 2) :=
    ((hψm.comp (measurable_snd.add measurable_fst)).sub (hψm.comp measurable_snd)).pow_const 2
  have hDm : Measurable D := hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hKD : Integrable (fun s => |K s| * D s) := by
    refine (hKa.mul_const (4 * ∫ w, ψ w ^ 2)).mono' (hKam.mul hDm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hD0 s))]
    exact mul_le_mul_of_nonneg_left (hDle s) (abs_nonneg _)
  refine ⟨hKD, ?_⟩
  -- the integrand as a convolution in the shift variable
  have hint1 : ∀ u, Integrable (fun s => ψ (u + s) * K s) := fun u => by
    refine (hKa.const_mul Bψ).mono'
      ((hψm.comp (measurable_const.add measurable_id)).mul hK).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hψb _) (abs_nonneg _)
  have hint2 : ∀ u, Integrable (fun s => ψ u * K s) := fun u => hKi.const_mul (ψ u)
  have hrep : ∀ u, (∫ w, ψ w * K (w - u)) - ψ u = ∫ s, (ψ (u + s) - ψ u) * K s := by
    intro u
    have e1 : ∫ w, ψ w * K (w - u) = ∫ s, ψ (u + s) * K s := by
      have := integral_add_left_eq_self (μ := volume) (fun w => ψ w * K (w - u)) u
      simpa [add_sub_cancel_left] using this.symm
    have e2 : ψ u = ∫ s, ψ u * K s := by rw [integral_const_mul, hK1, mul_one]
    calc (∫ w, ψ w * K (w - u)) - ψ u = (∫ s, ψ (u + s) * K s) - ∫ s, ψ u * K s := by
          rw [e1, ← e2]
      _ = ∫ s, (ψ (u + s) * K s - ψ u * K s) := (integral_sub (hint1 u) (hint2 u)).symm
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          dsimp only
          ring
  set T : SpaceTime → ℝ := fun u => ∫ s, (ψ (u + s) - ψ u) ^ 2 * |K s| with hT
  have hcs : ∀ u, (∫ s, (ψ (u + s) - ψ u) * K s) ^ 2 ≤ M * T u := by
    intro u
    have hFmeas : Measurable (fun s => ψ (u + s) - ψ u) :=
      (hψm.comp (measurable_const.add measurable_id)).sub measurable_const
    have hFb : ∀ s, |ψ (u + s) - ψ u| ≤ 2 * Bψ := fun s => by
      calc |ψ (u + s) - ψ u| ≤ |ψ (u + s)| + |ψ u| := abs_sub _ _
        _ ≤ 2 * Bψ := by linarith [hψb (u + s), hψb u]
    have hfh : Integrable (fun s => |ψ (u + s) - ψ u| * |K s|) := by
      refine (hKa.const_mul (2 * Bψ)).mono' (hFmeas.norm.mul hKam).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hFb s) (abs_nonneg _) |>.trans_eq (by ring)
    have hf2h : Integrable (fun s => |ψ (u + s) - ψ u| ^ 2 * |K s|) := by
      refine (hKa.const_mul ((2 * Bψ) ^ 2)).mono' ((hFmeas.norm.pow_const 2).mul hKam).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hFb s) 2)
        (abs_nonneg _)
    have hcs := noiseIntegral_mul_sq_le (μ := volume) (f := fun s => |ψ (u + s) - ψ u|)
      (h := fun s => |K s|) (fun _ => abs_nonneg _) hKa hfh hf2h
    have habs : |∫ s, (ψ (u + s) - ψ u) * K s| ≤ ∫ s, |ψ (u + s) - ψ u| * |K s| := by
      have := norm_integral_le_integral_norm (μ := volume)
        (fun s => (ψ (u + s) - ψ u) * K s)
      simpa [abs_mul] using this
    have hsq : (∫ s, (ψ (u + s) - ψ u) * K s) ^ 2 ≤
        (∫ s, |ψ (u + s) - ψ u| * |K s|) ^ 2 := by
      rw [← sq_abs (∫ s, (ψ (u + s) - ψ u) * K s)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine hsq.trans (hcs.trans_eq ?_)
    simp only [hT, hM, sq_abs]
  -- Tonelli
  have hprod : Integrable (Function.uncurry fun u s : SpaceTime =>
      (ψ (u + s) - ψ u) ^ 2 * |K s|) (volume.prod volume) := by
    have hmeas : Measurable (fun p : SpaceTime × SpaceTime =>
        (ψ (p.1 + p.2) - ψ p.1) ^ 2 * |K p.2|) :=
      (((hψm.comp (measurable_fst.add measurable_snd)).sub (hψm.comp measurable_fst)).pow_const 2).mul
        (hKam.comp measurable_snd)
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun s =>
        (integrable_shift_diff_sq_of_bounded hψm hψ2 s).mul_const (|K s|), ?_⟩
    refine hKD.congr (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    have : ∀ u, ‖(ψ (u + s) - ψ u) ^ 2 * |K s|‖ = (ψ (u + s) - ψ u) ^ 2 * |K s| := fun u =>
      Real.norm_of_nonneg (by positivity)
    simp only [this, hD]
    rw [integral_mul_const, mul_comm]
  have hTint : Integrable T := hprod.integral_prod_left
  have hTval : ∫ u, T u = ∫ s, |K s| * D s := by
    calc ∫ u, T u = ∫ s, ∫ u, (ψ (u + s) - ψ u) ^ 2 * |K s| := integral_integral_swap hprod
      _ = ∫ s, |K s| * D s := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          dsimp only
          rw [integral_mul_const, mul_comm]
  have hgm := measurable_noiseConv hK hψm
  obtain ⟨-, hle⟩ := integral_le_of_measurable_le
    (G := fun u => ((∫ w, ψ w * K (w - u)) - ψ u) ^ 2) (H := fun u => M * T u)
    ((hgm.sub hψm).pow_const 2) (hTint.const_mul M) (fun u => sq_nonneg _)
    (fun u => by
      rw [hrep u]
      exact hcs u)
  refine hle.trans ?_
  rw [integral_const_mul, hTval]

end RegularityStructures.Phi43

end

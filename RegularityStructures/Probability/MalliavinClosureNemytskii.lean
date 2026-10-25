/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureLpCalculus

/-!
# Bounded continuous composition in `L²`

On a finite measure space, a bounded continuous scalar map acts continuously on `L²`.  The proof
uses convergence in measure, extracts an almost-everywhere convergent subsequence from each
subsequence, and applies the bounded-majorant lemma.  This is the composition input for the
closure-level chain rule.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace RegularityStructures

theorem tendsto_Lp_comp_of_continuous_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {F₀ : α → ℝ} {φ : ℝ → ℝ}
    (hF : Tendsto (fun n => eLpNorm (F n - F₀) 2 μ) atTop (𝓝 0))
    (hφ_cont : Continuous φ)
    (hφ_bound : ∃ M : ℝ≥0, ∀ y : ℝ, ‖φ y‖₊ ≤ M)
    (hcomp : ∀ n, AEStronglyMeasurable (fun x => φ (F n x)) μ)
    (hcomp₀ : AEStronglyMeasurable (fun x => φ (F₀ x)) μ) :
    Tendsto (fun n => eLpNorm (fun x => φ (F n x) - φ (F₀ x)) 2 μ)
      atTop (𝓝 0) := by
  have hF_measure : TendstoInMeasure μ F atTop F₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
      (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.ofNat_ne_top hF
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, hms, hms_ae⟩ :=
    (hF_measure.comp hns).exists_seq_tendsto_ae
  let R : ℕ → α → ℝ := fun j x => φ (F (ns (ms j)) x) - φ (F₀ x)
  have hR_meas : ∀ j, AEStronglyMeasurable (R j) μ := by
    intro j
    dsimp [R]
    exact (hcomp (ns (ms j))).sub hcomp₀
  have hR_ae : ∀ᵐ x ∂μ, Tendsto (fun j => R j x) atTop (𝓝 0) := by
    filter_upwards [hms_ae] with x hx
    have hφx : Tendsto (fun j => φ (F (ns (ms j)) x)) atTop
        (𝓝 (φ (F₀ x))) := (hφ_cont.tendsto (F₀ x)).comp (hx)
    simpa [R] using hφx.sub_const (φ (F₀ x))
  obtain ⟨M, hM⟩ := hφ_bound
  have hR_bound : ∃ c : ℝ≥0, ∀ j, ∀ᵐ x ∂μ,
      ‖R j x‖ₑ ≤ ‖(c : ℝ) * (1 : ℝ)‖ₑ := by
    refine ⟨2 * M, fun j => Filter.Eventually.of_forall (fun x => ?_)⟩
    dsimp [R]
    calc
      ‖φ (F (ns (ms j)) x) - φ (F₀ x)‖ₑ ≤
          ‖φ (F (ns (ms j)) x)‖ₑ + ‖φ (F₀ x)‖ₑ := enorm_sub_le
      _ ≤ (M : ℝ≥0∞) + (M : ℝ≥0∞) := by
        gcongr
        · simpa [enorm_eq_nnnorm] using hM (F (ns (ms j)) x)
        · simpa [enorm_eq_nnnorm] using hM (F₀ x)
      _ = 2 * (M : ℝ≥0∞) := by rw [two_mul]
      _ = (M : ℝ≥0∞) * 2 := by rw [mul_comm]
      _ = ‖((2 * M : ℝ≥0) : ℝ) * (1 : ℝ)‖ₑ := by
        simp [enorm_eq_nnnorm, mul_comm]
  have hR_zero : Tendsto (fun j => eLpNorm (R j) 2 μ) atTop (𝓝 0) := by
    simpa [R] using
      (tendsto_Lp_zero_of_ae_tendsto_bounded_by hR_meas
        (memLp_const (p := (2 : ℝ≥0∞)) (μ := μ) (1 : ℝ)) hR_bound hR_ae)
  exact ⟨ms, by simpa [R] using hR_zero⟩

theorem tendsto_Lp_bounded_comp_mul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {F : ℕ → α → ℝ} {F₀ : α → ℝ}
    {D : ℕ → α × β → ℝ} {D₀ : α × β → ℝ} {φ : ℝ → ℝ}
    (hF_ae : ∀ᵐ p ∂(μ.prod ν),
      Tendsto (fun n => F n p.1) atTop (𝓝 (F₀ p.1)))
    (hD_tendsto : Tendsto
      (fun n => eLpNorm (D n - D₀) 2 (μ.prod ν)) atTop (𝓝 0))
    (hD₀ : MemLp D₀ 2 (μ.prod ν))
    (hφ_cont : Continuous φ)
    (hφ_bound : ∃ M : ℝ≥0, ∀ y : ℝ, ‖φ y‖₊ ≤ M)
    (hφF : ∀ n, AEStronglyMeasurable
      (fun p => φ (F n p.1)) (μ.prod ν))
    (hφF₀ : AEStronglyMeasurable
      (fun p => φ (F₀ p.1)) (μ.prod ν))
    (hD_meas : ∀ n, AEStronglyMeasurable (D n) (μ.prod ν)) :
    Tendsto
      (fun n => eLpNorm
        (fun p => φ (F n p.1) * D n p - φ (F₀ p.1) * D₀ p) 2 (μ.prod ν))
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hφ_bound
  let A : ℕ → α × β → ℝ := fun n p =>
    φ (F n p.1) * (D n p - D₀ p)
  let B : ℕ → α × β → ℝ := fun n p =>
    (φ (F n p.1) - φ (F₀ p.1)) * D₀ p
  have hA_meas : ∀ n, AEStronglyMeasurable (A n) (μ.prod ν) := by
    intro n
    dsimp [A]
    exact (hφF n).mul ((hD_meas n).sub hD₀.aestronglyMeasurable)
  have hA_bound : ∀ n,
      eLpNorm (A n) 2 (μ.prod ν) ≤
        (M : ℝ≥0∞) * eLpNorm (D n - D₀) 2 (μ.prod ν) := by
    intro n
    have hpoint : ∀ᵐ p ∂(μ.prod ν),
        ‖A n p‖ₑ ≤ ‖(M : ℝ) * (D n p - D₀ p)‖ₑ := by
      filter_upwards [] with p
      dsimp [A]
      calc
        ‖φ (F n p.1) * (D n p - D₀ p)‖ₑ =
            ‖φ (F n p.1)‖ₑ * ‖D n p - D₀ p‖ₑ := by rw [enorm_mul]
        _ ≤ (M : ℝ≥0∞) * ‖D n p - D₀ p‖ₑ := by
          gcongr
          simpa [enorm_eq_nnnorm] using hM (F n p.1)
        _ = ‖(M : ℝ) * (D n p - D₀ p)‖ₑ := by rw [enorm_mul]; simp
    have hnorm := eLpNorm_mono_enorm_ae (p := (2 : ℝ≥0∞)) (hA_meas n) hpoint
    rw [show eLpNorm (fun p => (M : ℝ) * (D n p - D₀ p)) 2 (μ.prod ν) =
        eLpNorm ((M : ℝ) • (D n - D₀)) 2 (μ.prod ν) by
      congr 1] at hnorm
    rw [eLpNorm_const_smul] at hnorm
    simpa [enorm_eq_nnnorm] using hnorm
  have hA_tendsto : Tendsto (fun n => eLpNorm (A n) 2 (μ.prod ν))
      atTop (𝓝 0) := by
    have hscale : Tendsto
        (fun n => (M : ℝ≥0∞) * eLpNorm (D n - D₀) 2 (μ.prod ν))
        atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul (a := (M : ℝ≥0∞))
        hD_tendsto (Or.inr ENNReal.coe_ne_top))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      hscale (fun _ => bot_le) hA_bound
  have hB_meas : ∀ n, AEStronglyMeasurable (B n) (μ.prod ν) := by
    intro n
    dsimp [B]
    exact ((hφF n).sub hφF₀).mul hD₀.aestronglyMeasurable
  have hB_ae : ∀ᵐ p ∂(μ.prod ν), Tendsto (fun n => B n p) atTop (𝓝 0) := by
    filter_upwards [hF_ae] with p hp
    have hφp : Tendsto (fun n => φ (F n p.1)) atTop (𝓝 (φ (F₀ p.1))) :=
      (hφ_cont.tendsto (F₀ p.1)).comp hp
    have hsub : Tendsto
        (fun n => φ (F n p.1) - φ (F₀ p.1)) atTop (𝓝 0) := by
      simpa using hφp.sub_const (φ (F₀ p.1))
    simpa [B] using hsub.mul_const (D₀ p)
  have hB_bound : ∃ c : ℝ≥0, ∀ n, ∀ᵐ p ∂(μ.prod ν),
      ‖B n p‖ₑ ≤ ‖(c : ℝ) * D₀ p‖ₑ := by
    refine ⟨2 * M, fun n => Filter.Eventually.of_forall (fun p => ?_)⟩
    dsimp [B]
    calc
      ‖(φ (F n p.1) - φ (F₀ p.1)) * D₀ p‖ₑ =
          ‖φ (F n p.1) - φ (F₀ p.1)‖ₑ * ‖D₀ p‖ₑ := by rw [enorm_mul]
      _ ≤ ((M : ℝ≥0∞) + M) * ‖D₀ p‖ₑ := by
        gcongr
        exact enorm_sub_le.trans (add_le_add
          (by simpa [enorm_eq_nnnorm] using hM (F n p.1))
          (by simpa [enorm_eq_nnnorm] using hM (F₀ p.1)))
      _ = ‖((2 * M : ℝ≥0) : ℝ) * D₀ p‖ₑ := by
        rw [enorm_mul]
        simp [enorm_eq_nnnorm, mul_comm]
        ring
  have hB_tendsto : Tendsto (fun n => eLpNorm (B n) 2 (μ.prod ν))
      atTop (𝓝 0) :=
    tendsto_Lp_zero_of_ae_tendsto_bounded_by hB_meas hD₀ hB_bound hB_ae
  have hsum_tendsto : Tendsto
      (fun n => eLpNorm (A n) 2 (μ.prod ν) + eLpNorm (B n) 2 (μ.prod ν))
      atTop (𝓝 0) := by simpa using hA_tendsto.add hB_tendsto
  have htotal_le : ∀ n,
      eLpNorm
          (fun p => φ (F n p.1) * D n p - φ (F₀ p.1) * D₀ p) 2 (μ.prod ν) ≤
        eLpNorm (A n) 2 (μ.prod ν) + eLpNorm (B n) 2 (μ.prod ν) := by
    intro n
    have heq : (fun p => φ (F n p.1) * D n p - φ (F₀ p.1) * D₀ p) =
        A n + B n := by
      funext p
      dsimp [A, B]
      ring
    rw [heq]
    exact eLpNorm_add_le (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    hsum_tendsto (fun _ => bot_le) htotal_le

end RegularityStructures

end

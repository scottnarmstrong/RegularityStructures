/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfWeightedFamily

/-!
# Weighted block-envelope moments, uniform in the probability space

The constant `M` of `exists_kernelBlockEnvelope_weightedFamily_lintegral_pow_moment_le` is chosen before
the probability space; the proof is that of the original (it never uses `P` to choose `M`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

/-- Weighted envelope moment for a finite family of polynomial weights. -/
theorem exists_kernelBlockEnvelope_weightedFamily_lintegral_pow_moment_le_uniform
    {ι : Type*} (J : Finset ι) (α : ι → ℝ) {n p : ℕ} (hp : 1 ≤ p) (hn1 : 1 < n)
    (hα : ∀ j ∈ J, 0 ≤ α j) (hn : ∀ j ∈ J, α j * p + 1 < n) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {s : ℝ}, 0 < s → ∀ (Y : Ω → ParabolicSpace → ℝ≥0∞),
      Measurable (Function.uncurry Y) → ∀ (x : ParabolicSpace) (c : ι → ℝ), (∀ j, 0 ≤ c j) →
      (∀ w : ParabolicSpace, ∫⁻ ω, Y ω w ^ p ∂P ≤
        (N : ℝ≥0∞) * ∑ j ∈ J, ENNReal.ofReal (c j * parabolicNorm (x - w) ^ α j) ^ p) →
      ∫⁻ ω, (∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) * Y ω w ∂volume) ^ p ∂P ≤
        ENNReal.ofReal (M * ∑ j ∈ J, c j * s ^ (α j / 4)) ^ p := by
  classical
  have hn1' : (1 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨M0, hM0, h0⟩ := exists_lintegral_kernelBlockEnvelope_shift_mul_rpow_le
    (n := n) (a := 0) le_rfl (by linarith)
  have hM1 : ∀ j, ∃ M1 : ℝ, 0 ≤ M1 ∧ (j ∈ J → ∀ {s : ℝ}, 0 < s → ∀ (x : ParabolicSpace) {c : ℝ},
      0 ≤ c → ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
          ENNReal.ofReal (c * parabolicNorm (x - w) ^ α j) ^ p ≤
        ENNReal.ofReal (c ^ p * (M1 * s ^ (α j * p / 4)))) := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨M1, hM1, h1⟩ := exists_lintegral_kernelBlockEnvelope_mul_ofReal_pow_le
        (n := n) (p := p) (hα j hj) (hn j hj)
      exact ⟨M1, hM1, fun _ {s} hs x {c} hc => h1 hs x hc⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose M1 hM1nn hM1b using hM1
  refine ⟨max 1 M0 * max 1 (N * J.card * ∑ j ∈ J, M1 j), by positivity,
    fun {Ω} _ {P} _ {s} hs Y hY x c hc hpoint => ?_⟩
  let K : ParabolicSpace → ℝ≥0∞ := fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x - w))
  have hK : Measurable K := (measurable_kernelBlockEnvelope_shift n hs x).ennreal_ofReal
  let m : ℝ≥0∞ := ∫⁻ w, K w ∂volume
  have hm : m ≤ ENNReal.ofReal M0 := by
    have := h0 hs x
    simpa [m, K] using this
  have hYsection : ∀ ω, AEMeasurable (Y ω) volume := fun ω =>
    (hY.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hYw : ∀ w, AEMeasurable (fun ω => Y ω w) P := fun w =>
    (hY.comp (measurable_id.prodMk measurable_const)).aemeasurable
  have hKYjoint : Measurable (Function.uncurry (fun ω w => K w * (Y ω w) ^ p)) :=
    (hK.comp measurable_snd).mul (hY.pow_const p)
  have hFmeas : Measurable (fun ω => ∫⁻ w, K w * (Y ω w) ^ p ∂volume) :=
    hKYjoint.lintegral_prod_right
  let G : ParabolicSpace → ℝ≥0∞ := fun w =>
    K w * ((N : ℝ≥0∞) * ∑ j ∈ J, ENNReal.ofReal (c j * parabolicNorm (x - w) ^ α j) ^ p)
  have hGeq : ∀ w, G w = (N : ℝ≥0∞) * ∑ j ∈ J, K w *
      ENNReal.ofReal (c j * parabolicNorm (x - w) ^ α j) ^ p := by
    intro w
    simp only [G]
    rw [mul_left_comm, Finset.mul_sum]
  have hmj : ∀ j : ι, Measurable (fun w : ParabolicSpace =>
      K w * ENNReal.ofReal (c j * parabolicNorm (x - w) ^ α j) ^ p) := fun j =>
    hK.mul ((((continuous_parabolicNorm.comp (continuous_const.sub continuous_id)).measurable.pow_const
      _).const_mul _).ennreal_ofReal.pow_const p)
  have hGint : ∫⁻ w, G w ∂volume ≤ (N : ℝ≥0∞) * ∑ j ∈ J,
      ENNReal.ofReal (c j ^ p * (M1 j * s ^ (α j * p / 4))) := by
    simp_rw [hGeq]
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hmj j),
      lintegral_finsetSum _ fun j _ => hmj j]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => hM1b j hj hs x (hc j)) zero_le
  have hswap : ∫⁻ ω, ∫⁻ w, K w * (Y ω w) ^ p ∂volume ∂P ≤ ∫⁻ w, G w ∂volume := by
    rw [lintegral_lintegral_swap hKYjoint.aemeasurable]
    refine lintegral_mono fun w => ?_
    calc ∫⁻ ω, K w * Y ω w ^ p ∂P = K w * ∫⁻ ω, Y ω w ^ p ∂P :=
          lintegral_const_mul'' (K w) ((hYw w).pow_const p)
      _ ≤ G w := mul_le_mul_of_nonneg_left (hpoint w) zero_le
  have hstoch : ∫⁻ ω, (∫⁻ w, K w * Y ω w ∂volume) ^ p ∂P ≤
      ENNReal.ofReal M0 ^ (p - 1) * ∫⁻ w, G w ∂volume := by
    calc _ ≤ ∫⁻ ω, m ^ (p - 1) * (∫⁻ w, K w * (Y ω w) ^ p ∂volume) ∂P :=
          lintegral_mono fun ω => piHalfJensen hp hK.aemeasurable (hYsection ω)
      _ = m ^ (p - 1) * ∫⁻ ω, ∫⁻ w, K w * (Y ω w) ^ p ∂volume ∂P :=
          lintegral_const_mul _ hFmeas
      _ ≤ ENNReal.ofReal M0 ^ (p - 1) * ∫⁻ w, G w ∂volume :=
          mul_le_mul' (pow_le_pow_left' hm _) hswap
  refine hstoch.trans ?_
  have hsp : ∀ j, (s ^ (α j / 4)) ^ p = s ^ (α j * p / 4) := fun j => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; congr 1; ring
  have hreal := piHalf_family_constant_le J c M1 (fun j => s ^ (α j / 4)) hp M0 hM0 N hc
    hM1nn (fun j => Real.rpow_nonneg hs.le _)
  calc ENNReal.ofReal M0 ^ (p - 1) * ∫⁻ w, G w ∂volume
      ≤ ENNReal.ofReal M0 ^ (p - 1) * ((N : ℝ≥0∞) * ∑ j ∈ J,
        ENNReal.ofReal (c j ^ p * (M1 j * s ^ (α j * p / 4)))) :=
        mul_le_mul_of_nonneg_left hGint zero_le
    _ = ENNReal.ofReal (M0 ^ (p - 1) * (N * ∑ j ∈ J, c j ^ p * (M1 j * (s ^ (α j / 4)) ^ p))) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hM0 _), ENNReal.ofReal_pow hM0,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (pow_nonneg (hc j) _)
            (mul_nonneg (hM1nn j) (pow_nonneg (Real.rpow_nonneg hs.le _) _))]
        simp_rw [hsp]
    _ ≤ ENNReal.ofReal ((max 1 M0 * max 1 (N * J.card * ∑ j ∈ J, M1 j) *
          ∑ j ∈ J, c j * s ^ (α j / 4)) ^ p) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
        rw [ENNReal.ofReal_pow (by
          refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => mul_nonneg (hc j)
            (Real.rpow_nonneg hs.le _)))]

end RegularityStructures

end

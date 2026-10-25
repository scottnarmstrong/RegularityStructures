/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfWeightedMoment

/-!
# Weighted block-envelope moments for a finite family of polynomial weights

If the pointwise `p`-th moment of `Y ω w` is bounded by `N ∑_{j ∈ J} (c_j d(x, w)^{α_j})^p`, then the
`p`-th moment of the block-envelope average of `Y` around `x` is bounded by
`(M ∑_{j ∈ J} c_j s^{α_j/4})^p`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

/-- The weight integral `∫⁻ E^n_s(x - w) (c d(x, w)^α)^p ≤ c^p M s^(α p/4)`. -/
theorem exists_lintegral_kernelBlockEnvelope_mul_ofReal_pow_le {n : ℕ} {α : ℝ} {p : ℕ}
    (hα : 0 ≤ α) (hn : α * p + 1 < n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {s : ℝ}, 0 < s → ∀ (x : ParabolicSpace) {c : ℝ}, 0 ≤ c →
      ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
          ENNReal.ofReal (c * parabolicNorm (x - w) ^ α) ^ p ≤
        ENNReal.ofReal (c ^ p * (M * s ^ (α * p / 4))) := by
  have hαp : 0 ≤ α * p := mul_nonneg hα (by positivity)
  obtain ⟨M1, hM1, h1⟩ := exists_lintegral_kernelBlockEnvelope_shift_mul_rpow_le
    (n := n) (a := α * p) hαp hn
  refine ⟨M1, hM1, fun {s} hs x c hc => ?_⟩
  have hGeq : ∀ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
      ENNReal.ofReal (c * parabolicNorm (x - w) ^ α) ^ p = ENNReal.ofReal (c ^ p) *
      (ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
        ENNReal.ofReal (parabolicNorm (x - w) ^ (α * p))) := by
    intro w
    have hd : 0 ≤ parabolicNorm (x - w) ^ α := Real.rpow_nonneg (parabolicNorm_nonneg _) _
    have e : (parabolicNorm (x - w) ^ α) ^ p = parabolicNorm (x - w) ^ (α * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (parabolicNorm_nonneg _)]
    rw [← ENNReal.ofReal_pow (mul_nonneg hc hd), mul_pow, e,
      ENNReal.ofReal_mul (pow_nonneg hc p)]
    ring
  simp_rw [hGeq]
  have hE : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x - w))) :=
    (measurable_kernelBlockEnvelope_shift n hs x).ennreal_ofReal
  have hmeasK : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
      ENNReal.ofReal (parabolicNorm (x - w) ^ (α * p))) :=
    hE.mul (((continuous_parabolicNorm.comp (continuous_const.sub continuous_id)).measurable.pow_const
      _).ennreal_ofReal)
  rw [lintegral_const_mul _ hmeasK, ENNReal.ofReal_mul (pow_nonneg hc p)]
  exact mul_le_mul_of_nonneg_left (h1 hs x) zero_le

/-- The real-number constant bookkeeping of the family moment. -/
theorem piHalf_family_constant_le {ι : Type*} (J : Finset ι) (c M1 a : ι → ℝ) {p : ℕ}
    (hp : 1 ≤ p) (M0 : ℝ) (hM0 : 0 ≤ M0) (N : ℕ) (hc : ∀ j, 0 ≤ c j) (hM1 : ∀ j, 0 ≤ M1 j)
    (ha : ∀ j, 0 ≤ a j) :
    M0 ^ (p - 1) * (N * ∑ j ∈ J, c j ^ p * (M1 j * a j ^ p)) ≤
      (max 1 M0 * max 1 (N * J.card * ∑ j ∈ J, M1 j) * ∑ j ∈ J, c j * a j) ^ p := by
  set X : ℝ := ∑ j ∈ J, c j * a j with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ha j)
  set S1 : ℝ := ∑ j ∈ J, M1 j with hS1
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun j _ => hM1 j
  have hterm : ∀ j ∈ J, c j ^ p * (M1 j * a j ^ p) ≤ S1 * X ^ p := by
    intro j hj
    have hxj : c j * a j ≤ X :=
      Finset.single_le_sum (f := fun j => c j * a j) (fun i _ => mul_nonneg (hc i) (ha i)) hj
    have hM1j : M1 j ≤ S1 := Finset.single_le_sum (f := M1) (fun i _ => hM1 i) hj
    calc c j ^ p * (M1 j * a j ^ p) = M1 j * (c j * a j) ^ p := by rw [mul_pow]; ring
      _ ≤ S1 * X ^ p :=
        mul_le_mul hM1j (pow_le_pow_left₀ (mul_nonneg (hc j) (ha j)) hxj p)
          (pow_nonneg (mul_nonneg (hc j) (ha j)) p) hS10
  have hsum : ∑ j ∈ J, c j ^ p * (M1 j * a j ^ p) ≤ J.card * (S1 * X ^ p) := by
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    simp
  set Q : ℝ := N * J.card * S1 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hA : M0 ^ (p - 1) ≤ (max 1 M0) ^ p :=
    (pow_le_pow_left₀ hM0 (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le p 1))
  have hB : Q ≤ (max 1 Q) ^ p :=
    (le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  calc M0 ^ (p - 1) * (N * ∑ j ∈ J, c j ^ p * (M1 j * a j ^ p))
      ≤ M0 ^ (p - 1) * (N * (J.card * (S1 * X ^ p))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
    _ = M0 ^ (p - 1) * (Q * X ^ p) := by rw [hQ]; ring
    _ ≤ (max 1 M0) ^ p * ((max 1 Q) ^ p * X ^ p) :=
        mul_le_mul hA (mul_le_mul_of_nonneg_right hB (pow_nonneg hX0 p)) (by positivity)
          (by positivity)
    _ = _ := by rw [mul_pow, mul_pow]; ring

end RegularityStructures

end

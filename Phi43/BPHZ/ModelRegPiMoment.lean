/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# From a second moment and moment equivalence to a `q`-th moment in `lintegral` form

For a random variable `Y` on a probability space, `q ≥ 1`, a bound `E Y² ≤ D²` and the
moment equivalence `E Y^(2q) ≤ A (E Y²)^q` (with `Y^(2q)` integrable) we get
`∫⁻ ‖Y‖ₑ^q ≤ ofReal (max 1 √A * D) ^ q`, the shape of the `i ∉ Dπ` hypothesis of the
Kolmogorov criterion.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(E |Y|^q)² ≤ E Y^(2q)` on a probability space, with `|Y|^q` integrable. -/
theorem integral_abs_pow_sq_le {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) {q : ℕ}
    (hint : Integrable (fun ω => Y ω ^ (2 * q)) P) :
    Integrable (fun ω => |Y ω| ^ q) P ∧
      (∫ ω, |Y ω| ^ q ∂P) ^ 2 ≤ ∫ ω, Y ω ^ (2 * q) ∂P := by
  have hm : AEStronglyMeasurable (fun ω => |Y ω| ^ q) P := hY.norm.pow q
  have hsq : ∀ ω, (|Y ω| ^ q) ^ 2 = Y ω ^ (2 * q) := fun ω => by
    rw [← pow_mul, mul_comm q 2, pow_mul, sq_abs, ← pow_mul]
  have hL2 : MemLp (fun ω => |Y ω| ^ q) 2 P :=
    (memLp_two_iff_integrable_sq hm).2 (hint.congr (Filter.Eventually.of_forall fun ω =>
      (hsq ω).symm))
  refine ⟨hL2.integrable one_le_two, ?_⟩
  have h := ProbabilityTheory.variance_nonneg (fun ω => |Y ω| ^ q) P
  rw [ProbabilityTheory.variance_eq_sub hL2] at h
  have e : ∫ ω, (|Y ω| ^ q) ^ 2 ∂P = ∫ ω, Y ω ^ (2 * q) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall hsq)
  simp only [Pi.pow_apply] at h
  rw [e] at h
  linarith

/-- **Second moment and moment equivalence give a `q`-th moment.** -/
theorem lintegral_enorm_pow_le_of_moments {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P)
    {q : ℕ} (hq : 1 ≤ q) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hint : Integrable (fun ω => Y ω ^ (2 * q)) P)
    (hmom : ∫ ω, Y ω ^ (2 * q) ∂P ≤ A * (∫ ω, Y ω ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, Y ω ^ 2 ∂P ≤ D ^ 2) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (max 1 (Real.sqrt A) * D) ^ q := by
  obtain ⟨hi, hE⟩ := integral_abs_pow_sq_le hY hint
  have hnn : 0 ≤ ∫ ω, |Y ω| ^ q ∂P := integral_nonneg fun ω => by positivity
  have hsecond : 0 ≤ ∫ ω, Y ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have h3 : (∫ ω, |Y ω| ^ q ∂P) ^ 2 ≤ A * (D ^ 2) ^ q :=
    hE.trans (hmom.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hsecond h2 q) hA))
  have h4 : ∫ ω, |Y ω| ^ q ∂P ≤ Real.sqrt A * D ^ q := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt hA, ← pow_mul, mul_comm q 2, pow_mul]
    exact h3
  have hK : Real.sqrt A * D ^ q ≤ (max 1 (Real.sqrt A) * D) ^ q := by
    set K := max 1 (Real.sqrt A)
    have hK1 : 1 ≤ K := le_max_left _ _
    have hKA : Real.sqrt A ≤ K := le_max_right _ _
    calc Real.sqrt A * D ^ q ≤ K * D ^ q := by gcongr
      _ ≤ K ^ q * D ^ q := by
          gcongr
          calc K = K ^ 1 := (pow_one K).symm
            _ ≤ K ^ q := pow_le_pow_right₀ hK1 hq
      _ = (K * D) ^ q := (mul_pow K D q).symm
  have hl : ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂P = ENNReal.ofReal (∫ ω, |Y ω| ^ q ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => by positivity)]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_pow (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]
  rw [hl, ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (h4.trans hK)

end RegularityStructures.Phi43

end

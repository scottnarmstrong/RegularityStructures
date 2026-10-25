/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.LpSpectralGapIteration
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder closure for the even-moment iteration

This is the Hölder estimate used after differentiating the centred power in [HS23, Remark 2.21 and
(2.8)]. The two `MemLp` hypotheses are stated explicitly so that no tail or integrability claim is
hidden in the spectral-gap theorem.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

/-- Hölder bounds the derivative cross term by the current even moment and the carré du champ. -/
theorem integral_abs_pow_mul_le_holder {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y Γ : Ω → ℝ} {q : ℕ} (hq : 2 ≤ q)
    (hY : MemLp (fun ω => |Y ω| ^ (2 * q - 2))
      (ENNReal.ofReal ((q : ℝ) / (q - 1))) P)
    (hΓ : MemLp Γ (ENNReal.ofReal (q : ℝ)) P)
    (hΓ_nonneg : 0 ≤ᵐ[P] Γ) :
    ∫ ω, |Y ω| ^ (2 * q - 2) * Γ ω ∂P ≤
      (∫ ω, |Y ω| ^ (2 * q) ∂P) ^ ((q - 1 : ℝ) / q) *
        (∫ ω, Γ ω ^ q ∂P) ^ ((1 : ℝ) / q) := by
  have hqpos : 0 < q := by omega
  have hq1pos : 0 < (q : ℝ) - 1 := by
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    linarith
  let p : ℝ := (q : ℝ) / (q - 1)
  have hpq : p.HolderConjugate (q : ℝ) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · dsimp [p]
      apply (lt_div_iff₀ hq1pos).2
      nlinarith
    · dsimp [p]
      field_simp
      ring
  have hf_nonneg : 0 ≤ᵐ[P] (fun ω => |Y ω| ^ (2 * q - 2)) :=
    Filter.Eventually.of_forall (fun ω => by positivity)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf_nonneg hΓ_nonneg hY hΓ
  have hleft : (fun ω => |Y ω| ^ (2 * q - 2) * Γ ω) =
      (fun ω => (|Y ω| ^ (2 * q - 2)) * Γ ω) := rfl
  have hfp : ∀ ω, (|Y ω| ^ (2 * q - 2)) ^ p = |Y ω| ^ (2 * q) := by
    intro ω
    dsimp [p]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg (Y ω))]
    have hqne : (q : ℝ) ≠ 0 := by positivity
    have hq1ne : (q : ℝ) - 1 ≠ 0 := ne_of_gt hq1pos
    have hcast : ((2 * q - 2 : ℕ) : ℝ) = 2 * (q : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]
      norm_num
    rw [hcast]
    rw [show (2 * (q : ℝ) - 2) * ((q : ℝ) / (q - 1)) = (2 * q : ℝ) by
      field_simp
      ]
    have hcast2 : 2 * (q : ℝ) = ((2 * q : ℕ) : ℝ) := by norm_num
    rw [hcast2, Real.rpow_natCast]
  have hleftpow :
      (∫ ω, (|Y ω| ^ (2 * q - 2)) ^ p ∂P) = ∫ ω, |Y ω| ^ (2 * q) ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hfp ω
  rw [hleftpow] at hholder
  simpa [hleft, p, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hholder

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovEstimate

/-!
# The spatial Kolmogorov moment criterion

This is the annealed-to-pathwise spatial step for the negative-order norm in
`RegularityStructures.Torus.HolderBesov`.  The decay condition is the expected
`p (α - η) > 3`; all measurability and pointwise heat-moment hypotheses are explicit.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

theorem holderBesovENorm_natMoment_le_of_pointwise {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {X : Ω → C(Torus3, ℝ)} {η α A : ℝ} {p : ℕ}
    (hη : η ≤ 0) (hp : 2 ≤ p) (hdecay : 3 < p * (α - η)) (hA : 0 ≤ A)
    (hholder : AEMeasurable (fun ω => holderBesovENorm η (X ω)) P)
    (hterm : ∀ n : ℕ,
      AEMeasurable (fun ω => dyadicHolderBesovTerm η n (X ω)) P)
    (hjoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      AEMeasurable
        (fun z : Ω × Torus3 =>
          ‖heatSemigroup r (X z.1) z.2‖ₑ ^ p) (P.prod volume))
    (hpoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ y : Torus3,
      ∫⁻ ω, ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2))) :
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤
      ENNReal.ofReal (kolmogorovHolderBesovConstant p α η * A ^ p) := by
  have hp0 : p ≠ 0 := by omega
  have hp1 : 1 < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  let q : ℝ := (p : ℝ) / ((p : ℝ) - 1)
  have hpq : (p : ℝ).HolderConjugate q := by
    dsimp [q]
    exact .conjExponent hp1
  let b : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal ((dyadicScale n) ^ (-η * p / 2) *
      (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
        (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))))
  have hdyadic :
      ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤ ∑' n, b n := by
    apply holderBesovENorm_natMoment_le_of_dyadic hη hp0 hholder hterm
    intro n
    dsimp [b]
    exact dyadicHolderBesovTerm_lintegral_pow_le hpq hjoint hpoint n
  let D : ℝ := heatKernelScaleConstant * (dyadicScale 2) ^ ((α * p - 3) / 2)
  have hδ : 0 < (p : ℝ) * (α - η) - 3 := by linarith
  have hq_nonneg : 0 ≤ (2 : ℝ) ^ (-(p * (α - η) - 3) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hq_lt : (2 : ℝ) ^ (-(p * (α - η) - 3) / 2) < 1 := by
    apply (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
    exact Or.inr (Or.inl ⟨by norm_num, by linarith⟩)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg heatKernelScaleConstant_nonneg
      (Real.rpow_nonneg (dyadicScale_pos 2).le _)
  have hDA : 0 ≤ D * A ^ p := mul_nonneg hD (pow_nonneg hA p)
  have hgeom :
      ∀ n : ℕ, b n =
        ENNReal.ofReal (D * A ^ p) *
          (ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2))) ^ n := by
    intro n
    have hreal :
        (dyadicScale n) ^ (-η * p / 2) *
            (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
              (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))) =
          D * A ^ p * ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by
      calc
        (dyadicScale n) ^ (-η * p / 2) *
              (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
                (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2))) =
            ((dyadicScale n) ^ (-η * p / 2) *
              (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
                (dyadicScale (n + 2)) ^ (α * p / 2))) * A ^ p := by ring
        _ = (D * ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n) * A ^ p := by
          rw [dyadicHeatPower_eq_geometric (p := p) (α := α) (η := η) n]
        _ = D * A ^ p * ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by ring
    dsimp [b]
    rw [hreal, ENNReal.ofReal_mul hDA, ENNReal.ofReal_pow hq_nonneg]
  calc
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤ ∑' n, b n := hdyadic
    _ = ENNReal.ofReal (D * A ^ p) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)))⁻¹ := by
      rw [show (fun n : ℕ => b n) =
          (fun n : ℕ => ENNReal.ofReal (D * A ^ p) *
            (ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2))) ^ n) by
        funext n
        exact hgeom n]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (D * A ^ p) *
        ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(p * (α - η) - 3) / 2))⁻¹) := by
      have hsub : (1 : ℝ≥0∞) -
          ENNReal.ofReal ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) =
          ENNReal.ofReal (1 - (2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) hq_nonneg]
      rw [hsub, ENNReal.ofReal_inv_of_pos (sub_pos.mpr hq_lt)]
    _ = ENNReal.ofReal (kolmogorovHolderBesovConstant p α η * A ^ p) := by
      rw [← ENNReal.ofReal_mul hDA]
      congr 1
      dsimp [kolmogorovHolderBesovConstant, D]
      ring

end RegularityStructures

end

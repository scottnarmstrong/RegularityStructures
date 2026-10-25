/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovReverseWeights
public import RegularityStructures.Torus.HolderBesovInverseHeatOperator

/-!
# Equivalence of the heat and periodic Littlewood--Paley norms

Exact heat reconstruction, annular multiplier decay and geometric summation give the heat-to-LP
bound. Combining it with the inverse-heat multiplier bound gives both inequalities with one common
positive constant. This proves the equivalence (`holderBesovENorm_equiv_littlewoodPaley`) of the
Littlewood--Paley norm with the heat norm (2.3) of the statement.
-/

public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace RegularityStructures

private theorem enorm_heat_complexify (g : C(Torus3, ℝ)) :
    ‖(⟨fun x : Torus3 => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ : C(Torus3, ℂ))‖ₑ = ‖g‖ₑ := by
  rw [ContinuousMap.enorm_eq_iSup_enorm, ContinuousMap.enorm_eq_iSup_enorm]
  apply iSup_congr
  intro x
  change ‖(g x : ℂ)‖ₑ = ‖g x‖ₑ
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]

private theorem enorm_heatOp_le_zero_add_tail {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ)) :
    ‖PDE.heatOp s f‖ₑ ≤ ‖PDE.heatOp s (torusLittlewoodPaleyBlock 0 f)‖ₑ +
      ∑' n : ℕ, ‖PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f)‖ₑ := by
  have ht := (tendsto_sum_heatOp_torusLittlewoodPaleyBlock hs f).enorm
  rw [enorm_heat_complexify] at ht
  apply le_of_tendsto ht
  filter_upwards [] with N
  apply (enorm_sum_le (Finset.range (N + 1))
    (fun j : ℕ => PDE.heatOp s (torusLittlewoodPaleyBlock j f))).trans
  rw [Finset.sum_range_succ', add_comm]
  exact add_le_add le_rfl (ENNReal.sum_le_tsum (Finset.range N))

theorem holderBesovENorm_le_torusLittlewoodPaleyENorm (η : ℝ) (hη : η < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(Torus3, ℝ),
      holderBesovENorm η f ≤ ENNReal.ofReal C * torusLittlewoodPaleyENorm η f := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-η / 2)
  have hgap : 0 < 2 * (M : ℝ) + η := by linarith only [hM]
  obtain ⟨K, hK, htail⟩ := tsum_enorm_heatOp_torusLittlewoodPaleyBlock_tail_le η hη M hgap
  refine ⟨1 + K, add_pos_of_pos_of_nonneg zero_lt_one hK, fun f => ?_⟩
  refine iSup₂_le fun s hs => ?_
  have h0 : ‖PDE.heatOp s (torusLittlewoodPaleyBlock 0 f)‖ₑ ≤ torusLittlewoodPaleyENorm η f := by
    apply (enorm_le_iff_norm_le.mpr (PDE.norm_heatOp_le s _)).trans
    simpa only [Nat.cast_zero, zero_mul, neg_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul] using
      enorm_torusLittlewoodPaleyBlock_le_ENorm η f 0
  have hscale : 1 ≤ s ^ (η / 2) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2
      (show η / 2 ≤ (0 : ℝ) by linarith only [hη])
  have h0' : ‖PDE.heatOp s (torusLittlewoodPaleyBlock 0 f)‖ₑ ≤
      ENNReal.ofReal (s ^ (η / 2)) * torusLittlewoodPaleyENorm η f := by
    apply h0.trans
    have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (s ^ (η / 2)) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hscale
    simpa only [one_mul] using mul_le_mul' he (le_refl (torusLittlewoodPaleyENorm η f))
  have hheat : ‖PDE.heatOp s f‖ₑ ≤ ENNReal.ofReal ((1 + K) * s ^ (η / 2)) *
      torusLittlewoodPaleyENorm η f := by
    apply (enorm_heatOp_le_zero_add_tail hs.1 f).trans
    apply (add_le_add h0' (htail s hs.1 hs.2 f)).trans_eq
    rw [← add_mul, ← ENNReal.ofReal_add (Real.rpow_nonneg hs.1.le _)
      (mul_nonneg hK (Real.rpow_nonneg hs.1.le _))]
    congr 2
    ring
  have hop : (⨆ x : Torus3, ‖heatSemigroup s f x‖ₑ) = ‖PDE.heatOp s f‖ₑ := by
    rw [ContinuousMap.enorm_eq_iSup_enorm]
    exact iSup_congr fun x => congrArg (fun a : ℝ => ‖a‖ₑ) (PDE.heatOp_eq_heatSemigroup hs.1 f x).symm
  change ENNReal.ofReal (s ^ (-η / 2)) * (⨆ x : Torus3, ‖heatSemigroup s f x‖ₑ) ≤ _
  rw [hop]
  apply (mul_le_mul' le_rfl hheat).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
  have he : s ^ (-η / 2) * ((1 + K) * s ^ (η / 2)) = 1 + K := by
    calc
      _ = (1 + K) * (s ^ (-η / 2) * s ^ (η / 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hs.1]
        have hexp : -η / 2 + η / 2 = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_one]
  rw [he]

theorem holderBesovENorm_equiv_littlewoodPaley (η : ℝ) (hη : η < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(Torus3, ℝ),
      holderBesovENorm η f ≤ ENNReal.ofReal C * torusLittlewoodPaleyENorm η f ∧
      torusLittlewoodPaleyENorm η f ≤ ENNReal.ofReal C * holderBesovENorm η f := by
  obtain ⟨A, hA, hheat⟩ := holderBesovENorm_le_torusLittlewoodPaleyENorm η hη
  obtain ⟨B, _hB, hLP⟩ := torusLittlewoodPaleyENorm_le_holderBesovENorm η
  refine ⟨max A B, hA.trans_le (le_max_left _ _), fun f => ⟨?_, ?_⟩⟩
  · exact (hheat f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  · exact (hLP f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl)

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.HolderContraction
public import RegularityStructures.PDE.Duhamel

/-!
# The `𝒞^η` norm of a Duhamel integral

For `0 ≤ t ≤ 1`, a continuous path `h` and a bound `‖h r‖_η ≤ D` on `[0, t]`, one has
`‖duhamel h t‖_η ≤ D` (`holderBesovENorm_duhamel_le`).  The proof commutes `P_τ` with the interval
integral and uses `‖P_τ h r‖_∞ ≤ τ^{η/2} ‖h r‖_η`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures

/-- A bound `‖P_τ g‖_∞ ≤ τ^{η/2} N` for all `τ ∈ (0, 1]` bounds the `𝒞^η` norm by `N`. -/
theorem holderBesovENorm_le_of_norm_heatOp_le (η : ℝ) {N : ℝ} (g : C(Torus3, ℝ))
    (h : ∀ τ ∈ Ioc (0 : ℝ) 1, ‖PDE.heatOp τ g‖ ≤ τ ^ (η / 2) * N) :
    holderBesovENorm η g ≤ ENNReal.ofReal N := by
  refine iSup₂_le fun τ hτ => ?_
  have h1 : ⨆ x, ‖heatSemigroup τ g x‖ₑ ≤ ENNReal.ofReal (‖PDE.heatOp τ g‖) := by
    refine iSup_le fun x => ?_
    rw [← PDE.heatOp_eq_heatSemigroup hτ.1, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ContinuousMap.norm_coe_le_norm _ x)
  have hp : 0 ≤ τ ^ (-η / 2) := Real.rpow_nonneg hτ.1.le _
  have e : τ ^ (-η / 2) * (τ ^ (η / 2) * N) = N := by
    rw [← mul_assoc, ← Real.rpow_add hτ.1, show -η / 2 + η / 2 = 0 by ring, Real.rpow_zero,
      one_mul]
  calc ENNReal.ofReal (τ ^ (-η / 2)) * ⨆ x, ‖heatSemigroup τ g x‖ₑ
      ≤ ENNReal.ofReal (τ ^ (-η / 2)) * ENNReal.ofReal (‖PDE.heatOp τ g‖) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal (τ ^ (-η / 2) * ‖PDE.heatOp τ g‖) := (ENNReal.ofReal_mul hp).symm
    _ ≤ ENNReal.ofReal N := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc τ ^ (-η / 2) * ‖PDE.heatOp τ g‖ ≤ τ ^ (-η / 2) * (τ ^ (η / 2) * N) :=
              mul_le_mul_of_nonneg_left (h τ hτ) hp
          _ = N := e

/-- `P_τ` commutes with the Duhamel integral. -/
theorem heatOp_duhamel {h : ℝ → C(Torus3, ℝ)} (hh : Continuous h) {τ : ℝ} (hτ : 0 ≤ τ) {t : ℝ}
    (ht : 0 ≤ t) :
    PDE.heatOp τ (PDE.duhamel h t) = PDE.duhamel (fun r => PDE.heatOp τ (h r)) t := by
  unfold PDE.duhamel
  have := (PDE.heatOpCLM (E := ℝ) τ).intervalIntegral_comp_comm
    (PDE.intervalIntegrable_duhamel_integrand hh t 0 t)
  simp only [PDE.heatOpCLM_apply] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht] at hr
  simp only
  rw [PDE.heatOp_heatOp (sub_nonneg.2 hr.2) hτ, PDE.heatOp_heatOp hτ (sub_nonneg.2 hr.2),
    add_comm]

/-- **The `𝒞^η` norm of a Duhamel integral** on `[0, 1]`. -/
theorem holderBesovENorm_duhamel_le (η : ℝ) {h : ℝ → C(Torus3, ℝ)} (hh : Continuous h) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {D : ℝ≥0∞} (hD : ∀ r ∈ Icc 0 t, holderBesovENorm η (h r) ≤ D) :
    holderBesovENorm η (PDE.duhamel h t) ≤ D := by
  rcases eq_or_ne D ⊤ with rfl | hDt
  · exact le_top
  obtain ⟨N, hN, rfl⟩ : ∃ N : ℝ, 0 ≤ N ∧ D = ENNReal.ofReal N :=
    ⟨D.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hDt).symm⟩
  refine (holderBesovENorm_le_of_norm_heatOp_le η _ (N := N * t) fun τ hτ => ?_).trans ?_
  · rw [heatOp_duhamel hh hτ.1.le ht.1]
    have hc : Continuous fun r => PDE.heatOp τ (h r) := (continuous_const.heatOp hh)
    have := PDE.norm_duhamel_le_mul hc ht.1 (M := τ ^ (η / 2) * N) fun r hr =>
      Potential.norm_heatOp_le_of_holderBesovENorm_le η hτ hN (hD r hr)
    calc _ ≤ τ ^ (η / 2) * N * t := this
      _ = τ ^ (η / 2) * (N * t) := by ring
  · exact ENNReal.ofReal_le_ofReal (by nlinarith [ht.2])

end RegularityStructures.Phi43.LocalLipschitz

end

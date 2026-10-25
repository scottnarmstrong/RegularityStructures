/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.TruncIdentity
public import Phi43.Potential.CutoffIBP
public import Phi43.Potential.HolderContraction
public import Phi43.Potential.KernelTail

/-!
# The potential part `χ G_m ∗ f` of `K ∗ f`, bounded by the `𝒞^η` norm of `ψ`

For `0 < u ≤ 1` and `x ∈ T³`, with the lag cutoff `χ = potCutoff` (`χ(0) = 1`, `χ = 0` for
lags `≥ 1/4`),

  `|∫_{s-1/4}^{s} χ(s-r) e^{-(s-r)} (P_{u+s-r} f_r)(x) dr| ≤ 2 u^{η/2} N`

whenever `‖ψ(r)‖_η ≤ N` for `r ∈ [s - 1/4, s]` (`abs_integral_cutoff_potF_le`).  Proof: integrate by
parts in `r` against the cutoff (`abs_integral_cutoff_le`); the antiderivative is, by the truncated
identity `integral_potF_Ioc`, `P_u ψ(s) - e^{-(s-r)} P_{u+s-r} ψ(r)`, which is bounded using the
contraction `‖P_τ g‖_∞ ≤ ‖g‖_∞` and `‖P_u g‖_∞ ≤ u^{η/2} ‖g‖_η`.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral

namespace RegularityStructures.Potential

open RegularityStructures

theorem contDiff_potCutoff_sub (s : ℝ) : ContDiff ℝ 1 fun r => potCutoff (s - r) :=
  (contDiff_potCutoff.comp (contDiff_const.sub contDiff_id)).of_le (by exact_mod_cast le_top)

theorem monotone_potCutoff_sub (s : ℝ) : Monotone fun r => potCutoff (s - r) := fun a b hab =>
  Real.smoothTransition.monotone (by linarith)

/-- **The potential part, bounded by the `𝒞^η` norm of `ψ`.** -/
theorem abs_integral_cutoff_potF_le {f : SpaceTime → ℝ} (hF : PotForcing f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) (η s : ℝ) {u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) 1) (x : Torus3) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ r) ≤ ENNReal.ofReal N) :
    |∫ r in (s - 1 / 4)..s, potCutoff (s - r) * PDE.heatOp u (potF hF.cont s r) x| ≤
      2 * (u ^ (η / 2) * N) := by
  set Λ : C(Torus3, ℝ) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ x).comp (PDE.heatOpCLM (E := ℝ) u) with hΛ
  have hΛapp : ∀ g : C(Torus3, ℝ), Λ g = PDE.heatOp u g x := fun g => rfl
  have hg : Continuous fun r => Λ (potF hF.cont s r) :=
    Λ.continuous.comp (continuous_potF hF.cont s)
  have hbound : ∀ r ∈ Icc (s - 1 / 4) s,
      |∫ t in r..s, Λ (potF hF.cont s t)| ≤ 2 * (u ^ (η / 2) * N) := by
    intro r hr
    have hrs : r ≤ s := hr.2
    have hint : IntegrableOn (potF hF.cont s) (Ioc r s) :=
      (continuous_potF hF.cont s).integrableOn_Ioc
    have h1 : ∫ t in r..s, Λ (potF hF.cont s t) = Λ (∫ t in Ioc r s, potF hF.cont s t) := by
      rw [intervalIntegral.integral_of_le hrs, Λ.integral_comp_comm hint]
    rw [h1, integral_potF_Ioc hF hψ hrs, map_sub, map_smul]
    have q0 : ‖PDE.heatOp u (ψ s)‖ ≤ u ^ (η / 2) * N :=
      norm_heatOp_le_of_holderBesovENorm_le η hu hN (hψN s ⟨by linarith, le_rfl⟩)
    have q1 : ‖PDE.heatOp u (ψ r)‖ ≤ u ^ (η / 2) * N :=
      norm_heatOp_le_of_holderBesovENorm_le η hu hN (hψN r hr)
    have e1 : |Λ (ψ s)| ≤ u ^ (η / 2) * N := by
      rw [hΛapp]; exact (Real.norm_eq_abs _ ▸ ContinuousMap.norm_coe_le_norm _ x).trans q0
    have e2 : |Λ (PDE.heatOp (s - r) (ψ r))| ≤ u ^ (η / 2) * N := by
      rw [hΛapp, PDE.heatOp_heatOp (sub_nonneg.2 hrs) hu.1.le, add_comm,
        ← PDE.heatOp_heatOp hu.1.le (sub_nonneg.2 hrs)]
      refine (Real.norm_eq_abs _ ▸ ContinuousMap.norm_coe_le_norm _ x).trans
        ((PDE.norm_heatOp_le _ _).trans q1)
    have hex : Real.exp (-(s - r)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : 0 ≤ u ^ (η / 2) * N := mul_nonneg (Real.rpow_nonneg hu.1.le _) hN
    calc |Λ (ψ s) - Real.exp (-(s - r)) • Λ (PDE.heatOp (s - r) (ψ r))|
        ≤ |Λ (ψ s)| + |Real.exp (-(s - r)) • Λ (PDE.heatOp (s - r) (ψ r))| := abs_sub _ _
      _ ≤ u ^ (η / 2) * N + u ^ (η / 2) * N := by
          refine add_le_add e1 ?_
          rw [smul_eq_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc Real.exp (-(s - r)) * |Λ (PDE.heatOp (s - r) (ψ r))|
              ≤ 1 * (u ^ (η / 2) * N) :=
                mul_le_mul hex e2 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = _ := by ring
  have key := abs_integral_cutoff_le (by linarith : s - 1 / 4 ≤ s) hg (contDiff_potCutoff_sub s)
    (by simpa using potCutoff_eq_zero (t := 1 / 4) le_rfl)
    (by simpa using potCutoff_eq_one (t := 0) (by norm_num)) (monotone_potCutoff_sub s) hbound
  simpa [hΛapp] using key

end RegularityStructures.Potential

end

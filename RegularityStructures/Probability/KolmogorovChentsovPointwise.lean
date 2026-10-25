/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovBorelCantelli
public import RegularityStructures.Probability.KolmogorovChentsovScale
public import RegularityStructures.Probability.KolmogorovChentsovSupremum

/-!
# Almost-sure convergence of dyadic approximants

For each fixed time, the moment estimate and first Borel--Cantelli imply that
the values on the dyadic skeleton converge almost surely to the original
value.  The proof uses only ENNReal integrals and works for an arbitrary
measure space.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem ae_tendsto_dyadicApprox_of_moment_bound
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    {P : Measure Ω} {X : UnitInterval → Ω → E}
    {p : ℕ} {q : ℝ} {M : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 0 < q) (hM : M ≠ ∞) (t : UnitInterval)
    (hmeas : ∀ s u, AEMeasurable (fun ω => edist (X s ω) (X u ω)) P)
    (hpair : ∀ s u, ∫⁻ ω, edist (X s ω) (X u ω) ^ p ∂P ≤
      M * edist s u ^ q) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X (dyadicApprox n t) ω) atTop
      (𝓝 (X t ω)) := by
  have hp0 : p ≠ 0 := by omega
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    edist (X (dyadicApprox n t) ω) (X t ω) ^ p
  let ε : ℕ → ℝ≥0∞ := fun n => (dyadicBase n) ^ (q / 2)
  let b : ℕ → ℝ≥0∞ := fun n => M * (dyadicBase n) ^ (q / 2)
  have hlevel : ∀ n, P {ω | ε n ≤ F n ω} ≤ b n := by
    intro n
    have hbase : dyadicBase n ≠ 0 := (dyadicBase_pos n).ne'
    have hbase_top : dyadicBase n ≠ ∞ := dyadicBase_ne_top n
    have heps_pos : 0 < ε n := by
      dsimp [ε]
      exact ENNReal.rpow_pos (dyadicBase_pos n) hbase_top
    have heps_top : ε n ≠ ∞ := by
      dsimp [ε]
      exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hbase_top).ne
    have hmark := meas_ge_le_lintegral_div
      ((hmeas (dyadicApprox n t) t).pow_const p)
      (show ε n ≠ 0 from heps_pos.ne') heps_top
    have hdist : edist (dyadicApprox n t) t ≤ dyadicBase n := by
      rw [← ofReal_inv_two_pow n]
      simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, dist_comm] using
        edist_dyadicApprox_le n t
    have hI : ∫⁻ ω, F n ω ∂P ≤ M * (dyadicBase n) ^ q := by
      dsimp [F]
      exact (hpair (dyadicApprox n t) t).trans <| by
        gcongr
    have hquot : (M * (dyadicBase n) ^ q) / ε n = b n := by
      dsimp [b, ε]
      rw [mul_div_assoc]
      rw [← ENNReal.rpow_sub _ _ hbase hbase_top]
      congr 2
      ring
    calc
      P {ω | ε n ≤ F n ω} ≤ (∫⁻ ω, F n ω ∂P) / ε n := by
        exact hmark
      _ ≤ (M * (dyadicBase n) ^ q) / ε n := by gcongr
      _ = b n := hquot
  have hsum_base : (∑' n : ℕ, (dyadicBase n) ^ (q / 2)) ≠ ∞ :=
    dyadicBase_rpow_tsum_ne_top (by linarith)
  have hsum : (∑' n : ℕ, b n) ≠ ∞ := by
    dsimp [b]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hM hsum_base
  have hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, F n ω < ε n :=
    ae_eventually_lt_of_summable_level_bound hlevel hsum
  let a : ℝ := q / (2 * (p : ℝ))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hupper : Tendsto (fun n : ℕ => (dyadicBase n) ^ a) atTop
      (𝓝 (0 : ℝ≥0∞)) := by
    rw [show (fun n : ℕ => (dyadicBase n) ^ a) =
        (fun n : ℕ => (((2 : ℝ≥0∞)⁻¹) ^ a) ^ n) by
      funext n; exact dyadicBase_rpow_eq_geometric n]
    apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    exact ENNReal.rpow_lt_one (by norm_num) ha
  filter_upwards [hev] with ω hω
  have hbound : ∀ᶠ n in atTop,
      edist (X (dyadicApprox n t) ω) (X t ω) <
        (dyadicBase n) ^ a := by
    filter_upwards [hω] with n hn
    apply (ENNReal.pow_lt_pow_left_iff hp0).mp
    rw [show ((dyadicBase n) ^ a) ^ p =
        (dyadicBase n) ^ (q / 2) by
      calc
        ((dyadicBase n) ^ a) ^ p =
            ((dyadicBase n) ^ a) ^ (p : ℝ) :=
          (ENNReal.rpow_natCast _ p).symm
        _ = (dyadicBase n) ^ (a * (p : ℝ)) :=
          (ENNReal.rpow_mul _ _ _).symm
        _ = (dyadicBase n) ^ (q / 2) := by
          congr 1
          dsimp [a]
          field_simp]
    exact hn
  have hdist_zero : Tendsto
      (fun n => edist (X (dyadicApprox n t) ω) (X t ω)) atTop
      (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Filter.Eventually.of_forall fun _ => bot_le)
      (hbound.mono fun _ h => h.le)
  simpa only [tendsto_iff_edist_tendsto_0] using hdist_zero

end RegularityStructures

end

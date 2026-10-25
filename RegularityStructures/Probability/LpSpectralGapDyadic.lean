/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.LpSpectralGapHolder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Dyadic `L^p` spectral-gap iteration

Applying the variance gap to successive powers gives the exponents `p = 2^(k+1)`, exactly the
iteration of [HS23, Remark 2.21 and (2.8)]. This module proves that iteration for an abstract
centred random variable. The cylindrical white-noise module supplies the power-variance estimate and
the explicit `MemLp` hypotheses.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

/-- Convert a root inequality into its corresponding natural-power moment inequality. -/
theorem lp_root_bound_to_moment {p : ℕ} (hp : 0 < p) {I J C : ℝ}
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hroot : I ^ (1 / (p : ℝ)) ≤ C * J ^ (1 / (p : ℝ))) :
    I ≤ C ^ p * J := by
  have hIroot : (I ^ (1 / (p : ℝ))) ^ p = I := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
    rw [show (1 / (p : ℝ)) * (p : ℝ) = 1 by field_simp]
    exact Real.rpow_one I
  have hJroot : (J ^ (1 / (p : ℝ))) ^ p = J := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ]
    rw [show (1 / (p : ℝ)) * (p : ℝ) = 1 by field_simp]
    exact Real.rpow_one J
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot p
  calc
    I = (I ^ (1 / (p : ℝ))) ^ p := hIroot.symm
    _ ≤ (C * J ^ (1 / (p : ℝ))) ^ p := hpow
    _ = C ^ p * J := by rw [mul_pow, hJroot]

/-- Dyadic moment bounds from the power-variance estimate and Hölder closure. -/
theorem lp_spectral_gap_dyadic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y Γ : Ω → ℝ}
    (hY_meas : AEStronglyMeasurable Y P)
    (_hY_integrable : ∀ r : ℕ, Integrable (fun ω => |Y ω| ^ r) P)
    (hY_memLp_two : ∀ r : ℕ, MemLp (fun ω => Y ω ^ r) 2 P)
    (_hΓ_integrable : ∀ r : ℕ, Integrable (fun ω => Γ ω ^ r) P)
    (hY_zero : ∫ ω, Y ω ∂P = 0)
    (hΓ_nonneg : 0 ≤ᵐ[P] Γ)
    (hvariance : ∀ q : ℕ, 1 ≤ q →
      Var[(fun ω => Y ω ^ q); P] ≤
        (q : ℝ) ^ 2 * ∫ ω, |Y ω| ^ (2 * q - 2) * Γ ω ∂P)
    (hholder : ∀ q : ℕ, 2 ≤ q →
      ∫ ω, |Y ω| ^ (2 * q - 2) * Γ ω ∂P ≤
        (∫ ω, |Y ω| ^ (2 * q) ∂P) ^ ((q - 1 : ℝ) / q) *
          (∫ ω, Γ ω ^ q ∂P) ^ ((1 : ℝ) / q))
    (hΓ_square : ∀ r : ℕ,
      (∫ ω, Γ ω ^ r ∂P) ^ 2 ≤ ∫ ω, Γ ω ^ (2 * r) ∂P) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      C ≤ 2 * ((2 ^ (k + 1) : ℕ) : ℝ) ^ 2 ∧
      (∫ ω, |Y ω| ^ (2 ^ (k + 1)) ∂P) ≤
        C ^ (2 ^ (k + 1)) * (∫ ω, Γ ω ^ (2 ^ k) ∂P) := by
  intro k
  induction k with
  | zero =>
      have hvar := hvariance 1 (by omega)
      have hvar' :
          ∫ ω, Y ω ^ 2 ∂P ≤ ∫ ω, Γ ω ∂P := by
        have hvar1 : Var[Y; P] ≤ ∫ ω, |Y ω| ^ 0 * Γ ω ∂P := by
          simpa [pow_one] using hvar
        rw [variance_eq_integral hY_meas.aemeasurable, hY_zero] at hvar1
        simpa [pow_two, abs_sq] using hvar1
      refine ⟨1, by norm_num, by norm_num, ?_⟩
      simpa using hvar'
  | succ k ih =>
      rcases ih with ⟨C, hC, hCbound, hprev⟩
      let q : ℕ := 2 ^ (k + 1)
      have hq : 2 ≤ q := by
        dsimp [q]
        have hkpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
        calc
          2 = 1 * 2 := by omega
          _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 hkpow
          _ = 2 ^ (k + 1) := by rw [pow_succ]
      have hqhalf : q / 2 = 2 ^ k := by
        dsimp [q]
        rw [pow_succ]
        simp [Nat.mul_comm]
      have hmean_abs :
          |∫ ω, Y ω ^ q ∂P| ≤ ∫ ω, |Y ω| ^ q ∂P := by
        simpa [abs_pow] using
          (abs_integral_le_integral_abs (f := fun ω => Y ω ^ q) (μ := P))
      have hmean_sq :
          (∫ ω, Y ω ^ q ∂P) ^ 2 ≤
            (∫ ω, |Y ω| ^ q ∂P) ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (integral_nonneg fun ω => by positivity)).2 hmean_abs
      have hprev' :
          (∫ ω, |Y ω| ^ q ∂P) ≤ C ^ q *
            (∫ ω, Γ ω ^ (q / 2) ∂P) := by
        simpa [q, hqhalf] using hprev
      have hΓsq := hΓ_square (q / 2)
      have hmean :
          (∫ ω, Y ω ^ q ∂P) ^ 2 ≤ C ^ (2 * q) *
            (∫ ω, Γ ω ^ q ∂P) := by
        have hCpow : 0 ≤ C ^ q := by positivity
        have hprev_sq := mul_self_le_mul_self (by positivity : 0 ≤
          ∫ ω, |Y ω| ^ q ∂P) hprev'
        have hCsq : (C ^ q) ^ 2 = C ^ (2 * q) := by
          rw [← pow_mul, Nat.mul_comm]
        have hqeq : 2 * (q / 2) = q := by
          dsimp [q]
          rw [pow_succ]
          simp [Nat.mul_comm]
        rw [hqeq] at hΓsq
        have hJnonneg : 0 ≤ ∫ ω, Γ ω ^ (q / 2) ∂P := by
          apply integral_nonneg_of_ae
          filter_upwards [hΓ_nonneg] with ω hω
          exact pow_nonneg hω _
        have hprev_sq' :
            (∫ ω, |Y ω| ^ q ∂P) ^ 2 ≤
              (C ^ q * (∫ ω, Γ ω ^ (q / 2) ∂P)) ^ 2 := by
          simpa [pow_two] using hprev_sq
        have hC2q : 0 ≤ C ^ (2 * q) := by positivity
        calc
          (∫ ω, Y ω ^ q ∂P) ^ 2 ≤ (∫ ω, |Y ω| ^ q ∂P) ^ 2 := hmean_sq
          _ ≤ (C ^ q * (∫ ω, Γ ω ^ (q / 2) ∂P)) ^ 2 := hprev_sq'
          _ = C ^ (2 * q) * (∫ ω, Γ ω ^ (q / 2) ∂P) ^ 2 := by
            rw [mul_pow, hCsq]
          _ ≤ C ^ (2 * q) * (∫ ω, Γ ω ^ q ∂P) := by
            exact mul_le_mul_of_nonneg_left hΓsq hC2q
      have hvar := hvariance q (by omega)
      have hvar' :
          (∫ ω, |Y ω| ^ (2 * q) ∂P) - (∫ ω, Y ω ^ q ∂P) ^ 2 ≤
            (q : ℝ) ^ 2 * ∫ ω, |Y ω| ^ (2 * q - 2) * Γ ω ∂P := by
        have hleft : (∫ ω, |Y ω| ^ (2 * q) ∂P) =
            ∫ ω, (Y ω ^ q) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          calc
            |Y ω| ^ (2 * q) = |Y ω| ^ (q + q) := by congr 1; omega
            _ = |Y ω ^ q| ^ 2 := by
              rw [abs_pow, ← pow_mul]
              congr 1
              omega
            _ = (Y ω ^ q) ^ 2 := by rw [sq_abs]
        rw [variance_eq_sub (hY_memLp_two q)] at hvar
        rw [hleft]
        exact hvar
      have hcross := hholder q hq
      have hstep := lp_power_step hq
        (hI := integral_nonneg fun ω => by positivity)
        (hJ := by
          apply integral_nonneg_of_ae
          filter_upwards [hΓ_nonneg] with ω hω
          exact pow_nonneg (by simpa using hω) _)
        (hD := hC) hmean hvar' hcross
      let Cnext : ℝ := 3 * (C + (q : ℝ))
      have hroot :
          (∫ ω, |Y ω| ^ (2 * q) ∂P) ^ (1 / (2 * q : ℝ)) ≤
            Cnext * (∫ ω, Γ ω ^ q ∂P) ^ (1 / (2 * q : ℝ)) := by
        simpa [Cnext] using hstep
      have hroot' :
          (∫ ω, |Y ω| ^ (2 * q) ∂P) ^ (1 / ((2 * q : ℕ) : ℝ)) ≤
            Cnext * (∫ ω, Γ ω ^ q ∂P) ^ (1 / ((2 * q : ℕ) : ℝ)) := by
        simpa [Nat.cast_mul] using hroot
      have hmoment := lp_root_bound_to_moment
        (p := 2 * q)
        (I := ∫ ω, |Y ω| ^ (2 * q) ∂P)
        (J := ∫ ω, Γ ω ^ q ∂P)
        (C := Cnext) (by omega)
        (hI := integral_nonneg fun ω => by positivity)
        (hJ := by
          apply integral_nonneg_of_ae
          filter_upwards [hΓ_nonneg] with ω hω
          exact pow_nonneg (by simpa using hω) _)
        hroot'
      have hqcast : (q : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) := by
        rfl
      have hCbound' : C ≤ 2 * q ^ 2 := by
        simpa [hqcast] using hCbound
      have hqreal : 2 ≤ (q : ℝ) := by
        exact_mod_cast hq
      have hnextbound : Cnext ≤
          2 * ((2 ^ (Nat.succ k + 1) : ℕ) : ℝ) ^ 2 := by
        dsimp [Cnext]
        have hpow : (2 ^ (Nat.succ k + 1) : ℕ) = 2 * q := by
          dsimp [q]
          have he : Nat.succ k + 1 = (k + 1) + 1 := by omega
          rw [he, pow_succ]
          simp [Nat.mul_comm]
        rw [hpow]
        norm_num at hCbound' ⊢
        nlinarith
      refine ⟨Cnext, by dsimp [Cnext]; positivity, hnextbound, ?_⟩
      simpa [q, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmoment

end RegularityStructures

end

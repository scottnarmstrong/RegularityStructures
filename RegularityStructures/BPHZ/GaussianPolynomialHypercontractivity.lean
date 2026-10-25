/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialEnergyStep

/-!
# Dimension-free equivalence of moments for Gaussian polynomials

For every `m` and `k` there is a constant `A` such that for all `n` and every polynomial `f` in `n`
variables of total degree at most `m`,
`E[f^(2^(k+1))] ≤ A (E[f²])^(2^k)` under the standard Gaussian measure
(`exists_integral_eval_pow_le_of_totalDegree_le`).

The proof uses the tower `E_j = ∑ |∂^j f|²` of iterated gradient energies, which satisfies
`E_j = 0` for `j > m`, `E[E_j] ≤ m^j E[f²]` (reverse Poincaré), and `M_j = E[E_j^q] ≤ c + β M_{j+1}`
for `q = 2^(k+1)` (one step of the dyadic spectral gap), so a downward induction in `j` bounds
`M_1 ≤ A_m (E f²)^q`.  The dyadic spectral gap for `f` itself then bounds the `2q`-th moment of
`f - E f` by `M_1`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The recursive bound for the tower of moments: `A 0 = 0`, `A (d + 1) = c + β A d`. -/
def momentTowerSeq (c β : ℝ) : ℕ → ℝ
  | 0 => 0
  | d + 1 => c + β * momentTowerSeq c β d

end RegularityStructures

end

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

theorem momentTowerSeq_nonneg {c β : ℝ} (hc : 0 ≤ c) (hβ : 0 ≤ β) :
    ∀ d : ℕ, 0 ≤ momentTowerSeq c β d
  | 0 => le_rfl
  | d + 1 => by
    have := momentTowerSeq_nonneg hc hβ d
    simp only [momentTowerSeq]
    positivity

private lemma integral_gaussExp_sq (f : MvPolynomial (Fin n) ℝ) :
    gaussExp (f * f) = ∫ x, eval x f ^ 2 ∂(standardGaussianMeasure n) := by
  unfold gaussExp
  simp_rw [map_mul, sq]

/-- The downward induction on the order of the derivative. -/
theorem integral_towerEnergy_pow_le (k : ℕ) {m : ℕ} {f : MvPolynomial (Fin n) ℝ}
    (hf : f.totalDegree ≤ m) :
    ∀ d j : ℕ, m + 1 ≤ j + d →
      ∫ x, eval x (towerEnergy f j) ^ (2 ^ (k + 1)) ∂(standardGaussianMeasure n) ≤
        momentTowerSeq (2 * (2 ^ (2 ^ (k + 1) - 1) * (((m : ℝ) + 1) ^ (m + 1)) ^ (2 ^ (k + 1))))
          (momentStepConst k) d *
        (∫ x, eval x f ^ 2 ∂(standardGaussianMeasure n)) ^ (2 ^ (k + 1)) := by
  set q : ℕ := 2 ^ (k + 1) with hq
  set S : ℝ := ∫ x, eval x f ^ 2 ∂(standardGaussianMeasure n) with hS
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  set c : ℝ := 2 * (2 ^ (q - 1) * (((m : ℝ) + 1) ^ (m + 1)) ^ q) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hβ0 := momentStepConst_nonneg k
  have hzero : ∀ j : ℕ, m < j →
      ∫ x, eval x (towerEnergy f j) ^ q ∂(standardGaussianMeasure n) = 0 := fun j hj => by
    rw [towerEnergy_eq_zero_of_lt hf hj]
    have hq0 : q ≠ 0 := by rw [hq]; positivity
    simp [hq0]
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [hzero j (by omega)]
    simp [momentTowerSeq]
  | succ d ih =>
    intro j hj
    by_cases hmj : m < j
    · rw [hzero j hmj]
      have := momentTowerSeq_nonneg hc0 hβ0 (d + 1)
      positivity
    · have hjm : j ≤ m := by omega
      have hmean : gaussExp (sqSum (derivTower f j)) ≤ ((m : ℝ) + 1) ^ (m + 1) * S := by
        have h1 := gaussExp_towerEnergy_le hf j
        rw [integral_gaussExp_sq] at h1
        have h2 : (m : ℝ) ^ j ≤ ((m : ℝ) + 1) ^ (m + 1) := by
          calc (m : ℝ) ^ j ≤ ((m : ℝ) + 1) ^ j :=
                pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) j
            _ ≤ ((m : ℝ) + 1) ^ (m + 1) :=
                pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (by omega)
        exact h1.trans (mul_le_mul_of_nonneg_right h2 hS0)
      have hstep := integral_pow_sqSum_le k (derivTower f j) _ hmean
      have hnext := ih (j + 1) (by omega)
      have hmq : (((m : ℝ) + 1) ^ (m + 1) * S) ^ q = (((m : ℝ) + 1) ^ (m + 1)) ^ q * S ^ q :=
        mul_pow _ _ _
      rw [hmq] at hstep
      calc ∫ x, eval x (towerEnergy f j) ^ q ∂(standardGaussianMeasure n)
          ≤ 2 * (2 ^ (q - 1) * ((((m : ℝ) + 1) ^ (m + 1)) ^ q * S ^ q)) +
            momentStepConst k * ∫ x, eval x (towerEnergy f (j + 1)) ^ q
              ∂(standardGaussianMeasure n) := hstep
        _ ≤ 2 * (2 ^ (q - 1) * ((((m : ℝ) + 1) ^ (m + 1)) ^ q * S ^ q)) +
            momentStepConst k * (momentTowerSeq c (momentStepConst k) d * S ^ q) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hnext hβ0) _
        _ = momentTowerSeq c (momentStepConst k) (d + 1) * S ^ q := by
          simp only [momentTowerSeq, hc]; ring

/-- **Dimension-free equivalence of moments for Gaussian polynomials.**  The constant `A` depends
only on the degree bound `m` and the exponent `2 ^ (k + 1)`, not on the number of variables
`n` or on the polynomial `f`. -/
theorem exists_integral_eval_pow_le_of_totalDegree_le (m k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f.totalDegree ≤ m →
      ∫ x, (MvPolynomial.eval x f) ^ (2 ^ (k + 1)) ∂(standardGaussianMeasure n) ≤
        A * (∫ x, (MvPolynomial.eval x f) ^ 2 ∂(standardGaussianMeasure n)) ^ (2 ^ k) := by
  cases k with
  | zero => exact ⟨1, zero_le_one, fun n f _ => by simp⟩
  | succ k =>
    set q : ℕ := 2 ^ (k + 1) with hq
    set Q : ℕ := 2 ^ (k + 1 + 1) with hQdef
    have hQ : Q = 2 * q := by rw [hQdef, hq, pow_succ]; ring
    set c : ℝ := 2 * (2 ^ (q - 1) * (((m : ℝ) + 1) ^ (m + 1)) ^ q) with hc
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hβ0 := momentStepConst_nonneg k
    set Am : ℝ := momentTowerSeq c (momentStepConst k) m with hAm
    have hAm0 : 0 ≤ Am := momentTowerSeq_nonneg hc0 hβ0 m
    set K2 : ℝ := (2 * ((Q : ℕ) : ℝ) ^ 2) ^ Q with hK2
    refine ⟨2 ^ (Q - 1) * (K2 * Am + 1), by positivity, fun n f hf => ?_⟩
    set S : ℝ := ∫ x, eval x f ^ 2 ∂(standardGaussianMeasure n) with hS
    set c0 : ℝ := ∫ x, eval x f ∂(standardGaussianMeasure n) with hc0def
    have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
    have hH2 := integral_abs_sub_mean_pow_le f (k + 1)
    rw [← hQdef, ← hc0def] at hH2
    have hM1 := integral_towerEnergy_pow_le k hf m 1 (by omega)
    rw [← hc, ← hq, ← hS] at hM1
    have hce : (fun x : Fin n → ℝ => coordinateEnergy (fun y : Fin n → ℝ => eval y f) x ^
        2 ^ (k + 1)) = fun x => eval x (towerEnergy f 1) ^ q := by
      funext x
      rw [coordinateEnergy_eval_eq_sqSum]
      rfl
    rw [hce] at hH2
    have hc0sq : c0 ^ 2 ≤ S := sq_integral_le_integral_sq_eval f
    have hcq : |c0| ^ Q ≤ S ^ q := by
      have heven : Even Q := ⟨q, by omega⟩
      rw [heven.pow_abs, hQ, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hc0sq q
    have hpt : ∀ x : Fin n → ℝ, eval x f ^ Q ≤
        2 ^ (Q - 1) * (|eval x f - c0| ^ Q + S ^ q) := fun x => by
      have heven : Even Q := ⟨q, by omega⟩
      have h1 : |eval x f| ≤ |eval x f - c0| + |c0| := by
        have := abs_sub_abs_le_abs_sub (eval x f) c0
        linarith
      calc eval x f ^ Q = |eval x f| ^ Q := (heven.pow_abs _).symm
        _ ≤ (|eval x f - c0| + |c0|) ^ Q := pow_le_pow_left₀ (abs_nonneg _) h1 Q
        _ ≤ 2 ^ (Q - 1) * (|eval x f - c0| ^ Q + |c0| ^ Q) :=
            add_pow_le (abs_nonneg _) (abs_nonneg _) Q
        _ ≤ 2 ^ (Q - 1) * (|eval x f - c0| ^ Q + S ^ q) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hcq _) (by positivity)
    have hint_abs : Integrable (fun x => |eval x f - c0| ^ Q) (standardGaussianMeasure n) := by
      have := integrable_abs_pow_eval (f - C c0) Q
      simp only [map_sub, eval_C] at this
      exact this
    have hint_f : Integrable (fun x => eval x f ^ Q) (standardGaussianMeasure n) := by
      simpa using integrable_eval_standardGaussianMeasure (f ^ Q)
    have hint_r : Integrable (fun x => 2 ^ (Q - 1) * (|eval x f - c0| ^ Q + S ^ q))
        (standardGaussianMeasure n) := (hint_abs.add (integrable_const _)).const_mul _
    calc ∫ x, eval x f ^ Q ∂(standardGaussianMeasure n)
        ≤ ∫ x, 2 ^ (Q - 1) * (|eval x f - c0| ^ Q + S ^ q) ∂(standardGaussianMeasure n) :=
          integral_mono hint_f hint_r hpt
      _ = 2 ^ (Q - 1) * (∫ x, |eval x f - c0| ^ Q ∂(standardGaussianMeasure n) + S ^ q) := by
          rw [integral_const_mul, integral_add hint_abs (integrable_const _)]
          simp
      _ ≤ 2 ^ (Q - 1) * (K2 * (Am * S ^ q) + S ^ q) := by
          refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (by positivity)
          exact hH2.trans (mul_le_mul_of_nonneg_left hM1 (by positivity))
      _ = 2 ^ (Q - 1) * (K2 * Am + 1) * S ^ q := by ring

end RegularityStructures

end

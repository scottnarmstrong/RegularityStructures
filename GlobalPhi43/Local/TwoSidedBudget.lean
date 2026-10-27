/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastExtension

/-! A constant selected before all data in the final time-order assembly. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open scoped BigOperators

def largePairFactor (η γ : ℝ) : ℝ :=
  1 / (2 * η) ^ γ + 3 * ((1 + η ^ γ) / η) / (2 * η) ^ (γ - 1)

def twoSidedFactor {I : Type*} (A : Finset I) (β : I → ℝ) (η γ : ℝ) : ℝ :=
  1 + largePairFactor η γ +
    (1 + largePairFactor η γ) * (1 + (Real.sqrt 2) ^ γ) +
      ∑ i ∈ A, (Real.sqrt 2) ^ (γ - β i)

theorem twoSidedFactor_pos {I : Type*} (A : Finset I) (β : I → ℝ)
    {η γ : ℝ} (hη : 0 < η) : 0 < twoSidedFactor A β η γ := by
  unfold twoSidedFactor largePairFactor
  positivity

/-- The large-pair allowance is bounded by a factor depending only on η,γ. -/
theorem largePairBudget_le_factor {η γ B Q M : ℝ} (hη : 0 < η)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hM : 0 ≤ M) :
    largePairBudget η γ B Q ≤ largePairFactor η γ * (B + Q + M) := by
  have hb : B ≤ B + Q + M := by linarith
  have hq : Q ≤ B + Q + M := by linarith
  have hn : B + Q * η ^ γ ≤ (B + Q + M) * (1 + η ^ γ) := by
    nlinarith [mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hη.le γ)]
  unfold largePairBudget largePairFactor
  calc
    _ ≤ (B + Q + M) / (2 * η) ^ γ +
        3 * (((B + Q + M) * (1 + η ^ γ)) / η) / (2 * η) ^ (γ - 1) := by
      exact add_le_add (div_le_div_of_nonneg_right hb (by positivity))
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hη.le) (by norm_num))
          (by positivity))
    _ = _ := by ring

/-- All three time-order/distance allowances share a single preselected
factor multiplying precisely the sum of existing data budgets. -/
theorem two_sided_budget_le {I : Type*} (A : Finset I) (β : I → ℝ)
    {η γ B Q M : ℝ} (hη : 0 < η) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hM : 0 ≤ M) :
    max (largePairBudget η γ B Q)
      (max Q (max Q (largePairBudget η γ B Q) * (1 + (Real.sqrt 2) ^ γ) +
        M * ∑ i ∈ A, (Real.sqrt 2) ^ (γ - β i))) ≤
      twoSidedFactor A β η γ * (B + Q + M) := by
  let D := B + Q + M
  let k := largePairFactor η γ
  let F := 1 + (Real.sqrt 2) ^ γ
  let S := ∑ i ∈ A, (Real.sqrt 2) ^ (γ - β i)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hk : 0 ≤ k := by dsimp [k, largePairFactor]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg 2) _
  have hq : Q ≤ D := by dsimp [D]; linarith
  have hm : M ≤ D := by dsimp [D]; linarith
  have hl : largePairBudget η γ B Q ≤ k * D := largePairBudget_le_factor hη hB hQ hM
  have hpast : max Q (largePairBudget η γ B Q) ≤ (1 + k) * D := by
    apply max_le
    · nlinarith
    · nlinarith
  have hfut : max Q (largePairBudget η γ B Q) * F + M * S ≤ ((1 + k) * F + S) * D := by
    nlinarith [mul_le_mul_of_nonneg_right hpast hF, mul_le_mul_of_nonneg_right hm hS]
  change max _ (max Q (max Q _ * F + M * S)) ≤ (1 + k + (1 + k) * F + S) * D
  have hFD : 0 ≤ (1 + k) * F * D :=
    mul_nonneg (mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hk) hF) hD
  have hSD := mul_nonneg hS hD
  have hkD := mul_nonneg hk hD
  apply max_le
  · nlinarith
  · apply max_le
    · nlinarith
    · nlinarith

end GlobalPhi43.Local

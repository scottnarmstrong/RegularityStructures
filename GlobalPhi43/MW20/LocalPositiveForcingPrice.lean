module

public import GlobalPhi43.MW20.LocalPositiveWeightedForcing

/-! A fixed loss-dependent price for the actual formal one-point allowance.
The constant is selected before the source fields and every radius. -/

@[expose] public noncomputable section

namespace GlobalPhi43.MW20

open RegularityStructures

def localPositiveP2Allowance (ε M S c : ℝ) : ℝ :=
  (4 : ℝ)^(3/2-5*ε)*sourceOnePointUniformBudget ε M S c

def localPositiveP2Constant (ε : ℝ) : ℝ :=
  1+(4 : ℝ)^(3/2-5*ε)*smallScaleForcingConstant ε*(1+sourceOnePointWeightConstant ε)

theorem localPositiveP2Constant_pos {ε : ℝ} (hsmall : ε < 1/14) :
    0 < localPositiveP2Constant ε := by
  have hC := smallScaleForcingConstant_nonneg hsmall
  have hW := sourceOnePointWeightConstant_nonneg ε
  unfold localPositiveP2Constant
  positivity

theorem localPositiveP2Allowance_nonneg {ε M S c : ℝ}
    (hsmall : ε < 1/14) (hM : 0 ≤ M) (hS : 0 ≤ S) (hc : 0 ≤ c) :
    0 ≤ localPositiveP2Allowance ε M S c :=
  mul_nonneg (by positivity) (sourceOnePointUniformBudget_nonneg hsmall hM hS hc)

theorem localPositiveP2Allowance_price {ε M S c : ℝ}
    (hsmall : ε < 1/14) (hM : 0 ≤ M) (hS : 0 ≤ S) (hc : 0 ≤ c) :
    localPositiveP2Allowance ε M S c ≤ localPositiveP2Constant ε*(M+c*(S+M)) := by
  let W := sourceOnePointWeightConstant ε
  have hW : 0 ≤ W := sourceOnePointWeightConstant_nonneg ε
  have hA : 0 ≤ M+c*(S+M) := by positivity
  have hC := smallScaleForcingConstant_nonneg hsmall
  have hb : M+c*W*(S+M) ≤ (1+W)*(M+c*(S+M)) := by
    nlinarith only [mul_nonneg hW hM, mul_nonneg hc (add_nonneg hS hM)]
  unfold localPositiveP2Allowance sourceOnePointUniformBudget localPositiveP2Constant
  have hh := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by positivity : 0 ≤ (4 : ℝ)^(3/2-5*ε)) hC)
  dsimp only [W] at hh
  nlinarith only [hh, hA]

end GlobalPhi43.MW20

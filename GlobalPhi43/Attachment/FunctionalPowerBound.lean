module

public import Phi43.Structure.Symbols
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Seventh-power bounds for the tree functional. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures.Phi43

/-- A uniform cubic input bound gives the source seventh-power bound for every root
whose denominator is at least 1/2-kappa. This covers all tree leaves and all three defects. -/
theorem cubic_root_le_seventh (κ : Kappa) {A R x p : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hx : 0 ≤ x)
    (hp : (1/2 : ℝ) - κ.1 ≤ p) (hbudget : x ≤ A * (1 + R) ^ 3) :
    x ^ p⁻¹ ≤ (1 + A) ^ (((1/2 : ℝ) - κ.1)⁻¹) * (1 + R) ^ (7 : ℝ) := by
  let b := (1/2 : ℝ) - κ.1
  have hs := κ.2.2
  have hb : 0 < b := by dsimp [b]; linarith only [hs]
  have hbp : b ≤ p := hp
  have hpp : 0 < p := hb.trans_le hbp
  have hq : p⁻¹ ≤ b⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hb hbp
  have hdegree : 3 / b < 7 := by
    apply (div_lt_iff₀ hb).mpr
    dsimp [b]
    linarith only [hs]
  have h7 : 3 * p⁻¹ ≤ 7 := by
    rw [div_eq_mul_inv] at hdegree
    linarith only [hq, hdegree]
  have hupper : x ≤ (1 + A) * (1 + R) ^ 3 :=
    hbudget.trans (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A) (by positivity))
  have hpow : ((1 + R) ^ 3) ^ p⁻¹ = (1 + R) ^ (3 * p⁻¹) := by
    rw [← Real.rpow_natCast (1 + R) 3, ← Real.rpow_mul (by positivity : 0 ≤ 1 + R)]
    norm_num
  calc x ^ p⁻¹ ≤ ((1 + A) * (1 + R) ^ 3) ^ p⁻¹ :=
      Real.rpow_le_rpow hx hupper (inv_nonneg.mpr hpp.le)
    _ = (1 + A) ^ p⁻¹ * (1 + R) ^ (3 * p⁻¹) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 1 + A) (by positivity : 0 ≤ (1 + R) ^ 3), hpow]
    _ ≤ (1 + A) ^ b⁻¹ * (1 + R) ^ (7 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by linarith) hq)
        (Real.rpow_le_rpow_of_exponent_le (by linarith) h7) (by positivity) (by positivity)

/-- Extended-real version, with a finite cubic bound paying all root finiteness.
This arithmetic lemma does not assume a finite value for the input norm. -/
theorem cubic_root_ENNReal_le_seventh (κ : Kappa) {A R p : ℝ} {x : ENNReal}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hp : (1/2 : ℝ) - κ.1 ≤ p)
    (hbudget : x ≤ ENNReal.ofReal (A * (1 + R) ^ 3)) :
    x ^ p⁻¹ ≤ ENNReal.ofReal ((1 + A) ^ (((1/2 : ℝ) - κ.1)⁻¹) * (1 + R) ^ (7 : ℝ)) := by
  have hb : 0 < (1/2 : ℝ) - κ.1 := by linarith only [κ.2.2]
  have hpp : 0 < p := hb.trans_le hp
  have hn : 0 ≤ A * (1 + R) ^ 3 := by positivity
  calc x ^ p⁻¹ ≤ ENNReal.ofReal (A * (1 + R) ^ 3) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hbudget (inv_nonneg.mpr hpp.le)
    _ = ENNReal.ofReal ((A * (1 + R) ^ 3) ^ p⁻¹) :=
      ENNReal.ofReal_rpow_of_nonneg hn (inv_nonneg.mpr hpp.le)
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (cubic_root_le_seventh κ hA hR hn hp le_rfl)

end GlobalPhi43.Attachment

module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic

/-! Conditional polynomial assembly of the cover, functional and slice rows.
Every quantity remains extended-valued, with the analytic estimates as hypotheses. -/

public noncomputable section

open RegularityStructures
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- One finite coefficient, determined before all fields, starts and initial data. -/
@[expose] def majorantCoefficient (C K H : ℝ≥0) : ℝ≥0 := 4*C + 2*C*K + 2*H

theorem majorant_rows_le (C K H : ℝ≥0) {M X Y : ℝ≥0∞}
    (hM : M ≤ (K : ℝ≥0∞) * (1+X)^7) :
    2*(C : ℝ≥0∞)*max 2 M + (H : ℝ≥0∞)*(Y+(1+X)^3) ≤
      (majorantCoefficient C K H : ℝ≥0∞)*(1+X+Y)^7 := by
  let Q : ℝ≥0∞ := 1+X+Y
  have h1 : 1 ≤ Q := le_self_add.trans le_self_add
  have hx : 1+X ≤ Q := le_self_add
  have hy : Y ≤ Q := le_add_self
  have hp1 : 1 ≤ Q^7 := one_le_pow₀ h1
  have hp : Q ≤ Q^7 := by simpa only [pow_one] using pow_le_pow_right' h1 (by decide : 1 ≤ 7)
  have hx7 : (1+X)^7 ≤ Q^7 := pow_le_pow_left' hx 7
  have hx3 : (1+X)^3 ≤ Q^7 :=
    (pow_le_pow_left' hx 3).trans (pow_le_pow_right' h1 (by decide : 3 ≤ 7))
  have hm : M ≤ (K : ℝ≥0∞)*Q^7 := hM.trans (by gcongr)
  have hmax : max 2 M ≤ (2+(K : ℝ≥0∞))*Q^7 := by
    calc max 2 M ≤ 2+M := max_le le_self_add le_add_self
      _ ≤ 2*Q^7+(K : ℝ≥0∞)*Q^7 := add_le_add (by simpa only [mul_one, one_mul, mul_comm] using mul_le_mul_left hp1 2) hm
      _ = _ := by ring
  have hslice : Y+(1+X)^3 ≤ 2*Q^7 := by
    calc _ ≤ Q^7+Q^7 := add_le_add (hy.trans hp) hx3
      _ = _ := by ring
  calc _ ≤ 2*(C : ℝ≥0∞)*((2+(K : ℝ≥0∞))*Q^7) + (H : ℝ≥0∞)*(2*Q^7) := by gcongr
    _ = (majorantCoefficient C K H : ℝ≥0∞)*Q^7 := by simp only [majorantCoefficient]; push_cast; ring

/-- Conditional norm application: cover in sup norm, slice at the SAME eta, and
functional control imply the fixed seventh-power norm estimate. -/
theorem majorant_norm_of_rows (η : ℝ) (hη : η ≤ 0) (C K H : ℝ≥0)
    (u J : C(Torus3, ℝ)) (w M X Y : ℝ≥0∞)
    (hcover : w*‖u-J‖ₑ ≤ 2*(C : ℝ≥0∞)*max 2 M)
    (hfunctional : M ≤ (K : ℝ≥0∞)*(1+X)^7)
    (hslice : w*holderBesovENorm η J ≤ (H : ℝ≥0∞)*(Y+(1+X)^3)) :
    w*holderBesovENorm η u ≤ (majorantCoefficient C K H : ℝ≥0∞)*(1+X+Y)^7 := by
  have hadd : holderBesovENorm η u ≤ holderBesovENorm η (u-J) + holderBesovENorm η J := by
    simpa only [sub_add_cancel] using holderBesovENorm_add_le η (u-J) J
  have hsup := holderBesovENorm_le hη (u-J)
  have hsupw : w * holderBesovENorm η (u-J) ≤ w * ‖u-J‖ₑ := by
    simpa only [mul_comm] using mul_le_mul_left hsup w
  calc _ ≤ w*(holderBesovENorm η (u-J)+holderBesovENorm η J) := by gcongr
    _ = w*holderBesovENorm η (u-J)+w*holderBesovENorm η J := mul_add _ _ _
    _ ≤ 2*(C : ℝ≥0∞)*max 2 M+(H : ℝ≥0∞)*(Y+(1+X)^3) :=
      add_le_add (hsupw.trans hcover) hslice
    _ ≤ _ := majorant_rows_le C K H hfunctional

end GlobalPhi43.Attachment

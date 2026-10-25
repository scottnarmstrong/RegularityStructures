/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.PDE.Semigroup
public import RegularityStructures.PDE.HeatOpBridge

/-!
# The heat semigroup on the completion `𝒞^η`

For `t > 0`, `f ↦ P_t f` is Lipschitz from `(C(T³), ‖·‖_η)` to the supremum norm, with constant
`(min t 1)^{η/2}`: for `t ≤ 1` this is the definition of `‖f‖_η`, and for `t > 1` use
`P_t = P_{t-1} P_1`. Hence it extends to the completion `HolderBesov η`:
`heatExt η a t : C(T³)` is `P_t a` (and `0` for `t ≤ 0`). It is additive, bounded by
`(min t 1)^{η/2} ‖a‖_η`, agrees with `heatSemigroup t` on `toHolderBesov η f`, and satisfies the
semigroup law `P_s (P_t a) = P_{s+t} a`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- `P_t` as an additive map on the seminormed group `HolderBesovPre η` (`t` is arbitrary; only
`t > 0` is used). -/
def heatPre (η : NegExponent) (t : ℝ) : HolderBesovPre η →+ C(Torus3, ℝ) where
  toFun f := heatOp t (show C(Torus3, ℝ) from f)
  map_zero' := heatOp_zero_right t
  map_add' f g := heatOp_add t (show C(Torus3, ℝ) from f) (show C(Torus3, ℝ) from g)

end RegularityStructures.Datum

end

public section

open MeasureTheory Set

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem heatPre_apply (η : NegExponent) (t : ℝ) (f : HolderBesovPre η) :
    heatPre η t f = heatOp t (show C(Torus3, ℝ) from f) := rfl

/-- `‖P_t f‖_∞ ≤ t^{η/2} ‖f‖_η` for `0 < t ≤ 1`: the definition of `‖f‖_η`. -/
theorem norm_heatOp_le_of_le_one (η : NegExponent) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (f : C(Torus3, ℝ)) :
    ‖heatOp t f‖ ≤ t ^ ((η : ℝ) / 2) * (holderBesovENorm η f).toReal := by
  have hE := holderBesovENorm_lt_top η.2.le f
  have hpow : 0 ≤ t ^ ((η : ℝ) / 2) := Real.rpow_nonneg ht0.le _
  refine (ContinuousMap.norm_le _ (mul_nonneg hpow ENNReal.toReal_nonneg)).2 fun x => ?_
  have h1 : ENNReal.ofReal (t ^ (-(η : ℝ) / 2)) * ‖heatSemigroup t f x‖ₑ ≤ holderBesovENorm η f := by
    calc ENNReal.ofReal (t ^ (-(η : ℝ) / 2)) * ‖heatSemigroup t f x‖ₑ
        ≤ ENNReal.ofReal (t ^ (-(η : ℝ) / 2)) * ⨆ x, ‖heatSemigroup t f x‖ₑ :=
          mul_le_mul_right (le_iSup (fun x => ‖heatSemigroup t f x‖ₑ) x) _
      _ ≤ holderBesovENorm η f :=
          le_iSup₂ (f := fun s (_ : s ∈ Ioc (0 : ℝ) 1) =>
            ENNReal.ofReal (s ^ (-(η : ℝ) / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ) t ⟨ht0, ht1⟩
  have h2 := ENNReal.toReal_mono hE.ne h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht0.le _),
    toReal_enorm] at h2
  rw [heatOp_eq_heatSemigroup ht0 f x, Real.norm_eq_abs]
  have h3 : t ^ ((η : ℝ) / 2) * t ^ (-(η : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add ht0]
    have : (η : ℝ) / 2 + -(η : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  calc |heatSemigroup t f x| = t ^ ((η : ℝ) / 2) * (t ^ (-(η : ℝ) / 2) * ‖heatSemigroup t f x‖) := by
        rw [← mul_assoc, h3, one_mul, Real.norm_eq_abs]
    _ ≤ t ^ ((η : ℝ) / 2) * (holderBesovENorm η f).toReal :=
        mul_le_mul_of_nonneg_left h2 hpow

/-- `‖P_t f‖_∞ ≤ (min t 1)^{η/2} ‖f‖_η` for all `t > 0`. -/
theorem norm_heatOp_le_holder (η : NegExponent) {t : ℝ} (ht0 : 0 < t) (f : C(Torus3, ℝ)) :
    ‖heatOp t f‖ ≤ (min t 1) ^ ((η : ℝ) / 2) * (holderBesovENorm η f).toReal := by
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1]
    exact norm_heatOp_le_of_le_one η ht0 ht1 f
  · rw [min_eq_right (not_le.1 ht1).le, Real.one_rpow, one_mul]
    have h1 := norm_heatOp_le_of_le_one η one_pos le_rfl f
    rw [Real.one_rpow, one_mul] at h1
    have e : heatOp t f = heatOp (t - 1) (heatOp 1 f) := by
      rw [heatOp_heatOp one_pos.le (sub_pos.2 (not_le.1 ht1)).le, add_sub_cancel]
    rw [e]
    exact (norm_heatOp_le _ _).trans h1

end RegularityStructures.Datum

end

public section

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- `‖f‖_η` as a real number (the norm on `HolderBesovPre η`). -/
theorem norm_holderBesovPre (η : NegExponent) (f : HolderBesovPre η) :
    ‖f‖ = (holderBesovENorm η (show C(Torus3, ℝ) from f)).toReal := rfl

theorem continuous_heatPre (η : NegExponent) {t : ℝ} (ht : 0 < t) : Continuous (heatPre η t) := by
  refine AddMonoidHomClass.continuous_of_bound (heatPre η t) ((min t 1) ^ ((η : ℝ) / 2))
    fun f => ?_
  rw [heatPre_apply, norm_holderBesovPre]
  exact norm_heatOp_le_holder η ht _

end RegularityStructures.Datum

end

@[expose] public noncomputable section

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- `P_t` on `𝒞^η`, valued in `C(T³)` (`0` for `t ≤ 0`). -/
def heatExtHom (η : NegExponent) (t : ℝ) : HolderBesov η →+ C(Torus3, ℝ) :=
  if ht : 0 < t then (heatPre η t).extension (continuous_heatPre η ht) else 0

/-- `P_t a ∈ C(T³)` for `a ∈ 𝒞^η` and `t > 0` (and `0` for `t ≤ 0`): the continuous extension of
`f ↦ heatSemigroup t f` from `C(T³)` to the completion. -/
def heatExt (η : NegExponent) (a : HolderBesov η) (t : ℝ) : C(Torus3, ℝ) := heatExtHom η t a

end RegularityStructures.Datum

end

public section

open MeasureTheory Set

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem heatExt_of_pos (η : NegExponent) (a : HolderBesov η) {t : ℝ} (ht : 0 < t) :
    heatExt η a t = (heatPre η t).extension (continuous_heatPre η ht) a := by
  simp [heatExt, heatExtHom, ht]

/-- On `toHolderBesov η f`, `P_t` is the heat semigroup. -/
theorem heatExt_toHolderBesov (η : NegExponent) (f : C(Torus3, ℝ)) {t : ℝ} (ht : 0 < t) :
    heatExt η (toHolderBesov η f) t = heatOp t f := by
  rw [heatExt_of_pos η _ ht, toHolderBesov]
  exact AddMonoidHom.extension_coe (heatPre η t) (continuous_heatPre η ht) (show HolderBesovPre η from f)

theorem heatExt_sub (η : NegExponent) (a b : HolderBesov η) (t : ℝ) :
    heatExt η (a - b) t = heatExt η a t - heatExt η b t := map_sub _ _ _

theorem continuous_heatExt (η : NegExponent) {t : ℝ} (ht : 0 < t) :
    Continuous fun a : HolderBesov η => heatExt η a t := by
  simp_rw [heatExt_of_pos η _ ht]
  exact AddMonoidHom.continuous_extension _ _

/-- **The bound** `‖P_t a‖_∞ ≤ (min t 1)^{η/2} ‖a‖_η`. -/
theorem norm_heatExt_le (η : NegExponent) (a : HolderBesov η) {t : ℝ} (ht : 0 < t) :
    ‖heatExt η a t‖ ≤ (min t 1) ^ ((η : ℝ) / 2) * ‖a‖ := by
  induction a using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le ((continuous_heatExt η ht).norm) (continuous_const.mul continuous_norm)
  | ih f =>
    have h1 : ((f : HolderBesovPre η) : HolderBesov η) = toHolderBesov η (show C(Torus3, ℝ) from f) :=
      rfl
    rw [h1, heatExt_toHolderBesov η _ ht, norm_toHolderBesov]
    exact norm_heatOp_le_holder η ht _

/-- **The semigroup law** `P_s (P_t a) = P_{s+t} a`. -/
theorem heatOp_heatExt (η : NegExponent) (a : HolderBesov η) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) : heatOp s (heatExt η a t) = heatExt η a (s + t) := by
  have hst : 0 < s + t := add_pos hs ht
  induction a using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_eq ?_ (continuous_heatExt η hst)
    exact (heatOpCLM (E := ℝ) s).continuous.comp (continuous_heatExt η ht) |>.congr
      fun a => by rw [Function.comp_apply, heatOpCLM_apply]
  | ih f =>
    have h1 : ((f : HolderBesovPre η) : HolderBesov η) = toHolderBesov η (show C(Torus3, ℝ) from f) :=
      rfl
    rw [h1, heatExt_toHolderBesov η _ ht, heatExt_toHolderBesov η _ hst,
      heatOp_heatOp ht.le hs.le, add_comm]

end RegularityStructures.Datum

end

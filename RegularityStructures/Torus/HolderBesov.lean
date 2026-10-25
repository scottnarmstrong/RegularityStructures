/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Hölder–Besov spaces of negative order on the three-torus

For `η < 0` and `f ∈ C(T³)`,
`‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_{x ∈ T³} |P_s f(x)|` (the statement, Definition 2.1 and
equation (2.3)), and `𝒞^η` is the completion of `C(T³)` for this norm.

`holderBesovENorm` is the extended-real supremum. For `η ≤ 0` it is bounded by the supremum
norm, so it is finite, and it is subadditive because `P_s` is linear. Hence it defines an additive
group seminorm on `C(T³)`. `HolderBesov η` is the completion of `C(T³)` for that seminorm, and
`toHolderBesov η` embeds `C(T³)` into it.

Source: the statement, Definition 2.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

/-- Negative regularity exponents `η < 0`. -/
abbrev NegExponent : Type := {η : ℝ // η < 0}

/-- `‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_x |P_s f(x)|`, as an extended real. -/
def holderBesovENorm (η : ℝ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ s ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

theorem holderBesovENorm_le {η : ℝ} (hη : η ≤ 0) (f : C(Torus3, ℝ)) :
    holderBesovENorm η f ≤ ‖f‖ₑ := by
  refine iSup₂_le fun s hs => ?_
  have h1 : ENNReal.ofReal (s ^ (-η / 2)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 (Real.rpow_le_one hs.1.le hs.2 (by linarith))
  have h2 : ⨆ x, ‖heatSemigroup s f x‖ₑ ≤ ‖f‖ₑ :=
    iSup_le fun x => enorm_le_iff_norm_le.2 (norm_heatSemigroup_le hs.1 f x)
  simpa using mul_le_mul' h1 h2

theorem holderBesovENorm_lt_top {η : ℝ} (hη : η ≤ 0) (f : C(Torus3, ℝ)) :
    holderBesovENorm η f < ⊤ :=
  (holderBesovENorm_le hη f).trans_lt enorm_lt_top

theorem holderBesovENorm_zero (η : ℝ) : holderBesovENorm η 0 = 0 := by
  simp [holderBesovENorm, heatSemigroup_zero]

theorem holderBesovENorm_neg (η : ℝ) (f : C(Torus3, ℝ)) :
    holderBesovENorm η (-f) = holderBesovENorm η f := by
  simp [holderBesovENorm, heatSemigroup_neg]

theorem holderBesovENorm_add_le (η : ℝ) (f g : C(Torus3, ℝ)) :
    holderBesovENorm η (f + g) ≤ holderBesovENorm η f + holderBesovENorm η g := by
  refine iSup₂_le fun s hs => ?_
  have hsum : ⨆ x, ‖heatSemigroup s (f + g) x‖ₑ ≤
      (⨆ x, ‖heatSemigroup s f x‖ₑ) + ⨆ x, ‖heatSemigroup s g x‖ₑ := by
    refine iSup_le fun x => ?_
    rw [heatSemigroup_add hs.1]
    exact (enorm_add_le _ _).trans
      (add_le_add (le_iSup (fun x => ‖heatSemigroup s f x‖ₑ) x)
        (le_iSup (fun x => ‖heatSemigroup s g x‖ₑ) x))
  calc ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s (f + g) x‖ₑ
      ≤ ENNReal.ofReal (s ^ (-η / 2)) *
          ((⨆ x, ‖heatSemigroup s f x‖ₑ) + ⨆ x, ‖heatSemigroup s g x‖ₑ) :=
        mul_le_mul_right hsum _
    _ = ENNReal.ofReal (s ^ (-η / 2)) * (⨆ x, ‖heatSemigroup s f x‖ₑ) +
          ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s g x‖ₑ := mul_add _ _ _
    _ ≤ holderBesovENorm η f + holderBesovENorm η g :=
        add_le_add
          (le_iSup₂ (f := fun s (_ : s ∈ Ioc (0 : ℝ) 1) =>
            ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ) s hs)
          (le_iSup₂ (f := fun s (_ : s ∈ Ioc (0 : ℝ) 1) =>
            ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s g x‖ₑ) s hs)

end RegularityStructures

end

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

/-- The seminorm `‖·‖_η` on `C(T³)`, for `η < 0`. -/
def holderBesovSeminorm (η : NegExponent) : AddGroupSeminorm C(Torus3, ℝ) where
  toFun f := (holderBesovENorm η f).toReal
  map_zero' := by simp [holderBesovENorm_zero]
  add_le' f g := by
    have hf := holderBesovENorm_lt_top η.2.le f
    have hg := holderBesovENorm_lt_top η.2.le g
    rw [← ENNReal.toReal_add hf.ne hg.ne]
    exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hf, hg⟩).ne (holderBesovENorm_add_le η f g)
  neg' f := by simp [holderBesovENorm_neg]

/-- `C(T³)` equipped with the seminorm `‖·‖_η`. -/
def HolderBesovPre (_η : NegExponent) : Type := C(Torus3, ℝ)

instance (η : NegExponent) : AddCommGroup (HolderBesovPre η) :=
  inferInstanceAs (AddCommGroup C(Torus3, ℝ))

instance (η : NegExponent) : SeminormedAddCommGroup (HolderBesovPre η) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := HolderBesovPre η) (holderBesovSeminorm η)

/-- The Hölder–Besov space `𝒞^η`, the completion of `C(T³)` for `‖·‖_η`. -/
abbrev HolderBesov (η : NegExponent) : Type := UniformSpace.Completion (HolderBesovPre η)

instance (η : NegExponent) : MeasurableSpace (HolderBesov η) := borel _

instance (η : NegExponent) : BorelSpace (HolderBesov η) := ⟨rfl⟩

/-- The embedding `C(T³) → 𝒞^η`. -/
def toHolderBesov (η : NegExponent) (f : C(Torus3, ℝ)) : HolderBesov η :=
  UniformSpace.Completion.coe' (show HolderBesovPre η from f)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem norm_toHolderBesov (η : NegExponent) (f : C(Torus3, ℝ)) :
    ‖toHolderBesov η f‖ = (holderBesovENorm η f).toReal := by
  rw [toHolderBesov, UniformSpace.Completion.norm_coe]
  rfl

theorem toHolderBesov_sub (η : NegExponent) (f g : C(Torus3, ℝ)) :
    toHolderBesov η (f - g) = toHolderBesov η f - toHolderBesov η g :=
  UniformSpace.Completion.coe_sub (show HolderBesovPre η from f) (show HolderBesovPre η from g)

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.Probability.WhiteNoise
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import GlobalPhi43Statements.Defs.HeatAt
public import GlobalPhi43Statements.Defs.ExtNorm
public import GlobalPhi43Statements.Defs.HolderBesovEmbed

/-!
# Characterisations of `heatAt`, `extNorm` and `holderBesovEmbed`

The two extensions to the completion `𝒞^η` are characterisation-defined. This file proves that each is the unique continuous map with
the required values on `C(T³)`, and that `𝒩^η_{η'}` is lower semicontinuous and Borel and restricts
to `‖·‖_{η'}` on `C(T³)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `|(P_s f)(x)| ≤ s^{η/2} ‖f‖_η` for `s ∈ (0, 1]`, read off the definition of `‖·‖_η`. -/
theorem abs_heatSemigroup_le (η : NegExponent) (s : Ioc (0 : ℝ) 1) (f : C(Torus3, ℝ))
    (x : Torus3) :
    |heatSemigroup s f x| ≤ (s : ℝ) ^ ((η : ℝ) / 2) * (holderBesovENorm η f).toReal := by
  have hs : (0 : ℝ) < s := s.2.1
  have hle : ENNReal.ofReal ((s : ℝ) ^ (-(η : ℝ) / 2)) * ‖heatSemigroup s f x‖ₑ ≤
      holderBesovENorm η f := by
    unfold holderBesovENorm
    refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ) (_ : r ∈ Ioc (0 : ℝ) 1) =>
      ENNReal.ofReal (r ^ (-(η : ℝ) / 2)) * ⨆ y, ‖heatSemigroup r f y‖ₑ) (s : ℝ) s.2)
    exact mul_le_mul_right (le_iSup (fun y => ‖heatSemigroup s f y‖ₑ) x) _
  have hfin := holderBesovENorm_lt_top η.2.le f
  have hpos : 0 < (s : ℝ) ^ (-(η : ℝ) / 2) := Real.rpow_pos_of_pos hs _
  have hreal : (s : ℝ) ^ (-(η : ℝ) / 2) * |heatSemigroup s f x| ≤
      (holderBesovENorm η f).toReal := by
    have h := ENNReal.toReal_mono hfin.ne hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le, ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs] at h
  have hinv : (s : ℝ) ^ ((η : ℝ) / 2) * (s : ℝ) ^ (-(η : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hs, show (η : ℝ) / 2 + -(η : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  calc |heatSemigroup s f x|
      = (s : ℝ) ^ ((η : ℝ) / 2) * ((s : ℝ) ^ (-(η : ℝ) / 2) * |heatSemigroup s f x|) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (s : ℝ) ^ ((η : ℝ) / 2) * (holderBesovENorm η f).toReal :=
        mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hs.le _)

/-- The distance of `HolderBesovPre η` is `‖f - g‖_η`. -/
theorem dist_holderBesovPre (η : NegExponent) (f g : C(Torus3, ℝ)) :
    dist (show HolderBesovPre η from f) (show HolderBesovPre η from g) =
      (holderBesovENorm η (f - g)).toReal := by
  rw [← UniformSpace.Completion.dist_eq, dist_eq_norm]
  change ‖toHolderBesov η f - toHolderBesov η g‖ = _
  rw [← toHolderBesov_sub, norm_toHolderBesov]

/-- `f ↦ (P_s f)(x)` is Lipschitz for `‖·‖_η`, with constant `s^{η/2}`. -/
theorem lipschitzWith_heatSemigroup (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3) :
    LipschitzWith ⟨(s : ℝ) ^ ((η : ℝ) / 2), Real.rpow_nonneg s.2.1.le _⟩
      (fun f : HolderBesovPre η => heatSemigroup s f x) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  let F : C(Torus3, ℝ) := f
  let G : C(Torus3, ℝ) := g
  have hsub : heatSemigroup s (F - G) x = heatSemigroup s F x - heatSemigroup s G x := by
    rw [sub_eq_add_neg, heatSemigroup_add s.2.1, heatSemigroup_neg, ← sub_eq_add_neg]
  have hd : dist f g = (holderBesovENorm η (F - G)).toReal := dist_holderBesovPre η F G
  rw [Real.dist_eq, hd]
  change |heatSemigroup s F x - heatSemigroup s G x| ≤ _
  rw [← hsub]
  exact abs_heatSemigroup_le η s (F - G) x

theorem heatAt_toHolderBesov (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3)
    (f : C(Torus3, ℝ)) : heatAt η s x (toHolderBesov η f) = heatSemigroup s f x :=
  UniformSpace.Completion.extension_coe (lipschitzWith_heatSemigroup η s x).uniformContinuous _

theorem continuous_heatAt (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3) :
    Continuous (heatAt η s x) :=
  UniformSpace.Completion.continuous_extension

/-- `heatAt η s x` is the unique continuous extension of `f ↦ (P_s f)(x)` to `𝒞^η`. -/
theorem heatAt_unique (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3)
    (g : HolderBesov η → ℝ) (hg : Continuous g)
    (hgf : ∀ f : C(Torus3, ℝ), g (toHolderBesov η f) = heatSemigroup s f x) :
    g = heatAt η s x :=
  UniformSpace.Completion.ext hg (continuous_heatAt η s x) fun f =>
    (hgf f).trans (heatAt_toHolderBesov η s x f).symm

/-- `𝒩^η_{η'}` is lower semicontinuous, hence Borel, on `𝒞^η`. -/
theorem lowerSemicontinuous_extNorm (η : NegExponent) (η' : ℝ) :
    LowerSemicontinuous (extNorm η η') := by
  have h : extNorm η η' = fun z => ⨆ s : Ioc (0 : ℝ) 1, ⨆ x,
      ENNReal.ofReal ((s : ℝ) ^ (-η' / 2)) * ‖heatAt η s x z‖ₑ := by
    funext z
    simp only [extNorm, ENNReal.mul_iSup]
  rw [h]
  refine lowerSemicontinuous_iSup fun s => lowerSemicontinuous_iSup fun x => ?_
  exact ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    (continuous_enorm.comp (continuous_heatAt η s x))).lowerSemicontinuous

theorem measurable_extNorm (η : NegExponent) (η' : ℝ) : Measurable (extNorm η η') :=
  (lowerSemicontinuous_extNorm η η').measurable

/-- On `C(T³)`, `𝒩_{η'}` is the norm `‖·‖_{η'}`. -/
theorem extNorm_toHolderBesov (η : NegExponent) (η' : ℝ) (f : C(Torus3, ℝ)) :
    extNorm η η' (toHolderBesov η f) = holderBesovENorm η' f := by
  simp only [extNorm, heatAt_toHolderBesov, holderBesovENorm]
  rw [iSup_subtype']

/-- `‖f‖_η ≤ ‖f‖_{η''}` for `η ≤ η''`. -/
theorem holderBesovENorm_mono {η η'' : ℝ} (h : η ≤ η'') (f : C(Torus3, ℝ)) :
    holderBesovENorm η f ≤ holderBesovENorm η'' f := by
  unfold holderBesovENorm
  refine iSup₂_mono fun s hs => mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2 (by linarith)

/-- The identity of `C(T³)` is `1`-Lipschitz from `‖·‖_{η''}` to `‖·‖_η` for `η ≤ η''`. -/
theorem lipschitzWith_holderBesovPre_id (η η'' : NegExponent) (h : (η : ℝ) ≤ η'') :
    LipschitzWith 1 (fun f : HolderBesovPre η'' => (show HolderBesovPre η from f)) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  let F : C(Torus3, ℝ) := f
  let G : C(Torus3, ℝ) := g
  have h₁ : dist (show HolderBesovPre η from F) (show HolderBesovPre η from G) =
      (holderBesovENorm η (F - G)).toReal := dist_holderBesovPre η F G
  have h₂ : dist f g = (holderBesovENorm η'' (F - G)).toReal := dist_holderBesovPre η'' F G
  rw [NNReal.coe_one, one_mul, h₂]
  refine le_of_eq_of_le h₁ ?_
  exact ENNReal.toReal_mono (holderBesovENorm_lt_top η''.2.le _).ne (holderBesovENorm_mono h _)

theorem holderBesovEmbed_toHolderBesov (η η'' : NegExponent) (h : (η : ℝ) ≤ η'')
    (f : C(Torus3, ℝ)) : holderBesovEmbed η η'' h (toHolderBesov η'' f) = toHolderBesov η f :=
  UniformSpace.Completion.map_coe (lipschitzWith_holderBesovPre_id η η'' h).uniformContinuous _

theorem continuous_holderBesovEmbed (η η'' : NegExponent) (h : (η : ℝ) ≤ η'') :
    Continuous (holderBesovEmbed η η'' h) :=
  UniformSpace.Completion.continuous_map

/-- `holderBesovEmbed η η'' h` is the unique continuous map `𝒞^{η''} → 𝒞^η` extending the identity
of `C(T³)`. -/
theorem holderBesovEmbed_unique (η η'' : NegExponent) (h : (η : ℝ) ≤ η'')
    (g : HolderBesov η'' → HolderBesov η) (hg : Continuous g)
    (hgf : ∀ f : C(Torus3, ℝ), g (toHolderBesov η'' f) = toHolderBesov η f) :
    g = holderBesovEmbed η η'' h :=
  UniformSpace.Completion.ext hg (continuous_holderBesovEmbed η η'' h) fun f =>
    (hgf f).trans (holderBesovEmbed_toHolderBesov η η'' h f).symm

end GlobalPhi43

end

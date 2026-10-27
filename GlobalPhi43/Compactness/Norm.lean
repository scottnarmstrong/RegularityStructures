module

public import GlobalPhi43.Compactness.Embedding

@[expose] public noncomputable section

open Set RegularityStructures
open scoped ENNReal

namespace GlobalPhi43

/-- Each heat probe is additive on the completion. -/
theorem heatAt_add (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3)
    (z w : HolderBesov η) : heatAt η s x (z + w) = heatAt η s x z + heatAt η s x w := by
  induction z, w using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      ((continuous_heatAt η s x).comp (continuous_fst.add continuous_snd))
      (((continuous_heatAt η s x).comp continuous_fst).add
        ((continuous_heatAt η s x).comp continuous_snd))
  | ih f g =>
    rw [← UniformSpace.Completion.coe_add]
    let F : C(Torus3, ℝ) := f
    let G : C(Torus3, ℝ) := g
    change heatAt η s x (toHolderBesov η (F + G)) =
      heatAt η s x (toHolderBesov η F) + heatAt η s x (toHolderBesov η G)
    simp only [heatAt_toHolderBesov, heatSemigroup_add s.2.1]

/-- The extended norm is subadditive, including at infinite values. -/
theorem extNorm_add_le (η : NegExponent) (α : ℝ) (z w : HolderBesov η) :
    extNorm η α (z + w) ≤ extNorm η α z + extNorm η α w := by
  unfold extNorm
  refine iSup_le fun s => ?_
  calc
    _ ≤ ENNReal.ofReal ((s : ℝ) ^ (-α / 2)) *
        ((⨆ x, ‖heatAt η s x z‖ₑ) + ⨆ x, ‖heatAt η s x w‖ₑ) := by
      gcongr
      refine iSup_le fun x => ?_
      rw [heatAt_add]
      exact (enorm_add_le _ _).trans (add_le_add (le_iSup (fun y => ‖heatAt η s y z‖ₑ) x)
        (le_iSup (fun y => ‖heatAt η s y w‖ₑ) x))
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (le_iSup (fun r : Ioc (0 : ℝ) 1 =>
        ENNReal.ofReal ((r : ℝ) ^ (-α / 2)) * ⨆ x, ‖heatAt η r x z‖ₑ) s)
        (le_iSup (fun r : Ioc (0 : ℝ) 1 =>
        ENNReal.ofReal ((r : ℝ) ^ (-α / 2)) * ⨆ x, ‖heatAt η r x w‖ₑ) s)

/-- At the source exponent the extended norm is bounded by the completion norm. -/
theorem extNorm_self_le (η : NegExponent) (z : HolderBesov η) :
    extNorm η η z ≤ ‖z‖ₑ := by
  unfold extNorm
  refine iSup_le fun s => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun x => ?_
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
        (continuous_enorm.comp (continuous_heatAt η s x))) continuous_enorm
  | ih f =>
    let F : C(Torus3, ℝ) := f
    change ENNReal.ofReal ((s : ℝ) ^ (-(η : ℝ) / 2)) *
      ‖heatAt η s x (toHolderBesov η F)‖ₑ ≤ ‖toHolderBesov η F‖ₑ
    have he : ‖toHolderBesov η F‖ₑ = holderBesovENorm η F := by
      rw [← ofReal_norm, norm_toHolderBesov,
        ENNReal.ofReal_toReal (holderBesovENorm_lt_top η.2.le F).ne]
    rw [heatAt_toHolderBesov, he]
    exact (mul_le_mul_right (le_iSup (fun y => ‖heatSemigroup s F y‖ₑ) x) _).trans
      (le_iSup₂ (f := fun (r : ℝ) (_ : r ∈ Ioc (0 : ℝ) 1) =>
        ENNReal.ofReal (r ^ (-(η : ℝ) / 2)) * ⨆ y, ‖heatSemigroup r F y‖ₑ) s s.2)

/-- The source extended norm is a continuous real-valued norm after `toReal`. -/
theorem lipschitzWith_extNorm_self_toReal (η : NegExponent) :
    LipschitzWith 1 (fun z => (extNorm η η z).toReal) := by
  have hfin (z : HolderBesov η) : extNorm η η z ≠ ⊤ :=
    ne_top_of_le_ne_top enorm_ne_top (extNorm_self_le η z)
  have hle (z w : HolderBesov η) :
      (extNorm η η z).toReal ≤ (extNorm η η w).toReal + ‖z - w‖ := by
    have hz : z = w + (z - w) := by abel
    have hb : extNorm η η z ≤ extNorm η η w + ‖z - w‖ₑ := by
      calc
        extNorm η η z = extNorm η η (w + (z - w)) := congrArg _ hz
        _ ≤ extNorm η η w + extNorm η η (z - w) := extNorm_add_le η η _ _
        _ ≤ _ := add_le_add_right (extNorm_self_le η (z - w)) _
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin w, enorm_ne_top⟩) hb
    simpa only [ENNReal.toReal_add (hfin w) enorm_ne_top, toReal_enorm] using ht
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, abs_le]
  constructor
  · have hh := hle w z
    rw [norm_sub_rev] at hh
    linarith
  · have hh := hle z w
    linarith

/-- The heat-probe norm at the source exponent equals the completion norm. -/
theorem extNorm_self (η : NegExponent) (z : HolderBesov η) :
    extNorm η η z = ‖z‖ₑ := by
  have heq : (fun w : HolderBesov η => (extNorm η η w).toReal) = fun w => ‖w‖ := by
    apply UniformSpace.Completion.ext (lipschitzWith_extNorm_self_toReal η).continuous
      continuous_norm
    intro f
    let F : C(Torus3, ℝ) := f
    change (extNorm η η (toHolderBesov η F)).toReal = ‖toHolderBesov η F‖
    rw [extNorm_toHolderBesov, norm_toHolderBesov]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_top_of_le_ne_top enorm_ne_top (extNorm_self_le η z)) enorm_ne_top).mp
  simpa only [toReal_enorm] using congrFun heq z

end GlobalPhi43

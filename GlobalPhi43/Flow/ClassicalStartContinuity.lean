module

public import GlobalPhi43.Flow.ClassicalStability

/-! Smooth classical paths vary continuously with the deterministic forcing
shift and the smooth initial datum, in the uniform norm on each finite horizon.
No rough-start continuity or stochastic perfection is asserted. -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped Topology

namespace GlobalPhi43.Flow

/-- Smooth data retain the ordinary spatial supremum topology. -/
abbrev SmoothDatum := {x : C(Torus3, ℝ) // IsSmoothOnTorus x}

@[expose] def classicalCurve (T b : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (x : SmoothDatum) :
    C(Icc (0 : ℝ) T, C(Torus3, ℝ)) where
  toFun r := smoothSolution b f hf x.val x.property r
  continuous_toFun :=
    (ContinuousMap.continuousOn_of_continuousOn_uncurry _
      (smoothSolution_spec b f hf x.val x.property).continuousOn).comp_continuous
        continuous_subtype_val (fun r => r.property.1)

/-- The smooth forcing window is a continuous function of every real start. -/
@[expose] def forcingWindow (T : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) : C(ℝ, C(Icc (0 : ℝ) T, C(Torus3, ℝ))) :=
  ContinuousMap.curry ⟨fun p => forcingCurve f hf ((p.2 : ℝ) + p.1),
    (forcingCurve f hf).continuous.comp
      ((continuous_subtype_val.comp continuous_snd).add continuous_fst)⟩

/-- Uniform path comparison on a common compact relative-time interval.
The forcing allowance is its actual window norm, not a supplied bound. -/
theorem classicalCurve_shift_stability (T b : ℝ) (hT : 0 ≤ T)
    (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (s s' : ℝ) (x y : SmoothDatum) :
    ‖classicalCurve T b (shiftForcing s f) (isSmoothOnSpaceTime_shiftForcing hf s) x -
      classicalCurve T b (shiftForcing s' f) (isSmoothOnSpaceTime_shiftForcing hf s') y‖ ≤
      Real.exp (max b 0 * T) *
        (‖x.val - y.val‖ + T * ‖forcingWindow T f hf s - forcingWindow T f hf s'‖) := by
  let B := ‖forcingWindow T f hf s - forcingWindow T f hf s'‖
  have hB : 0 ≤ B := norm_nonneg
    (forcingWindow T f hf s - forcingWindow T f hf s')
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_nonneg _)
    (add_nonneg (norm_nonneg _) (mul_nonneg hT hB)))).mpr
  intro r
  change ‖smoothSolution b (shiftForcing s f) (isSmoothOnSpaceTime_shiftForcing hf s) x.val x.property r -
    smoothSolution b (shiftForcing s' f) (isSmoothOnSpaceTime_shiftForcing hf s') y.val y.property r‖ ≤ _
  have hi := classicalSolution_integral_stability_pos
    (isSmoothOnSpaceTime_shiftForcing hf s) (isSmoothOnSpaceTime_shiftForcing hf s')
    (smoothSolution_spec b (shiftForcing s f) (isSmoothOnSpaceTime_shiftForcing hf s) x.val x.property)
    (smoothSolution_spec b (shiftForcing s' f) (isSmoothOnSpaceTime_shiftForcing hf s') y.val y.property) r.property.1
  have hforce : ∀ q ∈ Icc (0 : ℝ) (r : ℝ),
      ‖forcingCurve (shiftForcing s f) (isSmoothOnSpaceTime_shiftForcing hf s) q -
        forcingCurve (shiftForcing s' f) (isSmoothOnSpaceTime_shiftForcing hf s') q‖ ≤ B := by
    intro q hq
    exact (forcingWindow T f hf s - forcingWindow T f hf s').norm_coe_le_norm
      ⟨q, hq.1, hq.2.trans r.property.2⟩
  have hint : (∫ q in (0 : ℝ)..(r : ℝ),
      ‖forcingCurve (shiftForcing s f) (isSmoothOnSpaceTime_shiftForcing hf s) q -
        forcingCurve (shiftForcing s' f) (isSmoothOnSpaceTime_shiftForcing hf s') q‖) ≤ T * B := by
    have hm := intervalIntegral.integral_mono_on r.property.1
      ((forcingNorm_continuous (isSmoothOnSpaceTime_shiftForcing hf s)
        (isSmoothOnSpaceTime_shiftForcing hf s')).intervalIntegrable 0 r)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume 0 r)
      hforce
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right r.property.2 hB)
  have he : Real.exp (max b 0 * (r : ℝ)) ≤ Real.exp (max b 0 * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left r.property.2 (le_max_right b 0))
  apply hi.trans
  exact mul_le_mul he (by linarith only [hint])
    (add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg r.property.1
      (fun _ _ => norm_nonneg _))) (Real.exp_nonneg _)

/-- Joint start/data continuity of the actual chosen smooth classical paths,
uniformly over the full finite relative-time window, including zero. -/
theorem continuous_classicalCurve_shift (T b : ℝ) (hT : 0 ≤ T)
    (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f) :
    Continuous (fun p : ℝ × SmoothDatum => classicalCurve T b (shiftForcing p.1 f)
      (isSmoothOnSpaceTime_shiftForcing hf p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  refine (tendsto_iff_norm_sub_tendsto_zero
    (f := fun q : ℝ × SmoothDatum => classicalCurve T b (shiftForcing q.1 f)
      (isSmoothOnSpaceTime_shiftForcing hf q.1) q.2)).2 ?_
  have hfw : Continuous (fun q : ℝ × SmoothDatum =>
      forcingWindow T f hf q.1 - forcingWindow T f hf p.1) :=
    ((forcingWindow T f hf).continuous.comp continuous_fst).sub continuous_const
  have hn : Continuous (fun q : ℝ × SmoothDatum =>
      ‖forcingWindow T f hf q.1 - forcingWindow T f hf p.1‖) := by
    change Continuous (fun q : ℝ × SmoothDatum =>
      dist (forcingWindow T f hf q.1 - forcingWindow T f hf p.1) 0)
    exact hfw.dist continuous_const
  have hc : Continuous (fun q : ℝ × SmoothDatum =>
      Real.exp (max b 0 * T) * (‖q.2.val - p.2.val‖ +
        T * ‖forcingWindow T f hf q.1 - forcingWindow T f hf p.1‖)) := by
    exact continuous_const.mul
      (((continuous_subtype_val.comp continuous_snd).sub continuous_const).norm.add
        (continuous_const.mul hn))
  have hlim := hc.continuousAt (x := p) |>.tendsto
  have hz : ‖forcingWindow T f hf p.1 - forcingWindow T f hf p.1‖ = 0 := by
    rw [sub_self]
    change dist (0 : C(Icc (0 : ℝ) T, C(Torus3, ℝ))) 0 = 0
    exact dist_self _
  rw [hz] at hlim
  simp only [sub_self, norm_zero, mul_zero, add_zero] at hlim
  refine squeeze_zero (fun q => norm_nonneg
    (classicalCurve T b (shiftForcing q.1 f) (isSmoothOnSpaceTime_shiftForcing hf q.1) q.2 -
      classicalCurve T b (shiftForcing p.1 f) (isSmoothOnSpaceTime_shiftForcing hf p.1) p.2)) ?_ hlim
  intro q
  exact classicalCurve_shift_stability T b hT f hf q.1 p.1 q.2 p.2

end GlobalPhi43.Flow

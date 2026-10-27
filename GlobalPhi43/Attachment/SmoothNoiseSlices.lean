module

public import GlobalPhi43.Attachment.PotentialObservable
public import GlobalPhi43.Attachment.Realisation

/-! Everywhere time-slice observables on the full smooth-noise evaluation space.
The observables use the smooth-noise evaluation space directly, without
restriction to a growth event or replacement by zero. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43 Set
open scoped NNReal

/-- All smooth forcings, with the induced evaluation sigma algebra. -/
abbrev SmoothNoise := {f : SpaceTime → ℝ // IsSmoothOnSpaceTime f}

/-- The actual truncated-kernel J at a fixed time, as a continuous spatial function. -/
def smoothNoiseJ (N : ℕ) (f : SmoothNoise) (t : ℝ) : C(Torus3, ℝ) :=
  ⟨fun x => treeJ N f.1 (t, x), (continuous_treeJ f.2).comp
    (continuous_const.prodMk continuous_id)⟩

theorem smoothNoiseJ_continuous (N : ℕ) (f : SmoothNoise) : Continuous (smoothNoiseJ N f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_treeJ f.2).comp (continuous_fst.prodMk continuous_snd)

/-- Measurable dependence on the entire smooth forcing; no stochastic premise is needed. -/
theorem smoothNoiseJ_measurable (N : ℕ) (t : ℝ) :
    Measurable (fun f : SmoothNoise => smoothNoiseJ N f t) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro x
  have hn : Measurable (fun p : SmoothNoise × SpaceTime => p.1.1 p.2) := by
    have h := measurable_uncurry_of_continuous_of_measurable
      (u := fun (z : SpaceTime) (f : SmoothNoise) => f.1 z)
      (fun f => IsSmoothOnSpaceTime.continuous f.2)
      (fun z => (measurable_pi_apply z).comp measurable_subtype_coe)
    exact h.comp (measurable_snd.prodMk measurable_fst)
  have hi : Measurable (fun p : SmoothNoise × SpaceTime =>
      hairerKernelTorus N ((t, x) - p.2) * p.1.1 p.2) :=
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_snd)).mul hn
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

/-- The exact weighted time-slice quantity, on every smooth forcing. -/
def smoothNoiseSlice (N : ℕ) (η : NegExponent) (s : ℝ) (f : SmoothNoise) : ENNReal :=
  ⨆ t : Ioc (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt t.1) * holderBesovENorm η (smoothNoiseJ N f (s + t.1))

/-- The time-slice observable is measurable on the full smooth-noise evaluation space. -/
theorem smoothNoiseSlice_measurable (N : ℕ) (η : NegExponent) (s : ℝ) :
    Measurable (smoothNoiseSlice N η s) := by
  have he : smoothNoiseSlice N η s =
      (⨆ t : Ioc (0 : ℝ) 1, fun f : SmoothNoise =>
        ENNReal.ofReal (Real.sqrt t.1) * holderBesovENorm η (smoothNoiseJ N f (s + t.1))) := by
    funext f
    simp only [smoothNoiseSlice, iSup_apply]
  rw [he]
  have hm (t : Ioc (0 : ℝ) 1) : Measurable (fun f : SmoothNoise =>
      ENNReal.ofReal (Real.sqrt t.1) * holderBesovENorm η (smoothNoiseJ N f (s + t.1))) := by
    have hn : Measurable (fun f : SmoothNoise =>
        holderBesovENorm η (smoothNoiseJ N f (s + t.1))) :=
      (continuous_holderBesovENorm_negative η).measurable.comp
        (smoothNoiseJ_measurable N (s + t.1))
    exact measurable_const.mul hn
  apply measurable_iSup_of_lowerSemicontinuous hm
  intro f
  apply Continuous.lowerSemicontinuous
  refine Continuous.ennreal_mul ?_ ?_
    (fun t => Or.inr (holderBesovENorm_lt_top η.2.le _).ne)
    (fun _ => Or.inr ENNReal.ofReal_ne_top)
  · exact ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_subtype_val)
  · exact (continuous_holderBesovENorm_negative η).comp ((smoothNoiseJ_continuous N f).comp
      (continuous_const.add continuous_subtype_val))

/-- Finiteness is everywhere and uses compact-time continuity, not a good-noise event. -/
theorem smoothNoiseSlice_lt_top (N : ℕ) (η : NegExponent) (s : ℝ) (f : SmoothNoise) :
    smoothNoiseSlice N η s f < ⊤ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc s (s + 1))).exists_bound_of_continuousOn
    (smoothNoiseJ_continuous N f).continuousOn
  have hb : smoothNoiseSlice N η s f ≤ ENNReal.ofReal (max B 0) := by
    apply iSup_le
    intro t
    have hJ : holderBesovENorm η (smoothNoiseJ N f (s + t.1)) ≤ ENNReal.ofReal (max B 0) := by
      refine (holderBesovENorm_le η.2.le _).trans ?_
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      exact (hB _ ⟨by linarith [t.2.1], by linarith [t.2.2]⟩).trans (le_max_left _ _)
    have ht : ENNReal.ofReal (Real.sqrt t.1) ≤ 1 := ENNReal.ofReal_le_one.mpr
      (Real.sqrt_le_one.mpr t.2.2)
    exact (mul_le_mul' ht hJ).trans_eq (one_mul _)
  exact hb.trans_lt ENNReal.ofReal_lt_top

end GlobalPhi43.Attachment

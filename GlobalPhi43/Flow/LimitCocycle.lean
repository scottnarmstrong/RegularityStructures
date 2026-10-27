module

public import GlobalPhi43.Flow.MovingInitialData
public import GlobalPhi43.Flow.ClassicalTranslation

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow.FiniteLimitSystem

variable {N : ℕ} {κ : Kappa} {η : NegExponent} {A : ℕ → LiftData N κ}

/-- Classical restart passed to the noise/lift limit with the actual varying
smooth intermediate state, for every real nonnegative start and endpoint. -/
theorem cocycle_smooth (sys : FiniteLimitSystem η A) (s r t : ℝ)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    sys.value r (t - r) (sys.value s (r - s) (toHolderBesov η x)) =
      sys.value s (t - s) (toHolderBesov η x) := by
  let b := fun n => 3 * (A n).constants.1 - 9 * (A n).constants.2
  let v := fun n => smoothSolution (b n) (shiftForcing s (A n).forcing) ((A n).shiftSmooth s) x hx
  let y := fun n => toHolderBesov η (v n (r - s))
  have hds : 0 ≤ r - s := sub_nonneg.mpr hsr
  have hdt : 0 ≤ t - r := sub_nonneg.mpr hrt
  have hst : 0 ≤ t - s := sub_nonneg.mpr (hsr.trans hrt)
  have hy : Tendsto y atTop (𝓝 (sys.value s (r - s) (toHolderBesov η x))) :=
    sys.tendsto_smooth_value s (r - s) hs hds x hx
  have hc := sys.tendsto_moving_data r (t - r) (hs.trans hsr) hdt y _ hy
  have he (n : ℕ) : sys.approximant n r (t - r) (y n) =
      sys.approximant n s (t - s) (toHolderBesov η x) := by
    have hyS : IsSmoothOnTorus (v n (r - s)) := smoothSolution_smooth_state
      (b n) _ ((A n).shiftSmooth s) x hx hds
    rw [sys.approximant_smooth n r (t - r) (hs.trans hsr) hdt _ hyS,
      sys.approximant_smooth n s (t - s) hs hst x hx]
    have hshift : shiftForcing (r - s) (shiftForcing s (A n).forcing) =
        shiftForcing r (A n).forcing := by rw [shiftForcing_add, add_sub_cancel]
    have hrestart := smoothSolution_restart (b n) (shiftForcing s (A n).forcing)
      ((A n).shiftSmooth s) x hx hds hdt
    have htime : r - s + (t - r) = t - s := by ring
    rw [htime] at hrestart
    apply congrArg (toHolderBesov η)
    exact (smoothSolution_congr_forcing (b n) ((A n).shiftSmooth r)
      (isSmoothOnSpaceTime_shiftForcing ((A n).shiftSmooth s) (r - s)) hshift.symm
      (v n (r - s)) hyS (t - r)).trans hrestart
  exact tendsto_nhds_unique (hc.congr he) (sys.tendsto_value s (t - s) (toHolderBesov η x) hs hst)

/-- Density passes restart to all rough states, with no smoothness or size
hypothesis on the intermediate limiting datum. -/
theorem cocycle (sys : FiniteLimitSystem η A) (s r t : ℝ)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (x : HolderBesov η) :
    sys.value r (t - r) (sys.value s (r - s) x) = sys.value s (t - s) x := by
  let L := ‖x‖
  have hleft : Continuous (fun z : StateBall η L => sys.value r (t - r) (sys.value s (r - s) z.val)) :=
    (sys.continuous_data r (t - r) (hs.trans hsr) (sub_nonneg.mpr hrt)).comp
      ((sys.continuous_data s (r - s) hs (sub_nonneg.mpr hsr)).comp continuous_subtype_val)
  have hright : Continuous (fun z : StateBall η L => sys.value s (t - s) z.val) :=
    (sys.continuous_data s (t - s) hs (sub_nonneg.mpr (hsr.trans hrt))).comp continuous_subtype_val
  have he := ballExtension_unique hleft hright (fun z => by
    have h := sys.cocycle_smooth s r t hs hsr hrt (smoothRepresentative z)
      (smoothRepresentative_spec z).1
    simpa only [(smoothRepresentative_spec z).2] using h)
  exact congrFun he ⟨x, by simpa only [mem_closedBall, dist_zero_right] using (le_rfl : ‖x‖ ≤ L)⟩

end GlobalPhi43.Flow.FiniteLimitSystem

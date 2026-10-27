module

public import GlobalPhi43.Flow.TwoDataLocal
public import GlobalPhi43.Attachment.RestartCovariance
public import Mathlib.Topology.ContinuousMap.Compact

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

theorem smooth_of_moderateLift {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants}
    {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℝ → C(Torus3, ℝ)} (h : Statements.IsModeratePhi43Lift N κ f C Z ψ) :
    IsSmoothOnSpaceTime f := by
  obtain ⟨noise, hn, _⟩ := h.2.1
  exact Potential.isSmoothOnSpaceTime_of_noise hn

theorem moderateLift_time_translate {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants}
    {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℝ → C(Torus3, ℝ)} (h : Statements.IsModeratePhi43Lift N κ f C Z ψ) (s : ℝ) :
    Statements.IsModeratePhi43Lift N κ (shiftForcing s f) C (Z.translate (s, 0))
      (fun t => ψ (s + t)) := by
  obtain ⟨hZ, hg, hψ⟩ := Attachment.restart_inputs_time_translate h.2.1 h.1 h.2.2 s
  exact ⟨hg, hZ, hψ⟩

/-- A chosen classical path; existence is from the classical well-posedness theorem. -/
@[expose] def smoothSolution (c : ℝ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) : ℝ → C(Torus3, ℝ) :=
  (classicalSolution_exists_unique c hf hx).1.choose

theorem smoothSolution_spec (c : ℝ) (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    IsClassicalSolution c f x (smoothSolution c f hf x hx) :=
  (classicalSolution_exists_unique c hf hx).1.choose_spec

/-- The state-valued classical curve on a compact local interval. -/
@[expose] def smoothCurve (η : NegExponent) (τ c : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    C(Icc (0 : ℝ) τ, HolderBesov η) where
  toFun r := toHolderBesov η (smoothSolution c f hf x hx r)
  continuous_toFun := (classicalSolution_continuousOn η
    (smoothSolution_spec c f hf x hx)).comp_continuous continuous_subtype_val
      (fun r => r.property.1)

theorem enorm_toHolderBesov (η : NegExponent) (x : C(Torus3, ℝ)) :
    ‖toHolderBesov η x‖ₑ = holderBesovENorm η x := by
  rw [← ofReal_norm, norm_toHolderBesov,
    ENNReal.ofReal_toReal (holderBesovENorm_lt_top η.2.le x).ne]

theorem edist_toHolderBesov (η : NegExponent) (x y : C(Torus3, ℝ)) :
    edist (toHolderBesov η x) (toHolderBesov η y) = holderBesovENorm η (x - y) := by
  rw [edist_dist, dist_eq_norm, ← toHolderBesov_sub, ofReal_norm, enorm_toHolderBesov]

end GlobalPhi43.Flow

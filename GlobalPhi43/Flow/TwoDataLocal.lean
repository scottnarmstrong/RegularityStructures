/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.Flow.TwoDataEndpoint
public import Phi43.Persistence.ClassicalSolution
public import Phi43.Persistence.Realising

/-!
# Concrete distinct-data local continuity

All enlarged models, their realisation, growth, compatibility and joint
measurability are supplied here. The short-time endpoint estimate chooses its
time and constant before the two independent data, paths and lifts, under a
common state-radius bound on the preceding interval.
-/

public section

open Set
open scoped ENNReal

namespace GlobalPhi43.Flow

open RegularityStructures RegularityStructures.Phi43

/-- The independent-data enlarged-family estimate, with the actual enlarged models. -/
theorem twoDataLocalLipschitz {κ : Kappa} {N : ℕ} (hN : 5 ≤ N)
    {η : NegExponent} (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    :
    ∀ T L B : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → ∃ t₀ K : ℝ, 0 < t₀ ∧ 1 ≤ K ∧
      ∀ (f g : SpaceTime → ℝ) (C C' : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ ψ' : ℝ → C(Torus3, ℝ)) (u₀ v₀ : C(Torus3, ℝ)) (u v : ℝ → C(Torus3, ℝ)),
        Statements.IsModeratePhi43Lift N κ f C Z ψ → Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        IsClassicalSolution (3 * C'.1 - 9 * C'.2) g v₀ v →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + t₀ → t ≤ T →
          (∀ r ∈ Set.Icc (0 : ℝ) t,
            holderBesovENorm η (u r) ≤ ENNReal.ofReal L ∧
            holderBesovENorm η (v r) ≤ ENNReal.ofReal L) →
          holderBesovENorm η (u t - v t) ≤
            ENNReal.ofReal K * (holderBesovENorm η (u s - v s) + Statements.phi43Dist κ η T Z Z' ψ ψ') := by
  have hN3 : 3 ≤ N := by omega
  exact twoDataLocalLipschitz_of_enlargedFamily hN hη hκη
    (fun noise Cg q hg C s => Persistence.enlargedRestartModel N κ noise Cg q hg C s)
    (fun noise Cg q hg C s _ => Persistence.enlargedRestartModel_compat N κ noise Cg q hg C s)
    (fun noise Cg q hg C s _ =>
      Persistence.enlargedRestartModel_isRealisingP N κ noise Cg q hg C hN3 s)
    (fun noise Cg q hg C s _ =>
      Persistence.enlargedRestartModel_growth_kappa N κ noise Cg q hg C s)
    (fun noise Cg q hg C s _ =>
      Persistence.enlargedRestartModel_isJointMeasurable N κ noise Cg q hg C s)

end GlobalPhi43.Flow

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import Phi43.ClassicalSolution
public import Phi43.Persistence
public import Phi43.LocalLipschitz
public import Phi43.StoppedContinuity.ReductionBody

/-!
# Persistence and stopped continuity of classical solutions

`RegularityStructures.Phi43.phi43ClassicalSolution_stoppedContinuity` proves the statement
`Statements.phi43ClassicalSolution_stoppedContinuity` of
`Phi43Statements.Steps.ClassicalSolutionStoppedContinuity` [Hai14, Proposition 9.8,
Corollary 7.12, Proposition 9.10]:

* clause (i), persistence: `Persistence.phi43_persistence` (restart fixed point on the enlarged structure
  for start times `s > 0`, identification of its reconstruction with the classical solution, time slices,
  and `persistence_at_zero` for `s = 0`);
* clause (ii), stopped continuity: `StoppedContinuity.stoppedContinuity_of_localLipschitzBody` applied to the
  local Lipschitz step `StoppedContinuity.phi43LocalLipschitz_of_enlargedFamily`, for the family of enlarged
  restarted models `Persistence.enlargedRestartModel` (time translates of the enlarged renormalised
  model), whose compatibility, realising, growth and measurability are `Persistence.enlargedRestartModel_*`.
-/

public section

namespace RegularityStructures.Phi43

/-- **Persistence and stopped continuity** of classical solutions of the renormalised `Φ⁴₃`
equation for smooth lifted noise. -/
theorem phi43ClassicalSolution_stoppedContinuity (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
    (η : RegularityStructures.NegExponent)
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hκη : κ.1 < -(1 / 2 : ℝ) - η) :
    (∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : RegularityStructures.SpaceTime → ℝ)
        (C : RegularityStructures.Phi43.RenormalisationConstants)
        (Z : RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup)
        (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) (u₀ : C(RegularityStructures.Torus3, ℝ))
        (u : ℝ → C(RegularityStructures.Torus3, ℝ)) (T : ℝ),
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ f C Z ψ →
        RegularityStructures.Phi43.IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → RegularityStructures.Phi43.Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Set.Icc (0 : ℝ) T, RegularityStructures.holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Set.Icc s (s + t₀),
            RegularityStructures.holderBesovENorm η (u t) ≤ ENNReal.ofReal R) ∧
    ∀ T L B ϵ : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (f g : RegularityStructures.SpaceTime → ℝ)
        (C C' : RegularityStructures.Phi43.RenormalisationConstants)
        (Z Z' : RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup)
        (ψ ψ' : ℝ → C(RegularityStructures.Torus3, ℝ)) (u₀ : C(RegularityStructures.Torus3, ℝ))
        (u v : ℝ → C(RegularityStructures.Torus3, ℝ)),
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ f C Z ψ →
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        RegularityStructures.Phi43.IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        RegularityStructures.Phi43.IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        RegularityStructures.Phi43.Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        RegularityStructures.Phi43.Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        RegularityStructures.Phi43.Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ s ∈ Set.Icc (0 : ℝ) t,
            RegularityStructures.holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
            RegularityStructures.holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
          RegularityStructures.holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ := by
  have hN3 : 3 ≤ N := le_trans (by norm_num) hN
  refine ⟨Persistence.phi43_persistence κ hκE N hN η hη hκη, ?_⟩
  exact StoppedContinuity.stoppedContinuity_of_localLipschitzBody
    (StoppedContinuity.phi43LocalLipschitz_of_enlargedFamily hN hη hκη
      (fun noise Cg q hg C s => Persistence.enlargedRestartModel N κ noise Cg q hg C s)
      (fun noise Cg q hg C s _ => Persistence.enlargedRestartModel_compat N κ noise Cg q hg C s)
      (fun noise Cg q hg C s _ =>
        Persistence.enlargedRestartModel_isRealisingP N κ noise Cg q hg C hN3 s)
      (fun noise Cg q hg C s _ => Persistence.enlargedRestartModel_growth_kappa N κ noise Cg q hg C s)
      (fun noise Cg q hg C s _ =>
        Persistence.enlargedRestartModel_isJointMeasurable N κ noise Cg q hg C s))

end RegularityStructures.Phi43

end

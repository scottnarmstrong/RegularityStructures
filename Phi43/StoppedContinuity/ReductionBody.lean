/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.StoppedContinuity.Iterate
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import Phi43.ClassicalSolution

/-!
# Stopped continuity of classical solutions from a local Lipschitz step

`stoppedContinuity_of_localLipschitzBody`: if, on a window of length `t₀` after any restart time
`s`, the `𝒞^η` distance of two classical solutions driven by two lifts grows at most by a factor
`K`, up to the distance `phi43Dist` of the lifts, then the solutions depend continuously on the lift
up to exit from the `L`-ball. This is the stopped-continuity part of
`Statements.phi43ClassicalSolution_stoppedContinuity`. The proof iterates the local step over
`⌈T/t₀⌉` restarts (`le_iterConst_mul`).
-/

public section

open ENNReal

namespace RegularityStructures.Phi43.StoppedContinuity

/-- **Stopped continuity from the local Lipschitz step.** On `[0, T]`, as long as two classical
solutions stay in the `L`-ball, their `𝒞^η` distance is at most `ϵ` once the distance of their
lifts is at most `δ`, uniformly over lifts of size at most `B`. -/
theorem stoppedContinuity_of_localLipschitzBody {κ : Kappa} {N : ℕ} {η : ℝ}
    (hloc :
    ∀ T L B : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → ∃ t₀ K : ℝ, 0 < t₀ ∧ 1 ≤ K ∧
      ∀ (f g : SpaceTime → ℝ) (C C' : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ ψ' : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ)) (u v : ℝ → C(Torus3, ℝ)),
        Statements.IsModeratePhi43Lift N κ f C Z ψ → Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + t₀ → t ≤ T →
          (∀ r ∈ Set.Icc (0 : ℝ) t,
            holderBesovENorm η (u r) ≤ ENNReal.ofReal L ∧
            holderBesovENorm η (v r) ≤ ENNReal.ofReal L) →
          holderBesovENorm η (u t - v t) ≤
            ENNReal.ofReal K * (holderBesovENorm η (u s - v s) + Statements.phi43Dist κ η T Z Z' ψ ψ')) :
    ∀ T L B ϵ : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (f g : SpaceTime → ℝ) (C C' : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ ψ' : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ)) (u v : ℝ → C(Torus3, ℝ)),
        Statements.IsModeratePhi43Lift N κ f C Z ψ → Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ s ∈ Set.Icc (0 : ℝ) t,
            holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
            holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
          holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ := by
  intro T L B ϵ hT hL hB hϵ
  obtain ⟨t₀, K, ht₀, hK, hstep⟩ := hloc T L B hT hL hB
  set n : ℕ := ⌈T / t₀⌉₊ with hn
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_ceil_iff]
    exact div_pos (by linarith) ht₀
  have hc1 : 1 ≤ iterConst K n := one_le_iterConst hK n hn1
  have hcpos : 0 < iterConst K n := by linarith
  refine ⟨ϵ / iterConst K n, div_pos hϵ hcpos, ?_⟩
  intro f g C C' Z Z' ψ ψ' u₀ u v hf hg hu hv hZ hZ' hd t ht hLt
  set δ := ϵ / iterConst K n with hδ
  have hδ0 : 0 ≤ δ := (div_pos hϵ hcpos).le
  let D : ℝ → ℝ≥0∞ := fun r => holderBesovENorm η (u r - v r)
  have hD0 : D 0 = 0 := by
    simp only [D, hu.initial, hv.initial, sub_self, holderBesovENorm_zero]
  have hTn : t ≤ n * t₀ := by
    have h1 : T / t₀ ≤ n := Nat.le_ceil _
    have h2 : T ≤ n * t₀ := by rwa [div_le_iff₀ ht₀] at h1
    exact ht.2.trans h2
  have key := le_iterConst_mul (D := D) (T := t) hD0 ht₀ hK hδ0 (fun s r hs hsr hrs hrt => by
      refine (hstep f g C C' Z Z' ψ ψ' u₀ u v hf hg hu hv hZ hZ' s r hs hsr hrs
        (hrt.trans ht.2) fun q hq => hLt q ⟨hq.1, hq.2.trans hrt⟩).trans ?_
      gcongr) n t ht.1 hTn le_rfl
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hδ, mul_div_cancel₀ _ hcpos.ne']

end RegularityStructures.Phi43.StoppedContinuity

end

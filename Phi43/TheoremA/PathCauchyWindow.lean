/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.PathCauchy
public import Phi43.ClassicalSolution.PathContinuity
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size

/-!
# Compact-window Cauchy extraction with a separate model horizon

The stopped-continuity estimate is stated on horizons at least one, while a lifetime
construction may request convergence on a shorter interval.  This module separates the
path horizon from the horizon used for model sizes and stopped estimates.
-/

public section

open Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

private theorem assembly_path_dist_of_holderBesovENorm_window
    {η : NegExponent} {f g : C(Torus3, ℝ)} {r : ℝ} (hr : 0 ≤ r)
    (h : holderBesovENorm η (f - g) ≤ ENNReal.ofReal r) :
    dist (toHolderBesov η f) (toHolderBesov η g) ≤ r := by
  rw [dist_eq_norm, ← toHolderBesov_sub, norm_toHolderBesov]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal hr)

theorem assembly_path_cauchy_from_stopped_window
    {κ : Kappa} {N : ℕ} {η : NegExponent} {T H : ℝ}
    (hT : 0 ≤ T) (hH : 1 ≤ H) (hTH : T ≤ H)
    (hStopped : ∀ H L B ϵ : ℝ, 1 ≤ H → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ,
      0 < δ ∧
      ∀ (f g : SpaceTime → ℝ)
        (C C' : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ ψ' : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ))
        (u v : ℝ → C(Torus3, ℝ)),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        Statements.phi43Size κ η H Z ψ ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η H Z' ψ' ≤ ENNReal.ofReal B →
        Statements.phi43Dist κ η H Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
        ∀ t ∈ Icc (0 : ℝ) H,
          (∀ s ∈ Icc (0 : ℝ) t,
            holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
            holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
          holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ)
    {L B : ℝ} (hL : 1 ≤ L) (hB : 1 ≤ B)
    {u₀ : C(Torus3, ℝ)} {f : ℕ → SpaceTime → ℝ}
    {C : ℕ → RenormalisationConstants}
    {Z : ℕ → Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℕ → ℝ → C(Torus3, ℝ)} {u : ℕ → ℝ → C(Torus3, ℝ)}
    (hLift : ∀ n, Statements.IsModeratePhi43Lift N κ (f n) (C n) (Z n) (ψ n))
    (hclass : ∀ n, IsClassicalSolution (3 * (C n).1 - 9 * (C n).2)
      (f n) u₀ (u n))
    (hsize : ∀ n, Statements.phi43Size κ η H (Z n) (ψ n) ≤ ENNReal.ofReal B)
    (d : ℕ → ℕ → ℝ≥0∞)
    (hmetric : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ n m : ℕ, K ≤ n → K ≤ m →
      d n m ≤ ENNReal.ofReal δ)
    (hdist : ∀ n m : ℕ,
      Statements.phi43Dist κ η H (Z n) (Z m) (ψ n) (ψ m) ≤ d n m)
    (hbound : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T,
      holderBesovENorm η (u n t) ≤ ENNReal.ofReal L) :
    CauchySeq (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => toHolderBesov η (u n t.1))
        (continuousOn_iff_continuous_domRestrict.mp
          ((classicalSolution_continuousOn η (hclass n)).mono Icc_subset_Ici_self))) := by
  have hnorm : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T,
      ‖toHolderBesov η (u n t)‖ ≤ L := by
    intro n t ht
    rw [norm_toHolderBesov]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound n t ht)).trans_eq
      (ENNReal.toReal_ofReal (zero_le_one.trans hL))
  let hbound' : ∃ L' : ℝ, ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T,
      ‖toHolderBesov η (u n t)‖ ≤ L' := ⟨L, hnorm⟩
  apply assembly_path_cauchy_of_steps hT
    (fun n t => toHolderBesov η (u n t))
    (fun n => classicalSolution_continuousOn η (hclass n)) d hmetric hbound'
  intro ϵ hϵ
  obtain ⟨δ, hδ, hδspec⟩ := hStopped H L B ϵ hH hL hB hϵ
  refine ⟨δ, hδ, ?_⟩
  intro n m hnm _ t ht
  apply assembly_path_dist_of_holderBesovENorm_window (le_of_lt hϵ)
  apply hδspec (f n) (f m) (C n) (C m) (Z n) (Z m) (ψ n) (ψ m) u₀
    (u n) (u m) (hLift n) (hLift m) (hclass n) (hclass m) (hsize n) (hsize m)
    ((hdist n m).trans hnm) t ⟨ht.1, ht.2.trans hTH⟩
  intro s hs
  exact ⟨hbound n s ⟨hs.1, hs.2.trans ht.2⟩,
    hbound m s ⟨hs.1, hs.2.trans ht.2⟩⟩

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43.ClassicalSolution
public import RegularityStructures.Torus.HolderBesov

/-!
# Persistence from positive start times to start time zero

The persistence clause (i) of `Statements.phi43ClassicalSolution_stoppedContinuity` quantifies
over start times `s ∈ [0, T]`.  `persistence_at_zero` shows that it follows from the version with
`s ∈ (0, T]`, using continuity of a classical solution at time `0` in the sup norm of `C(T³)`.
-/

public section

open ENNReal

namespace RegularityStructures.Phi43.Persistence

private theorem exists_small_dist {c : ℝ} {f : SpaceTime → ℝ} {u₀ : C(Torus3, ℝ)}
    {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 ≤ s → s < δ → ‖u s - u 0‖ < ε := by
  let F : C(Set.Ici (0 : ℝ) × Torus3, ℝ) :=
    ⟨fun p => u p.1.1 p.2, hu.continuousOn.comp_continuous
      (by fun_prop : Continuous fun p : Set.Ici (0 : ℝ) × Torus3 => (p.1.1, p.2))
      (fun p => ⟨p.1.2, Set.mem_univ _⟩)⟩
  have hc : Continuous (ContinuousMap.curry F) := (ContinuousMap.curry F).continuous
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1
    (hc.continuousAt (x := ⟨0, Set.mem_Ici.2 le_rfl⟩)) ε hε
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  have := h (x := ⟨s, hs⟩) (by
    rw [Subtype.dist_eq, Real.dist_eq]
    simpa [abs_of_nonneg hs] using hsδ)
  have e1 : ContinuousMap.curry F ⟨s, hs⟩ = u s := rfl
  have e2 : ContinuousMap.curry F ⟨0, Set.mem_Ici.2 le_rfl⟩ = u 0 := rfl
  rwa [e1, e2, dist_eq_norm] at this

private theorem exists_pos_le {c : ℝ} {f : SpaceTime → ℝ} {u₀ : C(Torus3, ℝ)}
    {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u) (η : NegExponent)
    {L : ℝ} (hL : 1 ≤ L) (hu0 : holderBesovENorm η (u 0) ≤ ENNReal.ofReal L)
    {t : ℝ} (ht : 0 < t) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ t ∧ holderBesovENorm η (u s') ≤ ENNReal.ofReal (2 * L) := by
  obtain ⟨δ, hδ, h⟩ := exists_small_dist hu (zero_lt_one' ℝ)
  refine ⟨min t (δ / 2), lt_min ht (half_pos hδ), min_le_left _ _, ?_⟩
  have hs0 : 0 < min t (δ / 2) := lt_min ht (half_pos hδ)
  have hlt : min t (δ / 2) < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hd := h _ hs0.le hlt
  have hη : (η : ℝ) ≤ 0 := η.2.le
  have h1 : holderBesovENorm η (u (min t (δ / 2)) - u 0) ≤ ENNReal.ofReal L := by
    refine (holderBesovENorm_le hη _).trans ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hd.le.trans hL)
  calc holderBesovENorm η (u (min t (δ / 2)))
      = holderBesovENorm η (u 0 + (u (min t (δ / 2)) - u 0)) := by rw [add_sub_cancel]
    _ ≤ holderBesovENorm η (u 0) + holderBesovENorm η (u (min t (δ / 2)) - u 0) :=
        holderBesovENorm_add_le _ _ _
    _ ≤ ENNReal.ofReal L + ENNReal.ofReal L := add_le_add hu0 h1
    _ = ENNReal.ofReal (2 * L) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

/-- Persistence for start times in `[0, T]` follows from persistence for start times in `(0, T]`
(the persistence clause (i) of `Statements.phi43ClassicalSolution_stoppedContinuity`). -/
theorem persistence_at_zero (κ : Kappa) (N : ℕ) (η : NegExponent)
    (hpos : ∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ)) (u : ℝ → C(Torus3, ℝ)) (T : ℝ),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Set.Ioc (0 : ℝ) T, holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Set.Icc s (s + t₀), holderBesovENorm η (u t) ≤ ENNReal.ofReal R) :
    ∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ)) (u : ℝ → C(Torus3, ℝ)) (T : ℝ),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Set.Icc (0 : ℝ) T, holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Set.Icc s (s + t₀), holderBesovENorm η (u t) ≤ ENNReal.ofReal R := by
  intro L B hL hB
  obtain ⟨t₀, R, ht₀, ht₁, h⟩ := hpos (2 * L) B (by linarith) hB
  refine ⟨t₀, max R L, ht₀, ht₁, fun f C Z ψ u₀ u T hlift hsol hT hsize s hs hsL t ht => ?_⟩
  have hLle : ENNReal.ofReal L ≤ ENNReal.ofReal (2 * L) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hRle : ENNReal.ofReal R ≤ ENNReal.ofReal (max R L) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  rcases hs.1.eq_or_lt with h0 | hspos
  · subst h0
    rcases ht.1.eq_or_lt with ht0 | htpos
    · subst ht0
      exact hsL.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    · obtain ⟨s', hs'0, hs't, hs'⟩ := exists_pos_le hsol η hL hsL htpos
      have h1 : s' ≤ T := by linarith [ht.2]
      exact (h f C Z ψ u₀ u T hlift hsol hT hsize s' ⟨hs'0, h1⟩ hs' t
        ⟨hs't, by linarith [ht.2]⟩).trans hRle
  · exact (h f C Z ψ u₀ u T hlift hsol hT hsize s ⟨hspos, hs.2⟩ (hsL.trans hLle) t ht).trans hRle

end RegularityStructures.Phi43.Persistence

end

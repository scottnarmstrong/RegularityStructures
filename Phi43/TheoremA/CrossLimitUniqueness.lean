/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Limit
public import Phi43.Uniqueness
public import Phi43.ClassicalSolution
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size
public import RegularityStructures.Torus.HolderBesov
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Cross-mollifier uniqueness of the stopped limit

The two approximation families need not be the same family, so the elementary uniqueness theorem
for one fixed family is not applicable directly.  This module records the corresponding argument
using the cross-model estimate: on bounded-limit paths, two approximants are close outside the
two size tails, the cross-model tail, and the two convergence-error events.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

universe u

private theorem assembly_holder_distance_of_bound
    {η : NegExponent} {f g : C(Torus3, ℝ)} {r : ℝ} (hr : 0 ≤ r)
    (h : holderBesovENorm η (f - g) ≤ ENNReal.ofReal r) :
    dist (toHolderBesov η f) (toHolderBesov η g) ≤ r := by
  rw [dist_eq_norm, ← toHolderBesov_sub η, norm_toHolderBesov]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal hr)

private theorem assembly_holderENorm_of_norm_bound
    {η : NegExponent} (g : C(Torus3, ℝ)) {R : ℝ}
    (h : ‖toHolderBesov η g‖ ≤ R) :
    holderBesovENorm η g ≤ ENNReal.ofReal R := by
  have htop : holderBesovENorm η g < ⊤ := holderBesovENorm_lt_top η.2.le g
  rw [norm_toHolderBesov] at h
  calc
    holderBesovENorm η g = ENNReal.ofReal (holderBesovENorm η g).toReal :=
      (ENNReal.ofReal_toReal htop.ne).symm
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal h

theorem assembly_cross_limit_unique
    {Ω : Type u} [MeasurableSpace Ω] {η : NegExponent} {κ : Kappa} {N : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {u₀ : C(Torus3, ℝ)}
    {u u' : ℝ → Ω → ℝ → C(Torus3, ℝ)}
    {τ τ' : Ω → ℝ≥0∞} {v v' : Ω → ℝ → HolderBesov η}
    {ξ ξ' : ℝ → Ω → SpaceTime → ℝ}
    {C C' : ℝ → RenormalisationConstants}
    {Z Z' : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ ψ' : ℝ → Ω → ℝ → C(Torus3, ℝ)}
    (hStopped : ∀ T L B ϵ : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (f g : SpaceTime → ℝ) (C C' : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ ψ' : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ))
        (u v : ℝ → C(Torus3, ℝ)),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
        ∀ t ∈ Icc (0 : ℝ) T,
          (∀ s ∈ Icc (0 : ℝ) t,
            holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
            holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
          holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ)
    (hsize : ∀ T : ℝ, 1 ≤ T → ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ,
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        P {ω | ENNReal.ofReal B < Statements.phi43Size κ η T (Z ε ω) (ψ ε ω)} ≤
          ENNReal.ofReal ϑ)
    (hsize' : ∀ T : ℝ, 1 ≤ T → ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ,
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        P {ω | ENNReal.ofReal B < Statements.phi43Size κ η T (Z' ε ω) (ψ' ε ω)} ≤
          ENNReal.ofReal ϑ)
    (hcross : ∀ T : ℝ, 1 ≤ T → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun e : ℝ × ℝ =>
        P {ω | ENNReal.ofReal δ < Statements.phi43Dist κ η T
          (Z e.1 ω) (Z' e.2 ω) (ψ e.1 ω) (ψ' e.2 ω)})
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0))
    (hLift : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift N κ (ξ ε ω) (C ε) (Z ε ω) (ψ ε ω))
    (hLift' : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift N κ (ξ' ε ω) (C' ε) (Z' ε ω) (ψ' ε ω))
    (hclass : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω,
      IsClassicalSolution (3 * (C ε).1 - 9 * (C ε).2)
        (ξ ε ω) u₀ (u ε ω))
    (hclass' : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω,
      IsClassicalSolution (3 * (C' ε).1 - 9 * (C' ε).2)
        (ξ' ε ω) u₀ (u' ε ω))
    (h : IsPhi43Limit P η u₀ u τ v)
    (h' : IsPhi43Limit P η u₀ u' τ' v') :
    τ' =ᵐ[P] τ ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      ENNReal.ofReal t < τ ω → v' ω t = v ω t := by
  let D (T δ : ℝ) : Set Ω := {ω |
    ENNReal.ofReal T < τ ω ∧ ENNReal.ofReal T < τ' ω ∧
      ∃ t ∈ Icc (0 : ℝ) T, 2 * δ < ‖v ω t - v' ω t‖}
  let VBound (T : ℝ) (M : ℕ) : Set Ω := {ω |
    ENNReal.ofReal T < τ ω ∧ ENNReal.ofReal T < τ' ω ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖v ω t‖ ≤ (M : ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖v' ω t‖ ≤ (M : ℝ)}
  have hDcover : ∀ T δ : ℝ, 0 < T → 0 < δ →
      D T δ ⊆ ⋃ M : ℕ, D T δ ∩ VBound T M := by
    intro T δ hT hδ ω hω
    have hDmem := hω
    dsimp [D] at hω
    rcases hω with ⟨hτ, hτ', t, ht, hdis⟩
    have hvcont : ContinuousOn (v ω) (Icc (0 : ℝ) T) :=
      (h.continuousOn ω).mono fun t ht =>
        ⟨ht.1, (ENNReal.ofReal_mono ht.2).trans_lt hτ⟩
    have hv'cont : ContinuousOn (v' ω) (Icc (0 : ℝ) T) :=
      (h'.continuousOn ω).mono fun t ht =>
        ⟨ht.1, (ENNReal.ofReal_mono ht.2).trans_lt hτ'⟩
    obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hvcont
    obtain ⟨A', hA'⟩ := isCompact_Icc.exists_bound_of_continuousOn hv'cont
    obtain ⟨M, hM⟩ := exists_nat_ge (max A A')
    refine Set.mem_iUnion.mpr ⟨M, ?_⟩
    refine ⟨hDmem, hτ, hτ', ?_, ?_⟩
    · intro t ht
      exact (hA t ht).trans ((le_max_left A A').trans (by exact_mod_cast hM))
    · intro t ht
      exact (hA' t ht).trans ((le_max_right A A').trans (by exact_mod_cast hM))
  have hDzero : ∀ T δ : ℝ, 0 < T → 0 < δ → P (D T δ) = 0 := by
    intro T δ hT hδ
    have hMzero : ∀ M : ℕ, P (D T δ ∩ VBound T M) = 0 := by
      intro M
      have hMbound : ∀ q : ℝ, 0 < q → P (D T δ ∩ VBound T M) ≤
          ENNReal.ofReal (2 * q) := by
        intro q hq
        let A : ℝ := max 1 ((M : ℝ) + δ + 1)
        have hA : 1 ≤ A := le_max_left _ _
        obtain ⟨K, hK⟩ := exists_nat_ge T
        let H : ℕ := max 1 K
        have hH : (1 : ℝ) ≤ H := by
          dsimp [H]
          exact_mod_cast le_max_left 1 K
        have hTH : T ≤ (H : ℝ) := hK.trans (by
          dsimp [H]
          exact_mod_cast le_max_right 1 K)
        obtain ⟨B, hB⟩ := hsize (H : ℝ) hH q hq
        obtain ⟨B', hB'⟩ := hsize' (H : ℝ) hH q hq
        let B₀ : ℝ := max (max B B') 1
        have hB₀ : 1 ≤ B₀ := le_max_right _ _
        obtain ⟨d, hd, hδspec⟩ := hStopped (H : ℝ) A B₀ δ hH hA hB₀
          (by positivity)
        have hcross_ev : {z : ℝ × ℝ |
            P {ω | ENNReal.ofReal d < Statements.phi43Dist κ η (H : ℝ)
              (Z z.1 ω) (Z' z.2 ω) (ψ z.1 ω) (ψ' z.2 ω)} <
              ENNReal.ofReal q} ∈ (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)) := by
          exact (tendsto_order.1 (hcross (H : ℝ) hH d hd)).2
            (ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq)
        obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_prod_iff.mp hcross_ev
        let E₁ (e : ℝ) : Set Ω := {ω |
          ENNReal.ofReal T < τ ω ∧ ∃ t ∈ Icc (0 : ℝ) T,
            δ / 2 < ‖toHolderBesov η (u e ω t) - v ω t‖}
        let E₂ (e : ℝ) : Set Ω := {ω |
          ENNReal.ofReal T < τ' ω ∧ ∃ t ∈ Icc (0 : ℝ) T,
            δ / 2 < ‖toHolderBesov η (u' e ω t) - v' ω t‖}
        let S₁ (e : ℝ) : Set Ω := {ω |
          ENNReal.ofReal B₀ < Statements.phi43Size κ η (H : ℝ) (Z e ω) (ψ e ω)}
        let S₂ (e : ℝ) : Set Ω := {ω |
          ENNReal.ofReal B₀ < Statements.phi43Size κ η (H : ℝ) (Z' e ω) (ψ' e ω)}
        let M₁₂ (e e' : ℝ) : Set Ω := {ω |
          ENNReal.ofReal d < Statements.phi43Dist κ η (H : ℝ)
            (Z e ω) (Z' e' ω) (ψ e ω) (ψ' e' ω)}
        let L₁ (e : ℝ) (he : e ∈ Ioc (0 : ℝ) 1) : Set Ω := {ω |
          ¬ Statements.IsModeratePhi43Lift N κ (ξ e ω) (C e) (Z e ω) (ψ e ω)}
        let L₂ (e : ℝ) (he : e ∈ Ioc (0 : ℝ) 1) : Set Ω := {ω |
          ¬ Statements.IsModeratePhi43Lift N κ (ξ' e ω) (C' e) (Z' e ω) (ψ' e ω)}
        have hE1 : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
            P {ω | ENNReal.ofReal T < τ ω ∧ ∃ t ∈ Icc (0 : ℝ) T,
              δ / 2 < ‖toHolderBesov η (u e ω t) - v ω t‖} <
                ENNReal.ofReal q := by
          simpa [E₁] using (tendsto_order.1
            (h.converges T hT (δ / 2) (by linarith))).2
            (ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq)
        have hE2 : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
            P {ω | ENNReal.ofReal T < τ' ω ∧ ∃ t ∈ Icc (0 : ℝ) T,
              δ / 2 < ‖toHolderBesov η (u' e ω t) - v' ω t‖} <
                ENNReal.ofReal q := by
          simpa [E₂] using (tendsto_order.1
            (h'.converges T hT (δ / 2) (by linarith))).2
            (ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq)
        have hpair : ∀ᶠ z : ℝ × ℝ in
            (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)),
            z.1 ∈ Ioc (0 : ℝ) 1 ∧ z.2 ∈ Ioc (0 : ℝ) 1 ∧ U z.1 ∧ V z.2 ∧
              P (E₁ z.1) < ENNReal.ofReal q ∧
              P (E₂ z.2) < ENNReal.ofReal q ∧
              P (M₁₂ z.1 z.2) < ENNReal.ofReal q := by
          apply Filter.eventually_prod_iff.mpr
          refine ⟨fun e => U e ∧ e ∈ Ioc (0 : ℝ) 1 ∧
              P (E₁ e) < ENNReal.ofReal q,
            ?_, fun e => V e ∧ e ∈ Ioc (0 : ℝ) 1 ∧
              P (E₂ e) < ENNReal.ofReal q,
            ?_, ?_⟩
          · filter_upwards [hU, Ioc_mem_nhdsGT one_pos, hE1] with e heU heI heE
            exact ⟨heU, heI, heE⟩
          · filter_upwards [hV, Ioc_mem_nhdsGT one_pos, hE2] with e heV heI heE
            exact ⟨heV, heI, heE⟩
          · intro e hee e' hee'
            exact ⟨hee.2.1, hee'.2.1, hee.1, hee'.1,
              hee.2.2, hee'.2.2, hUV hee.1 hee'.1⟩
        have hGlim : Tendsto (fun z : ℝ × ℝ =>
            ENNReal.ofReal q + ENNReal.ofReal q + P (M₁₂ z.1 z.2) +
              P (E₁ z.1) + P (E₂ z.2))
            ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))
            (𝓝 (ENNReal.ofReal q + ENNReal.ofReal q)) := by
          have hm := hcross (H : ℝ) hH d hd
          have he1 := h.converges T hT (δ / 2) (by linarith)
          have he2 := h'.converges T hT (δ / 2) (by linarith)
          have he1' : Tendsto (fun z : ℝ × ℝ => P (E₁ z.1))
              ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0) :=
            he1.comp tendsto_fst
          have he2' : Tendsto (fun z : ℝ × ℝ => P (E₂ z.2))
              ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0) :=
            he2.comp tendsto_snd
          have hsum : Tendsto
              (fun z : ℝ × ℝ => ENNReal.ofReal q +
                (ENNReal.ofReal q + P (M₁₂ z.1 z.2)))
              ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)))
              (𝓝 (ENNReal.ofReal q + (ENNReal.ofReal q + 0))) :=
            tendsto_const_nhds.add (tendsto_const_nhds.add hm)
          simpa [M₁₂, E₁, E₂, Function.comp_def, add_assoc] using
            (hsum.add he1').add he2'
        have hbound : ∀ᶠ z : ℝ × ℝ in
            (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)),
            P (D T δ ∩ VBound T M) ≤
              ENNReal.ofReal q + ENNReal.ofReal q + P (M₁₂ z.1 z.2) +
                P (E₁ z.1) + P (E₂ z.2) := by
          filter_upwards [hpair] with z hz
          have hS₁ : P (S₁ z.1) ≤ ENNReal.ofReal q := by
            apply (measure_mono ?_).trans (hB z.1 hz.1)
            intro ω hω
            change ENNReal.ofReal B₀ < Statements.phi43Size κ η (H : ℝ)
              (Z z.1 ω) (ψ z.1 ω) at hω
            change ENNReal.ofReal B < Statements.phi43Size κ η (H : ℝ)
              (Z z.1 ω) (ψ z.1 ω)
            have hBB₀ : B ≤ B₀ := by
              dsimp [B₀]
              exact (le_max_left B B').trans (le_max_left (max B B') 1)
            exact (ENNReal.ofReal_mono hBB₀).trans_lt hω
          have hS₂ : P (S₂ z.2) ≤ ENNReal.ofReal q := by
            apply (measure_mono ?_).trans (hB' z.2 hz.2.1)
            intro ω hω
            change ENNReal.ofReal B₀ < Statements.phi43Size κ η (H : ℝ)
              (Z' z.2 ω) (ψ' z.2 ω) at hω
            change ENNReal.ofReal B' < Statements.phi43Size κ η (H : ℝ)
              (Z' z.2 ω) (ψ' z.2 ω)
            have hB'B₀ : B' ≤ B₀ := by
              dsimp [B₀]
              exact (le_max_right B B').trans (le_max_left (max B B') 1)
            exact (ENNReal.ofReal_mono hB'B₀).trans_lt hω
          have hL₁ : P (L₁ z.1 hz.1) = 0 := by
            simpa only [L₁] using (ae_iff.mp (hLift z.1 hz.1))
          have hL₂ : P (L₂ z.2 hz.2.1) = 0 := by
            simpa only [L₂] using (ae_iff.mp (hLift' z.2 hz.2.1))
          have hsub : D T δ ∩ VBound T M ⊆
              S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1 ∪ E₂ z.2 ∪
                L₁ z.1 hz.1 ∪ L₂ z.2 hz.2.1 := by
            intro ω hω
            by_cases hs₁ : ω ∈ S₁ z.1
            · simp [hs₁]
            · by_cases hs₂ : ω ∈ S₂ z.2
              · simp [hs₂]
              · by_cases hm : ω ∈ M₁₂ z.1 z.2
                · simp [hm]
                · by_cases he₁ : ω ∈ E₁ z.1
                  · simp [he₁]
                  · by_cases he₂ : ω ∈ E₂ z.2
                    · simp [he₂]
                    · by_cases hl₁ : ω ∈ L₁ z.1 hz.1
                      · simp [hl₁]
                      · by_cases hl₂ : ω ∈ L₂ z.2 hz.2.1
                        · simp [hl₂]
                        · have hDω := hω.1
                          dsimp [D] at hDω
                          rcases hDω with ⟨hτT, hτ'T, t, ht, hbad⟩
                          have hVω := hω.2
                          dsimp [VBound] at hVω
                          have h1 : ∀ s ∈ Icc (0 : ℝ) T,
                              ‖toHolderBesov η (u z.1 ω s)‖ ≤ A := by
                            intro s hs
                            have he : ‖toHolderBesov η (u z.1 ω s) - v ω s‖ ≤ δ / 2 := by
                              by_contra hnot
                              apply he₁
                              exact ⟨hτT, s, hs, lt_of_not_ge hnot⟩
                            have hv := hVω.2.2.1 s hs
                            calc
                              ‖toHolderBesov η (u z.1 ω s)‖ ≤
                                  ‖toHolderBesov η (u z.1 ω s) - v ω s‖ + ‖v ω s‖ :=
                                calc
                                  ‖toHolderBesov η (u z.1 ω s)‖ =
                                      ‖(toHolderBesov η (u z.1 ω s) - v ω s) +
                                        v ω s‖ := by
                                      congr 1
                                      abel
                                  _ ≤ _ := norm_add_le _ _
                              _ ≤ δ / 2 + (M : ℝ) := add_le_add he hv
                              _ ≤ A := by
                                have hA' : (M : ℝ) + δ + 1 ≤ A := by
                                  dsimp [A]
                                  exact le_max_right _ _
                                linarith
                          have h2 : ∀ s ∈ Icc (0 : ℝ) T,
                              ‖toHolderBesov η (u' z.2 ω s)‖ ≤ A := by
                            intro s hs
                            have he : ‖toHolderBesov η (u' z.2 ω s) - v' ω s‖ ≤ δ / 2 := by
                              by_contra hnot
                              apply he₂
                              exact ⟨hτ'T, s, hs, lt_of_not_ge hnot⟩
                            have hv := hVω.2.2.2 s hs
                            calc
                              ‖toHolderBesov η (u' z.2 ω s)‖ ≤
                                  ‖toHolderBesov η (u' z.2 ω s) - v' ω s‖ + ‖v' ω s‖ :=
                                calc
                                  ‖toHolderBesov η (u' z.2 ω s)‖ =
                                      ‖(toHolderBesov η (u' z.2 ω s) - v' ω s) +
                                        v' ω s‖ := by
                                      congr 1
                                      abel
                                  _ ≤ _ := norm_add_le _ _
                              _ ≤ δ / 2 + (M : ℝ) := add_le_add he hv
                              _ ≤ A := by
                                have hA' : (M : ℝ) + δ + 1 ≤ A := by
                                  dsimp [A]
                                  exact le_max_right _ _
                                linarith
                          have hL₁' : Statements.IsModeratePhi43Lift N κ
                              (ξ z.1 ω) (C z.1) (Z z.1 ω) (ψ z.1 ω) := by
                            exact not_not.mp (by simpa [L₁] using hl₁)
                          have hL₂' : Statements.IsModeratePhi43Lift N κ
                              (ξ' z.2 ω) (C' z.2) (Z' z.2 ω) (ψ' z.2 ω) := by
                            exact not_not.mp (by simpa [L₂] using hl₂)
                          have hs₁' : Statements.phi43Size κ η (H : ℝ)
                              (Z z.1 ω) (ψ z.1 ω) ≤ ENNReal.ofReal B₀ :=
                            le_of_not_gt (by simpa [S₁] using hs₁)
                          have hs₂' : Statements.phi43Size κ η (H : ℝ)
                              (Z' z.2 ω) (ψ' z.2 ω) ≤ ENNReal.ofReal B₀ :=
                            le_of_not_gt (by simpa [S₂] using hs₂)
                          have hm' : Statements.phi43Dist κ η (H : ℝ)
                              (Z z.1 ω) (Z' z.2 ω) (ψ z.1 ω) (ψ' z.2 ω) ≤
                              ENNReal.ofReal d := le_of_not_gt (by simpa [M₁₂] using hm)
                          have hdif := hδspec (ξ z.1 ω) (ξ' z.2 ω) (C z.1) (C' z.2)
                            (Z z.1 ω) (Z' z.2 ω) (ψ z.1 ω) (ψ' z.2 ω) u₀
                            (u z.1 ω) (u' z.2 ω) hL₁' hL₂'
                            (hclass z.1 hz.1 ω) (hclass' z.2 hz.2.1 ω) hs₁' hs₂' hm'
                            t ⟨ht.1, ht.2.trans hTH⟩ (by
                              intro s hs
                              exact ⟨assembly_holderENorm_of_norm_bound _
                                  (h1 s ⟨hs.1, hs.2.trans ht.2⟩),
                                assembly_holderENorm_of_norm_bound _
                                  (h2 s ⟨hs.1, hs.2.trans ht.2⟩)⟩)
                          have hdist := assembly_holder_distance_of_bound
                            (le_of_lt (by positivity)) hdif
                          have hvtri : ‖v ω t - v' ω t‖ ≤
                              ‖v ω t - toHolderBesov η (u z.1 ω t)‖ +
                              ‖toHolderBesov η (u z.1 ω t) -
                                toHolderBesov η (u' z.2 ω t)‖ +
                              ‖toHolderBesov η (u' z.2 ω t) - v' ω t‖ := by
                            calc
                              _ = ‖(v ω t - toHolderBesov η (u z.1 ω t)) +
                                  (toHolderBesov η (u z.1 ω t) -
                                    toHolderBesov η (u' z.2 ω t)) +
                                  (toHolderBesov η (u' z.2 ω t) - v' ω t)‖ := by
                                congr 1
                                abel
                              _ ≤ _ := by
                                calc
                                  _ ≤ ‖(v ω t - toHolderBesov η (u z.1 ω t)) +
                                      (toHolderBesov η (u z.1 ω t) -
                                        toHolderBesov η (u' z.2 ω t))‖ +
                                      ‖toHolderBesov η (u' z.2 ω t) - v' ω t‖ :=
                                    norm_add_le _ _
                                  _ ≤ _ := add_le_add
                                    (norm_add_le (v ω t - toHolderBesov η (u z.1 ω t))
                                      (toHolderBesov η (u z.1 ω t) -
                                        toHolderBesov η (u' z.2 ω t))) le_rfl
                          have he₁' : ‖toHolderBesov η (u z.1 ω t) - v ω t‖ ≤ δ / 2 := by
                            by_contra hnot
                            apply he₁
                            exact ⟨hτT, t, ht, lt_of_not_ge hnot⟩
                          have he₂' : ‖toHolderBesov η (u' z.2 ω t) - v' ω t‖ ≤ δ / 2 := by
                            by_contra hnot
                            apply he₂
                            exact ⟨hτ'T, t, ht, lt_of_not_ge hnot⟩
                          have hdist' : ‖toHolderBesov η (u z.1 ω t) -
                              toHolderBesov η (u' z.2 ω t)‖ ≤ δ := by
                            simpa only [dist_eq_norm] using hdist
                          have he₁'' : ‖v ω t - toHolderBesov η (u z.1 ω t)‖ ≤ δ / 2 := by
                            simpa [norm_sub_rev] using he₁'
                          exfalso
                          linarith [hbad, hvtri, he₁'', he₂', hdist']
          have hmu' : P (D T δ ∩ VBound T M) ≤
              P (S₁ z.1) + P (S₂ z.2) + P (M₁₂ z.1 z.2) +
                P (E₁ z.1) + P (E₂ z.2) + P (L₁ z.1 hz.1) +
                P (L₂ z.2 hz.2.1) := by
            have hmu₂ : P (S₁ z.1 ∪ S₂ z.2) ≤
                P (S₁ z.1) + P (S₂ z.2) := measure_union_le _ _
            have hmu₃ : P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2) ≤
                P (S₁ z.1) + P (S₂ z.2) + P (M₁₂ z.1 z.2) := by
              calc
                _ ≤ P (S₁ z.1 ∪ S₂ z.2) + P (M₁₂ z.1 z.2) := measure_union_le _ _
                _ ≤ _ := add_le_add_left hmu₂ _
            have hmu₄ : P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1) ≤
                P (S₁ z.1) + P (S₂ z.2) + P (M₁₂ z.1 z.2) + P (E₁ z.1) := by
              calc
                _ ≤ P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2) + P (E₁ z.1) :=
                  measure_union_le _ _
                _ ≤ _ := add_le_add_left hmu₃ _
            have hmu₅ : P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1 ∪ E₂ z.2) ≤
                P (S₁ z.1) + P (S₂ z.2) + P (M₁₂ z.1 z.2) +
                  P (E₁ z.1) + P (E₂ z.2) := by
              calc
                _ ≤ P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1) +
                    P (E₂ z.2) := measure_union_le _ _
                _ ≤ _ := add_le_add_left hmu₄ _
            have hmu₆ : P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1 ∪ E₂ z.2 ∪
                L₁ z.1 hz.1) ≤
                P (S₁ z.1) + P (S₂ z.2) + P (M₁₂ z.1 z.2) +
                  P (E₁ z.1) + P (E₂ z.2) + P (L₁ z.1 hz.1) := by
              calc
                _ ≤ P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1 ∪ E₂ z.2) +
                    P (L₁ z.1 hz.1) := measure_union_le _ _
                _ ≤ _ := add_le_add_left hmu₅ _
            calc
              _ ≤ P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1 ∪
                  E₂ z.2 ∪ L₁ z.1 hz.1 ∪ L₂ z.2 hz.2.1) := measure_mono hsub
              _ ≤ _ := calc
                _ ≤ P (S₁ z.1 ∪ S₂ z.2 ∪ M₁₂ z.1 z.2 ∪ E₁ z.1 ∪ E₂ z.2 ∪
                    L₁ z.1 hz.1) + P (L₂ z.2 hz.2.1) := measure_union_le _ _
                _ ≤ _ := add_le_add_left hmu₆ _
          calc
            P (D T δ ∩ VBound T M) ≤
                P (S₁ z.1) + P (S₂ z.2) + P (M₁₂ z.1 z.2) +
                  P (E₁ z.1) + P (E₂ z.2) + P (L₁ z.1 hz.1) +
            P (L₂ z.2 hz.2.1) := hmu'
            _ ≤ ENNReal.ofReal q + ENNReal.ofReal q + P (M₁₂ z.1 z.2) +
                P (E₁ z.1) + P (E₂ z.2) := by
              calc
                _ ≤ ENNReal.ofReal q + P (S₂ z.2) + P (M₁₂ z.1 z.2) +
                    P (E₁ z.1) + P (E₂ z.2) + P (L₁ z.1 hz.1) +
                    P (L₂ z.2 hz.2.1) := by
                  gcongr
                _ ≤ ENNReal.ofReal q + ENNReal.ofReal q + P (M₁₂ z.1 z.2) +
                    P (E₁ z.1) + P (E₂ z.2) + P (L₁ z.1 hz.1) +
                    P (L₂ z.2 hz.2.1) := by
                  gcongr
                _ ≤ _ := by simp [hL₁, hL₂]
        have hbound' := ge_of_tendsto hGlim hbound
        calc
          P (D T δ ∩ VBound T M) ≤
              ENNReal.ofReal q + ENNReal.ofReal q := by
            simpa [add_assoc] using hbound'
          _ = ENNReal.ofReal (2 * q) := by
            rw [← ENNReal.ofReal_add (le_of_lt hq) (le_of_lt hq)]
            congr 1
            ring
      apply le_antisymm
      · refine ENNReal.le_of_forall_pos_le_add ?_
        intro q hq htop
        have hq' : 0 < (q : ℝ) / 4 := by positivity
        have hqbound := hMbound ((q : ℝ) / 4) hq'
        have hqle : P (D T δ ∩ VBound T M) ≤ (q : ℝ≥0∞) := by
          calc
            P (D T δ ∩ VBound T M) ≤ ENNReal.ofReal (2 * ((q : ℝ) / 4)) := hqbound
            _ ≤ (q : ℝ≥0∞) := by
              rw [show 2 * ((q : ℝ) / 4) = (q : ℝ) / 2 by ring]
              have hqhalf : (q : ℝ) / 2 ≤ (q : ℝ) := by
                linarith [show (0 : ℝ) ≤ q by positivity]
              exact (ENNReal.ofReal_mono hqhalf).trans_eq ENNReal.ofReal_coe_nnreal
        simpa using hqle
      · exact bot_le
    have hUnion : P (⋃ M : ℕ, D T δ ∩ VBound T M) = 0 :=
      measure_iUnion_null hMzero
    exact le_antisymm ((measure_mono (hDcover T δ hT hδ)).trans_eq hUnion) bot_le
  let E : Set Ω := ⋃ q : {q : ℚ // 0 < q}, ⋃ n : ℕ,
    D (q : ℝ) (1 / ((n : ℝ) + 1))
  have hN : P E = 0 := by
    dsimp [E]
    refine measure_iUnion_null fun q => measure_iUnion_null fun n => ?_
    exact hDzero (q : ℝ) (1 / ((n : ℝ) + 1))
      (by exact_mod_cast q.2) (by positivity)
  have hEq : ∀ {ω : Ω} {t : ℝ}, ω ∉ E → 0 ≤ t →
      ENNReal.ofReal t < τ ω → ENNReal.ofReal t < τ' ω →
      v ω t = v' ω t := by
    intro ω t hω ht htτ htτ'
    obtain ⟨q, hq0, htq, hqτ⟩ :=
      ENNReal.lt_iff_exists_rat_btwn.1 (lt_min htτ htτ')
    change ENNReal.ofReal t < ENNReal.ofReal q at htq
    change ENNReal.ofReal q < min (τ ω) (τ' ω) at hqτ
    have htq' : t < q := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 htq
    have hqpos : (0 : ℚ) < q := by exact_mod_cast ht.trans_lt htq'
    by_contra hne
    have hd : 0 < ‖v ω t - v' ω t‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hd)
    apply hω
    dsimp [E]
    refine mem_iUnion.2 ⟨⟨q, hqpos⟩, mem_iUnion.2 ⟨n, ?_⟩⟩
    refine ⟨hqτ.trans_le (min_le_left _ _), hqτ.trans_le (min_le_right _ _),
      t, ⟨ht, htq'.le⟩, ?_⟩
    linarith
  have hnot : ∀ ω, ω ∉ E → τ ω = τ' ω := by
    intro ω hω
    rcases lt_trichotomy (τ ω) (τ' ω) with hlt | heq | hgt
    · have hfin : τ ω ≠ ⊤ := (hlt.trans_le le_top).ne
      set R := (τ ω).toReal
      have hsub : Icc 0 R ⊆ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ' ω} := by
        rintro s ⟨hs0, hsR⟩
        refine ⟨hs0, lt_of_le_of_lt ?_ hlt⟩
        calc
          ENNReal.ofReal s ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hsR
          _ = τ ω := ENNReal.ofReal_toReal hfin
      obtain ⟨C₀, hC₀⟩ :=
        isCompact_Icc.exists_bound_of_continuousOn ((h'.continuousOn ω).mono hsub)
      have hbdd : BddAbove ((fun s => ‖v ω s‖) ''
          {s | 0 ≤ s ∧ ENNReal.ofReal s < τ ω}) := by
        refine ⟨C₀, ?_⟩
        rintro _ ⟨s, ⟨hs0, hsτ⟩, rfl⟩
        have hsR : s ≤ R :=
          ((ENNReal.ofReal_lt_iff_lt_toReal hs0 hfin).1 hsτ).le
        change ‖v ω s‖ ≤ C₀
        rw [hEq hω hs0 hsτ (hsτ.trans hlt)]
        exact hC₀ s ⟨hs0, hsR⟩
      exact absurd hbdd (h.explosion ω (hlt.trans_le le_top))
    · exact heq
    · have hfin : τ' ω ≠ ⊤ := (hgt.trans_le le_top).ne
      set R := (τ' ω).toReal
      have hsub : Icc 0 R ⊆ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω} := by
        rintro s ⟨hs0, hsR⟩
        refine ⟨hs0, lt_of_le_of_lt ?_ hgt⟩
        calc
          ENNReal.ofReal s ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hsR
          _ = τ' ω := ENNReal.ofReal_toReal hfin
      obtain ⟨C₀, hC₀⟩ :=
        isCompact_Icc.exists_bound_of_continuousOn ((h.continuousOn ω).mono hsub)
      have hbdd : BddAbove ((fun s => ‖v' ω s‖) ''
          {s | 0 ≤ s ∧ ENNReal.ofReal s < τ' ω}) := by
        refine ⟨C₀, ?_⟩
        rintro _ ⟨s, ⟨hs0, hsτ'⟩, rfl⟩
        have hsR : s ≤ R :=
          ((ENNReal.ofReal_lt_iff_lt_toReal hs0 hfin).1 hsτ').le
        change ‖v' ω s‖ ≤ C₀
        rw [← hEq hω hs0 (hsτ'.trans hgt) hsτ']
        exact hC₀ s ⟨hs0, hsR⟩
      exact absurd hbdd (h'.explosion ω (hgt.trans_le le_top))
  have hAE : ∀ᵐ ω ∂P, ω ∉ E := by
    exact (measure_eq_zero_iff_ae_notMem.mp hN)
  refine ⟨hAE.mono fun ω hω => (hnot ω hω).symm, ?_⟩
  filter_upwards [hAE] with ω hω t ht htτ
  exact (hEq hω ht htτ ((hnot ω hω) ▸ htτ)).symm

end RegularityStructures.Phi43

end

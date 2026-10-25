/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.Step
public import Phi43.ClassicalSolution
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The local Lipschitz step for classical solutions, conditional on a family of enlarged models

`phi43LocalLipschitz_of_enlargedFamily`: given, for every noise, growth data, renormalisation
constants and restart time `s ≥ 0`, an enlarged model compatible with the translate by `(s, 0)` of the
renormalised canonical model, realising, with qualitative growth and jointly measurable, the local
Lipschitz step holds: for two classical solutions that stay in the `L`-ball of `𝒞^η`, driven by lifts
of size at most `B`,
`‖u t - v t‖_η ≤ K (‖u s - v s‖_η + phi43Dist)` for `0 ≤ s ≤ t ≤ s + t₀`, `t ≤ T`, with the
explicit time `t₀ = stepTime L B` and constant `K = max 1 (stepK L B)`. This is the uniform
Lipschitz dependence of the local solution on the model and the datum [Hai14, Theorem 7.8,
Corollary 7.12], in the form of the hypothesis of `stoppedContinuity_of_localLipschitzBody`.

* For `s > 0` this is `lipschitz_step_of_restartModels`, applied to the family at the restart `s`.
* For `s = 0` the two solutions have the same initial datum; the step from `s' ∈ (0, t]` and the
  continuity of both solutions at `0` in the sup norm give the bound with `‖u(s') - v(s')‖_η → 0`.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.StoppedContinuity

open RegularityStructures.Phi43.LocalLipschitz RegularityStructures.Phi43.LiftBounds

private theorem noise_growth_family {f : SpaceTime → ℝ} (hf : Statements.HasPhi43NoiseGrowth f)
    (noise : CanonicalNoise)
    (hnz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2)) :
    ∃ (Cg : ℝ) (q : ℕ), ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
  obtain ⟨Cg, q, h⟩ := hf
  refine ⟨Cg, q, fun k hk z => ?_⟩
  have : noise.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hnz
  rw [this]
  exact h k hk z

private theorem exists_small_dist_sol {c : ℝ} {f : SpaceTime → ℝ} {u₀ : C(Torus3, ℝ)}
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

/-- Two classical solutions with the same initial datum are close in `C^η` near `t = 0`. -/
private theorem exists_pos_sub_le {c c' : ℝ} {f g : SpaceTime → ℝ} {u₀ : C(Torus3, ℝ)}
    {u v : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u)
    (hv : IsClassicalSolution c' g u₀ v) (η : NegExponent) {t : ℝ} (ht : 0 < t) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ t ∧ holderBesovENorm η (u s' - v s') ≤ ENNReal.ofReal ε := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_small_dist_sol hu (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_small_dist_sol hv (half_pos hε)
  set s' := min t (min δ₁ δ₂ / 2) with hs'
  have hs0 : 0 < s' := lt_min ht (half_pos (lt_min hδ₁ hδ₂))
  have hm : min δ₁ δ₂ / 2 < min δ₁ δ₂ := half_lt_self (lt_min hδ₁ hδ₂)
  have hs1 : s' < δ₁ := (min_le_right _ _).trans_lt (hm.trans_le (min_le_left _ _))
  have hs2 : s' < δ₂ := (min_le_right _ _).trans_lt (hm.trans_le (min_le_right _ _))
  refine ⟨s', hs0, min_le_left _ _, ?_⟩
  have hη : (η : ℝ) ≤ 0 := η.2.le
  have e : u s' - v s' = (u s' - u 0) - (v s' - v 0) := by
    rw [hu.initial, hv.initial]; abel
  refine (holderBesovENorm_le hη _).trans ?_
  rw [← ofReal_norm, e]
  refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans ?_)
  linarith [h₁ s' hs0.le hs1, h₂ s' hs0.le hs2]

theorem one_le_stepK (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - η) (N : ℕ) (hN : 3 ≤ N) {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) :
    1 ≤ stepK κ η hη₁ hκη N hN L B := by
  have h1 : 0 ≤ Composition.compK' κ η hη₁ hκη N hN (forcingGc N κ) (stepL N κ L B)
      (stepB B) :=
    (Composition.diffConst_nonneg κ η (forcingGc_nonneg N κ)
      (C₀d := Composition.fpCd κ η hη₁ hκη N hN) (c := Composition.rqC κ N hN)
      (cd := Composition.rqCd κ N hN) (Classical.choose_spec
        (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη hN (kernelPair_ann N))).1
      (by linarith [le_stepL N κ (L := L) hB]) (by linarith [le_stepB B])).trans
      (le_max_left _ _)
  have h2 : 0 ≤ stepDW B * (max 1 (Composition.chainG B) * max B 1 * l8Const N κ) :=
    mul_nonneg (zero_le_one.trans (one_le_stepDW B)) (mul_nonneg (mul_nonneg
      (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_right _ _)))
      (l8Const_nonneg N κ))
  unfold stepK
  nlinarith

/-- **The local Lipschitz step from a family of enlarged models.** -/
theorem phi43LocalLipschitz_of_enlargedFamily {κ : Kappa} {N : ℕ} (hN : 5 ≤ N)
    {η : NegExponent} (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (F : (noise : CanonicalNoise) → (Cg : ℝ) → (q : ℕ) →
      (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q) →
      RenormalisationConstants → ℝ → Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hFC : ∀ noise Cg q hg C s, 0 ≤ s → Restart.EnlargedCompat κ
      ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s))
      (F noise Cg q hg C s))
    (hFR : ∀ noise Cg q hg C s, 0 ≤ s → (F noise Cg q hg C s).IsRealisingP (annKernel0C N)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (phi43PolynomialSectorF κ) phi43IntegrationF
      (blockSpan phi43XiFreeF))
    (hFG : ∀ noise Cg q hg C s, 0 ≤ s → ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q' : ℝ),
      (F noise Cg q hg C s).GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q')
    (hFJ : ∀ noise Cg q hg C s, 0 ≤ s → (F noise Cg q hg C s).IsJointMeasurable) :
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
            ENNReal.ofReal K * (holderBesovENorm η (u s - v s) + Statements.phi43Dist κ η T Z Z' ψ ψ') := by
  have hN3 : 3 ≤ N := by omega
  have hη₁ : -2 / 3 < (η : ℝ) := by linarith [hη.1]
  have hκη' : κ.1 < -1 / 2 - η := by linarith
  intro T L B hT hL hB
  set t₀ := stepTime κ η hη₁ hκη' N hN3 L B with ht₀
  set K := stepK κ η hη₁ hκη' N hN3 L B with hK
  refine ⟨t₀, max 1 K, ?_, le_max_left _ _, ?_⟩
  · exact Composition.restartTime_pos κ η (forcingGc_nonneg N κ)
      (Classical.choose_spec (phi43FixedPointF_window_nearOne κ hη₁ hκη' hN3
        (kernelPair_ann N))).1
      (Classical.choose_spec (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη' hN3
        (kernelPair_ann N))).1
      (by linarith [le_stepL N κ (L := L) (B := B) (by linarith)])
      (by linarith [le_stepB B])
  intro f g C C' Z Z' ψ ψ' u₀ u v hf hg hu hv hsize hsize' s t hs hst hts htT hLt
  obtain ⟨hgf, ⟨noise₁, hnz₁, h₁₁, h₁₂, h₁₃, -⟩, hψ⟩ := hf
  obtain ⟨hgg, ⟨noise₂, hnz₂, h₂₁, h₂₂, h₂₃, -⟩, hψ'⟩ := hg
  have hZ : Statements.IsRenormalisedCanonicalModel N κ noise₁ C Z := ⟨h₁₁, h₁₂, h₁₃⟩
  have hZ' : Statements.IsRenormalisedCanonicalModel N κ noise₂ C' Z' := ⟨h₂₁, h₂₂, h₂₃⟩
  obtain ⟨Cg₁, q₁, hg₁⟩ := noise_growth_family hgf noise₁ hnz₁
  obtain ⟨Cg₂, q₂, hg₂⟩ := noise_growth_family hgg noise₂ hnz₂
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 K) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  -- the case of an infinite distance
  by_cases hdtop : Statements.phi43Dist κ η T Z Z' ψ ψ' = ⊤
  · rw [hdtop, add_top, ENNReal.mul_top (ne_of_gt (lt_of_lt_of_le zero_lt_one hK1))]
    exact le_top
  set δ := (Statements.phi43Dist κ η T Z Z' ψ ψ').toReal with hδ
  have hdist : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ := by
    rw [hδ, ENNReal.ofReal_toReal hdtop]
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hdeq : ENNReal.ofReal δ = Statements.phi43Dist κ η T Z Z' ψ ψ' := by
    rw [hδ, ENNReal.ofReal_toReal hdtop]
  have hKK : ENNReal.ofReal K ≤ ENNReal.ofReal (max 1 K) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hK1r : 1 ≤ K := one_le_stepK κ η hη₁ hκη' N hN3 (by linarith) (by linarith)
  have hK1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK1r
  -- the step from a positive restart time
  have step : ∀ s' : ℝ, 0 < s' → s' ≤ t → t ≤ s' + t₀ →
      holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal K *
        (holderBesovENorm η (u s' - v s') + ENNReal.ofReal δ) := by
    intro s' hs' hs't hts'
    rcases eq_or_lt_of_le hs't with heq | hlt
    · subst heq
      calc holderBesovENorm η (u s' - v s') ≤ 1 * (holderBesovENorm η (u s' - v s') + 0) := by
            simp
        _ ≤ _ := mul_le_mul' hK1' (add_le_add le_rfl (by positivity))
    · have hτ : t - s' ∈ Ioc 0 t₀ := ⟨by linarith, by linarith⟩
      have hL₁ := (hLt s' ⟨hs'.le, hs't⟩).1
      have hL₂ := (hLt s' ⟨hs'.le, hs't⟩).2
      have := lipschitz_step_of_restartModels κ η hη₁ hκη' N hN3 hL hB hs' (hs't.trans htT) hδ0
        (hg₁ := hg₁) (hg₂ := hg₂) hZ hZ' hnz₁ hnz₂ hgf hgg hψ hψ' hsize hsize' hdist
        (F noise₁ Cg₁ q₁ hg₁ C s') (F noise₂ Cg₂ q₂ hg₂ C' s') (hFC _ _ _ _ _ _ hs'.le)
        (hFC _ _ _ _ _ _ hs'.le) (hFR _ _ _ _ _ _ hs'.le) (hFR _ _ _ _ _ _ hs'.le)
        (hFG _ _ _ _ _ _ hs'.le) (hFG _ _ _ _ _ _ hs'.le) (hFJ _ _ _ _ _ _ hs'.le)
        (hFJ _ _ _ _ _ _ hs'.le) hu hv hL₁ hL₂ (t - s') hτ
      rwa [show s' + (t - s') = t by ring] at this
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · -- restart at `s = 0`
    subst hs0
    rcases eq_or_lt_of_le hst with ht0 | htpos
    · subst ht0
      rw [hu.initial, hv.initial, sub_self, holderBesovENorm_zero]
      positivity
    · have hlim : holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal K * ENNReal.ofReal δ := by
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        have hKpos : 0 < K + 1 := by linarith
        obtain ⟨s', hs'0, hs't, hsmall⟩ := exists_pos_sub_le hu hv η htpos
          (ε := (ε : ℝ) / (K + 1)) (div_pos hε hKpos)
        refine (step s' hs'0 hs't (by linarith)).trans ?_
        rw [mul_add, add_comm]
        refine add_le_add le_rfl ?_
        refine (mul_le_mul' le_rfl hsmall).trans ?_
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_coe_nnreal]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc']
        rw [div_le_iff₀ hKpos]
        have hε0 : (0 : ℝ) ≤ ε := hε.le
        nlinarith
      rw [hu.initial, hv.initial, sub_self, holderBesovENorm_zero, zero_add, ← hdeq]
      exact hlim.trans (mul_le_mul' hKK le_rfl)
  · refine (step s hspos hst hts).trans ?_
    rw [← hdeq]
    exact mul_le_mul' hKK le_rfl

end RegularityStructures.Phi43.StoppedContinuity

end

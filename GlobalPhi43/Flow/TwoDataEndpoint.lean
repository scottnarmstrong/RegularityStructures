/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.Flow.TwoDataStep
public import Phi43.LocalLipschitz.OfEnlargedModels
public import Phi43.ClassicalSolution.PathContinuity
public import Phi43.ClassicalSolution
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# Distinct-data restart estimate including clock zero

The positive-clock estimate is `lipschitz_step_of_restartModels_twoData`.
At zero the continuous eta-norm of the difference tends to the eta-norm of
the two independent initial data. No uniform supremum norm of the data is used.
The enlarged-family estimates are also applicable to concrete canonical models.
-/

public section

open Set
open scoped ENNReal

namespace GlobalPhi43.Flow

open RegularityStructures RegularityStructures.Phi43
  RegularityStructures.Phi43.StoppedContinuity

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

/-- Positive clocks approximate the difference of independent initial data in the state norm. -/
theorem exists_pos_sub_le_initial {c c' : ℝ} {f g : SpaceTime → ℝ}
    {u₀ v₀ : C(Torus3, ℝ)} {u v : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution c f u₀ u) (hv : IsClassicalSolution c' g v₀ v)
    (η : NegExponent) {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ t ∧ holderBesovENorm η (u s' - v s') ≤
      holderBesovENorm η (u₀ - v₀) + ENNReal.ofReal ε := by
  have hc := ((classicalSolution_continuousOn η hu).sub
    (classicalSolution_continuousOn η hv)).norm
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.1
    (hc.continuousWithinAt (show (0 : ℝ) ∈ Ici 0 from le_rfl)) ε hε
  let s' := min t (δ / 2)
  have hs : 0 < s' := lt_min ht (half_pos hδ)
  have hsδ : s' < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hn := hd (show s' ∈ Ici 0 from hs.le) (by
    simpa [Real.dist_eq, abs_of_nonneg hs.le] using hsδ)
  have heq (r : ℝ) : holderBesovENorm η (u r - v r) =
      ENNReal.ofReal ‖toHolderBesov η (u r) - toHolderBesov η (v r)‖ := by
    rw [← toHolderBesov_sub, norm_toHolderBesov,
      ENNReal.ofReal_toReal (holderBesovENorm_lt_top η.2.le _).ne]
  refine ⟨s', hs, min_le_left _ _, ?_⟩
  rw [← hu.initial, ← hv.initial, heq s', heq 0]
  rw [← ENNReal.ofReal_add (norm_nonneg _) hε.le]
  apply ENNReal.ofReal_le_ofReal
  have := (abs_lt.1 (show |‖toHolderBesov η (u s') - toHolderBesov η (v s')‖ -
    ‖toHolderBesov η (u 0) - toHolderBesov η (v 0)‖| < ε from hn)).2
  linarith

/-- **The local Lipschitz step from a family of enlarged models.** -/
theorem twoDataLocalLipschitz_of_enlargedFamily {κ : Kappa} {N : ℕ} (hN : 5 ≤ N)
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
  intro f g C C' Z Z' ψ ψ' u₀ v₀ u v hf hg hu hv hsize hsize' s t hs hst hts htT hLt
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
      have := lipschitz_step_of_restartModels_twoData κ η hη₁ hκη' N hN3 hL hB hs' (hs't.trans htT) hδ0
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
      calc
        holderBesovENorm η (u 0 - v 0) ≤
            1 * (holderBesovENorm η (u 0 - v 0) +
              Statements.phi43Dist κ η T Z Z' ψ ψ') := by simp
        _ ≤ _ := mul_le_mul' hK1 le_rfl
    · have hlim : holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal K *
          (holderBesovENorm η (u₀ - v₀) + ENNReal.ofReal δ) := by
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        have hKpos : 0 < K + 1 := by linarith
        obtain ⟨s', hs'0, hs't, hsmall⟩ := exists_pos_sub_le_initial hu hv η htpos
          (ε := (ε : ℝ) / (K + 1)) (div_pos hε hKpos)
        calc
          holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal K *
              ((holderBesovENorm η (u₀ - v₀) + ENNReal.ofReal ((ε : ℝ) / (K + 1))) +
                ENNReal.ofReal δ) :=
            (step s' hs'0 hs't (by linarith)).trans
              (mul_le_mul' le_rfl (add_le_add hsmall le_rfl))
          _ = ENNReal.ofReal K * (holderBesovENorm η (u₀ - v₀) + ENNReal.ofReal δ) +
              ENNReal.ofReal K * ENNReal.ofReal ((ε : ℝ) / (K + 1)) := by
            simp only [mul_add]; ac_rfl
          _ ≤ _ := by
            refine add_le_add le_rfl ?_
            rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_coe_nnreal]
            apply ENNReal.ofReal_le_ofReal
            rw [mul_div_assoc', div_le_iff₀ hKpos]
            have hε0 : (0 : ℝ) ≤ ε := hε.le
            nlinarith
      rw [hu.initial, hv.initial, ← hdeq]
      exact hlim.trans (mul_le_mul' hKK le_rfl)
  · refine (step s hspos hst hts).trans ?_
    rw [← hdeq]
    exact mul_le_mul' hKK le_rfl

end GlobalPhi43.Flow

end

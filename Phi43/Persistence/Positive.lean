/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43.ClassicalSolution
public import Phi43.Composition.Exists
public import Phi43.Persistence.Slice
public import Phi43.Persistence.NearHyp
public import Phi43.Potential.NoiseBounds

/-!
# Persistence for positive start times

`persist_positive`: the persistence clause (i) of `Statements.phi43ClassicalSolution_stoppedContinuity`
for start times `s ∈ (0, T]`.  Proof: at the restart `s` the datum `w_s = u(s) - (K ∗ ζ)(s)` has
`‖w_s‖_η ≤ L + C₈(B)` (`persist_conv_bound`), the forcing `ζ_s` satisfies the derivative hypothesis
(`persist_derivHyp`), so the fixed point `U = -𝒦 (U⋆³) + v` of the enlarged restarted model exists
on `(0, t₀]` (`Composition.restart_fixedPoint_exists`); its reconstruction is the classical solution
(`phi43_reconstruction_eq_classical`) and `persist_slice_bound` bounds `‖u(s + t)‖_η`.  The time
`t₀` and the radius `R` depend only on `(L, B)` (and on `κ, N, η`).
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Persistence

open RegularityStructures.Inhomogeneity

theorem persist_positive (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - (η : ℝ)) (N : ℕ) (hN : 3 ≤ N) :
    ∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ)) (u : ℝ → C(Torus3, ℝ)) (T : ℝ),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Set.Ioc (0 : ℝ) T, holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Set.Icc s (s + t₀), holderBesovENorm η (u t) ≤ ENNReal.ofReal R := by
  obtain ⟨t₀f, R₀f, Kf, hpos, hfp⟩ := Composition.restart_fixedPoint_exists κ η hη₁ hκη N hN
    (persistGc N κ) (persistGc_nonneg N κ)
  obtain ⟨c, hc0, hc⟩ := nearHyp_of_restart (κ := κ) N hN
  intro L B hL hB
  have hB0 : 0 ≤ B := by linarith
  set C8 := persistC8 N κ B with hC8def
  have hC8 : 0 ≤ C8 := persistC8_nonneg N κ hB0
  set L' := L + C8 with hL'def
  set B'' := max B (persistBg B) with hB''def
  have hL' : 1 ≤ L' := by linarith
  have hB'' : 1 ≤ B'' := le_max_of_le_left hB
  have hB''0 : 0 ≤ B'' := by linarith
  obtain ⟨hT0, hT1, -, hK0⟩ := hpos L' B'' hL' hB''
  have hM0 : 0 ≤ persistGc N κ 0 * persistBg B :=
    mul_nonneg (persistGc_nonneg N κ 0) (persistBg_nonneg hB0)
  refine ⟨t₀f L' B'', L + 2 * C8 + persistGc N κ 0 * persistBg B + Kf L' B'', hT0, hT1, ?_⟩
  intro f C Z ψ u₀ u T hlift hsol hT hsize s hs hsL t ht
  have hR : L ≤ L + 2 * C8 + persistGc N κ 0 * persistBg B + Kf L' B'' := by linarith
  rcases ht.1.eq_or_lt with h | h
  · subst h
    exact hsL.trans (ENNReal.ofReal_le_ofReal hR)
  obtain ⟨hgrowth, ⟨noise, hnz, hZV2⟩, hψ⟩ := hlift
  have hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z := ⟨hZV2.1, hZV2.2.1, hZV2.2.2.1⟩
  have hg' := hgrowth
  obtain ⟨Cg, q, hgq⟩ := hg'
  have hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    have hz : noise.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hnz
    rw [hz]
    exact hgq
  have hf : IsSmoothOnSpaceTime f := Potential.isSmoothOnSpaceTime_of_noise hnz
  have hs0 : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hsize'' : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B'' :=
    hsize.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the enlarged restarted model
  have hC := enlargedRestartModel_compat N κ noise Cg q hg C s
  have hreal := enlargedRestartModel_isRealisingP N κ noise Cg q hg C hN s
  have hgr' := enlargedRestartModel_growth_kappa N κ noise Cg q hg C s
  have hJ := enlargedRestartModel_isJointMeasurable N κ noise Cg q hg C s
  -- the datum
  have hpsi := perSmooth_phi43PsiAt N κ noise C
  have hVb : ∀ s' : ℝ, s ≤ s' → s' ≤ s + 1 → s' ≤ T + 1 →
      holderBesovENorm η (forcePath hpsi s') ≤ ENNReal.ofReal C8 := fun s' h0 h1 h2 =>
    persist_conv_bound Cg q hg hZ hnz hgrowth hψ hB0 hs0 hsize η.2.le h0 h1 h2 _ (fun xt => by
      rw [forcePath_apply, phi43PsiAt_eq])
  have hV0 := hVb s le_rfl (by linarith) (by linarith [hs.2])
  set ws : C(Torus3, ℝ) := u s - forcePath hpsi s with hws
  have hwsb : holderBesovENorm η ws ≤ ENNReal.ofReal L' := by
    have e : ws = u s + -forcePath hpsi s := by rw [hws]; abel
    rw [e]
    refine (holderBesovENorm_add_le _ _ _).trans ?_
    rw [holderBesovENorm_neg, hL'def, ENNReal.ofReal_add (by linarith) hC8]
    exact add_le_add hsL hV0
  have hws' : ∀ x : Fin 3 → ℝ, ws (torusProj x) = u s (torusProj x) - phi43PsiAt N κ noise C (s, x) :=
    fun x => by
      rw [hws, ContinuousMap.sub_apply, forcePath_apply]
  -- the forcing
  have hgs := Potential.perSmooth_zeta_restart noise N s
  have hBg0 := persistBg_nonneg hB0
  have hBgB : persistBg B ≤ B'' := le_max_right _ _
  have hG := fun L => persist_derivHyp Cg q hg hZ (Potential.polyBounded_zeta hnz hgrowth) hB0
    hs0 hsize L
  -- the fixed point
  obtain ⟨𝒦, U, h𝒦, -, hfix, hKb⟩ := hfp L' B'' hL' hB'' hZ hs0 hsize'' _ hC hreal hgr' hJ ws hwsb
    hgs hBg0 hBgB hG
  have hyp := hc hB''0 hZ hs0 hsize'' hT0 hT1 _ hC ⟨hreal, hgr'⟩ hJ
  let S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s :=
    { ws := ws
      B := persistBg B
      hB := hBg0
      Gc := persistGc N κ
      hGc := persistGc_nonneg N κ
      hGζ := hG
      U := U
      𝒦 := 𝒦
      h𝒦 := h𝒦
      hfix := hfix hT1 }
  have hws'' : ∀ x : Fin 3 → ℝ,
      S.ws (torusProj x) = u s (torusProj x) - phi43PsiAt N κ noise C (s, x) := hws'
  have ident := phi43_reconstruction_eq_classical hyp hN hη₁ hκη noise Cg q hg C hs.1 hC hf hnz
    hsol S hws''
  have hslice := persist_slice_bound hyp noise C S ident (L' := L') (C8 := C8) (K := Kf L' B'')
    (by linarith) hC8 hK0 hwsb
    (fun t' ht' => hVb (t' + s) (by linarith [ht'.1]) (by linarith [ht'.2])
      (by linarith [ht'.2, hs.2])) (fun x hx => hKb x hx)
  have hτ : t - s ∈ Ioc 0 (t₀f L' B'') := ⟨by linarith, by linarith [ht.2]⟩
  have h1 := hslice (t - s) hτ
  rw [add_sub_cancel] at h1
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have hτ1 : t - s ≤ 1 := hτ.2.trans hT1
  have : (persistGc N κ 0 * persistBg B) * (t - s) ≤ persistGc N κ 0 * persistBg B :=
    mul_le_of_le_one_right hM0 hτ1
  show L + C8 + C8 + (persistGc N κ 0 * persistBg B) * (t - s) + Kf L' B'' ≤ _
  linarith

end RegularityStructures.Phi43.Persistence

end

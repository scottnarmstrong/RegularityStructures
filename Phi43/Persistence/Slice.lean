/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Identification
public import Phi43.Reconstruction.InhomUnit
public import Phi43.TimeSlice.HolderBesovBound
public import Phi43.Persistence.Forcing
public import RegularityStructures.Abstract.Datum.HeatExtCont

/-!
# The `𝒞^η` bound of a restarted solution from the fixed point

`persist_slice_bound`: let `S` be a solution of the fixed point at a restart `s` (`Phi43RestartSolution`)
whose reconstruction is the classical solution, `S.U(t, x)_1 + (K ∗ ζ)((t, x) + (s, 0)) = u(s + t)(x)`.
Then, in `C(T³)`,

  `u(s + t) = P_t w_s + (K ∗ ζ)(s + t) + θ_s(t) - ⟨1, 𝒦 (U⋆³)⟩(t)`,

(the unit coordinate of the fixed point equation `U = -𝒦 (U⋆³) + v`, with `v_1 = P_t w_s + θ_s`),
so `‖u(s + t)‖_η ≤ ‖w_s‖_η + ‖(K ∗ ζ)(s + t)‖_η + t sup |ζ_s| + sup |⟨1, 𝒦 (U⋆³)⟩|`, using the
contraction of `P_t` on `𝒞^η` and `‖·‖_η ≤ ‖·‖_∞`.
-/

public section

open Set RegularityStructures.PDE

namespace RegularityStructures.Phi43.Persistence

open Inhomogeneity

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

/-- The Duhamel integral of the restarted forcing is bounded in `𝒞^η` by its sup bound times
the time. -/
theorem holderBesovENorm_duhamel_zeta_le {g : ParabolicSpace → ℝ} (hg : PerSmooth g) {M₀ : ℝ}
    (hM₀ : 0 ≤ M₀) (hbd : ∀ r ∈ Icc (0 : ℝ) 1, ∀ y : Fin 3 → ℝ, |g (r, y)| ≤ M₀) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    holderBesovENorm η (duhamel (forcePath hg) t) ≤ ENNReal.ofReal (M₀ * t) := by
  have hn : ‖duhamel (forcePath hg) t‖ ≤ M₀ * t := by
    refine norm_duhamel_le_mul (continuous_forcePath hg) ht0 fun r hr => ?_
    refine (ContinuousMap.norm_le _ hM₀).2 fun y => ?_
    obtain ⟨z, rfl⟩ := torusProj_surjective y
    rw [forcePath_apply, Real.norm_eq_abs]
    exact hbd r ⟨hr.1, hr.2.trans ht1⟩ z
  refine (holderBesovENorm_le η.2.le _).trans ?_
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

/-- **The `𝒞^η` bound of the restarted solution** from the fixed point. -/
theorem persist_slice_bound (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T)
    (noise : CanonicalNoise) (C : RenormalisationConstants) {s : ℝ}
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s) {u : ℝ → C(Torus3, ℝ)}
    (hid : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, S.U.val (t, x) (.old .one) +
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) = u (s + t) (torusProj x))
    {L' C8 K : ℝ} (hL' : 0 ≤ L') (hC8 : 0 ≤ C8) (hK0 : 0 ≤ K)
    (hws : holderBesovENorm η S.ws ≤ ENNReal.ofReal L')
    (hΨ : ∀ t ∈ Ioc 0 T, holderBesovENorm η
      (forcePath (perSmooth_phi43PsiAt N κ noise C) (t + s)) ≤ ENNReal.ofReal C8)
    (hK : ∀ x ∈ timeSlab T, |(S.𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) S.U)).val x (.old .one)| ≤ K) :
    ∀ t ∈ Ioc 0 T, holderBesovENorm η (u (s + t)) ≤
      ENNReal.ofReal (L' + C8 + (S.Gc 0 * S.B) * t + K) := by
  intro t ht
  have hM₀ : 0 ≤ S.Gc 0 * S.B := mul_nonneg (S.hGc 0) S.hB
  set Pw : C(Torus3, ℝ) := heatOp t S.ws with hPw
  set Ps : C(Torus3, ℝ) := forcePath (perSmooth_phi43PsiAt N κ noise C) (t + s) with hPs
  set Th : C(Torus3, ℝ) := duhamel (forcePath (Potential.perSmooth_zeta_restart noise N s)) t
    with hTh
  set k : C(Torus3, ℝ) := Pw + Ps + Th - u (s + t) with hk
  have hkx : ∀ x : Fin 3 → ℝ, k (torusProj x) = (S.𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) S.U)).val (t, x) (.old .one) := by
    intro x
    have hx : ((t, x) : ParabolicSpace) ∈ timeSlab T := ⟨ht.1, ht.2⟩
    have h1 := congrArg (fun W => W.val (t, x) (.old .one)) S.hfix
    simp only [Model.SlabSpace.val_add, Model.SlabSpace.val_neg, Pi.add_apply, Pi.neg_apply] at h1
    rw [phi43InhomTheta_unit κ η M hyp.real.poly hyp.hT1 _ _ S.hB S.hGc S.hGζ hx,
      datumField_toHolderBesov_apply η S.ws ht.1 x,
      duhamelField_of_pos _ (show 0 < ((t, x) : ParabolicSpace).1 from ht.1)] at h1
    have h2 := hid t ht x
    rw [restartPoint_add] at h2
    have e1 : Ps (torusProj x) = phi43PsiAt N κ noise C (t + s, x) := forcePath_apply _ _ _
    have e2 : Th (torusProj x) = duhamel (forcePath (Potential.perSmooth_zeta_restart noise N s)) t
        (torusProj x) := rfl
    simp only [hk, ContinuousMap.sub_apply, ContinuousMap.add_apply, e1, ← h2]
    simp only [hPw, hTh] at h1 ⊢
    linarith
  have hkb : ∀ y : Torus3, |k y| ≤ K := by
    intro y
    obtain ⟨x, rfl⟩ := torusProj_surjective y
    rw [hkx x]
    exact hK _ ⟨ht.1, ht.2⟩
  have hu : u (s + t) = (Pw + Ps + Th) + (-k) := by
    simp only [hk]
    abel
  have hPwb : holderBesovENorm η Pw ≤ ENNReal.ofReal L' :=
    (Datum.holderBesovENorm_heatOp_le η ht.1 S.ws).trans hws
  have hThb : holderBesovENorm η Th ≤ ENNReal.ofReal ((S.Gc 0 * S.B) * t) := by
    refine holderBesovENorm_duhamel_zeta_le (Potential.perSmooth_zeta_restart noise N s) hM₀
      (fun r hr y => ?_) ht.1.le (ht.2.trans hyp.hT1)
    exact S.hGζ 0 [] (by simp) r ⟨hr.1, hr.2⟩ y
  have hkb' : holderBesovENorm η k ≤ ENNReal.ofReal K :=
    TimeSlice.holderBesovENorm_le_ofReal_of_abs_le η.2.le k hK0 hkb
  have hMt : 0 ≤ (S.Gc 0 * S.B) * t := mul_nonneg hM₀ ht.1.le
  rw [hu]
  calc holderBesovENorm η ((Pw + Ps + Th) + -k)
      ≤ holderBesovENorm η (Pw + Ps + Th) + holderBesovENorm η (-k) :=
        holderBesovENorm_add_le _ _ _
    _ ≤ (holderBesovENorm η (Pw + Ps) + holderBesovENorm η Th) + holderBesovENorm η k := by
        rw [holderBesovENorm_neg]
        gcongr
        exact holderBesovENorm_add_le _ _ _
    _ ≤ ((holderBesovENorm η Pw + holderBesovENorm η Ps) + holderBesovENorm η Th) +
          holderBesovENorm η k := by
        gcongr
        exact holderBesovENorm_add_le _ _ _
    _ ≤ ((ENNReal.ofReal L' + ENNReal.ofReal C8) + ENNReal.ofReal ((S.Gc 0 * S.B) * t)) +
          ENNReal.ofReal K := by
        gcongr
        exact hΨ t ht
    _ = ENNReal.ofReal (L' + C8 + (S.Gc 0 * S.B) * t + K) := by
        rw [← ENNReal.ofReal_add hL' hC8, ← ENNReal.ofReal_add (add_nonneg hL' hC8) hMt,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg hL' hC8) hMt) hK0]

end RegularityStructures.Phi43.Persistence

end

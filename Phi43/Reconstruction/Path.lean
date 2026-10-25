/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.UnitContinuity

/-!
# The reconstruction as a continuous path in `C(T³)`

Part of the derivation of the mild equation (continuity of `w` on `[0, T] × T³`, `w(0) = u(s)`). If
the unit coordinate of `U` is spatially periodic, `w = ⟨1, U⟩ + K ∗ ζ(· + (s, 0))` is a continuous
periodic function on `(0, T] × ℝ³` (`phi43_unit_continuousWithinAt`), tends to `u(s)` uniformly as
`t → 0` (`phi43_small_time`), and therefore extends to a continuous path `W : ℝ → C(T³)`
(`exists_phi43_path`).
-/

public section

open Set Filter Topology RegularityStructures.PDE

namespace RegularityStructures.Phi43

/-- A continuous function on `ℝ × ℝ³` that is constant on the fibres of `torusProj` in the second
variable, as a continuous function on `ℝ × T³`. -/
@[expose] noncomputable def descend2 (h : ℝ × (Fin 3 → ℝ) → ℝ) (hc : Continuous h)
    (hp : ∀ s a b, torusProj a = torusProj b → h (s, a) = h (s, b)) : C(ℝ × Torus3, ℝ) where
  toFun p := h (p.1, torusRep p.2)
  continuous_toFun := by
    have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) torusProj) :=
      IsOpenQuotientMap.id.prodMap (IsOpenQuotientMap.piMap fun _ =>
        QuotientAddGroup.isOpenQuotientMap_mk)
    rw [hq.isQuotientMap.continuous_iff]
    refine hc.congr fun p => ?_
    refine (hp _ _ _ ?_).symm
    funext i
    simp [torusProj, torusRep]

theorem descend2_apply (h : ℝ × (Fin 3 → ℝ) → ℝ) (hc : Continuous h)
    (hp : ∀ s a b, torusProj a = torusProj b → h (s, a) = h (s, b)) (t : ℝ) (y : Fin 3 → ℝ) :
    descend2 h hc hp (t, torusProj y) = h (t, y) :=
  hp _ _ _ (torusProj_torusRep _)

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

/-- **The reconstruction is a continuous path in `C(T³)`**, started at `u(s)`. -/
theorem exists_phi43_path (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - (η : ℝ))
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ}
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s) (us : C(Torus3, ℝ))
    (hws : ∀ x : Fin 3 → ℝ, S.ws (torusProj x) = us (torusProj x) - phi43PsiAt N κ noise C (s, x))
    (hper : ∀ t ∈ Ioc 0 T, ∀ (x c : Fin 3 → ℝ), torusProj c = 0 →
      S.U.val (t, x + c) (.old .one) = S.U.val (t, x) (.old .one)) :
    ∃ W : ℝ → C(Torus3, ℝ), Continuous W ∧ W 0 = us ∧ ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      W t (torusProj x) = S.U.val (t, x) (.old .one) +
        phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) := by
  obtain ⟨E, hE, hEb⟩ := phi43_small_time hyp hN hη₁ hκη noise Cg q hg C hC S us hws
  have hψ := perSmooth_phi43PsiAt N κ noise C
  have hψc : Continuous (phi43PsiAt N κ noise C) := hψ.smooth.continuous
  have hT0 := hyp.hT0
  set Wt : ℝ × (Fin 3 → ℝ) → ℝ := fun p => S.U.val (min p.1 T, p.2) (.old .one) +
    phi43PsiAt N κ noise C (min p.1 T + s, p.2) with hWt
  set Wf : ℝ × (Fin 3 → ℝ) → ℝ := fun p => if 0 < p.1 then Wt p else us (torusProj p.2) with hWf
  have hus : Continuous fun p : ℝ × (Fin 3 → ℝ) => us (torusProj p.2) :=
    us.continuous.comp (continuous_torusProj.comp continuous_snd)
  have hgmap : Continuous fun p : ℝ × (Fin 3 → ℝ) => ((min p.1 T, p.2) : ParabolicSpace) :=
    (continuous_fst.min continuous_const).prodMk continuous_snd
  -- continuity of `Wt` where `p.1 > 0`
  have hWtc : ∀ p₀ : ℝ × (Fin 3 → ℝ), 0 < p₀.1 → ContinuousAt Wt p₀ := by
    intro p₀ hp₀
    have hz : ((min p₀.1 T, p₀.2) : ParabolicSpace) ∈ timeSlab T :=
      ⟨lt_min hp₀ hT0, min_le_right _ _⟩
    have hU := phi43_unit_continuousWithinAt hyp S hz
    have hev : ∀ᶠ p in 𝓝 p₀, ((min p.1 T, p.2) : ParabolicSpace) ∈ timeSlab T := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp₀] with p hp
      exact ⟨lt_min hp hT0, min_le_right _ _⟩
    have h1 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => S.U.val ((min p.1 T, p.2) : ParabolicSpace)
        (.old .one)) p₀ := by
      have := hU.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hgmap.continuousAt.tendsto, hev⟩)
      exact this
    have h2 : Continuous fun p : ℝ × (Fin 3 → ℝ) =>
        phi43PsiAt N κ noise C (min p.1 T + s, p.2) :=
      hψc.comp (((continuous_fst.min continuous_const).add continuous_const).prodMk continuous_snd)
    exact h1.add h2.continuousAt
  have hWfc : Continuous Wf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    rcases lt_trichotomy p₀.1 0 with hneg | hzero | hpos
    · have : Wf =ᶠ[𝓝 p₀] fun p : ℝ × (Fin 3 → ℝ) => us (torusProj p.2) := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hneg] with p hp
        simp [hWf, not_lt.2 hp.le]
      exact (hus.continuousAt).congr this.symm
    · -- the point `t = 0`
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hE'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hE (ε / 2) (by linarith)
      obtain ⟨δ₂, hδ₂, hus'⟩ := Metric.continuous_iff.1
        (us.continuous.comp continuous_torusProj) p₀.2 (ε / 2) (by linarith)
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp => ?_⟩
      have hp1 : |p.1| < min δ₁ δ₂ := by
        have := (Prod.dist_eq (x := p) (y := p₀)).symm ▸ hp
        have h := lt_of_le_of_lt (le_max_left _ _) this
        rwa [Real.dist_eq, hzero, sub_zero] at h
      have hp2 : dist p.2 p₀.2 < min δ₁ δ₂ := by
        have := (Prod.dist_eq (x := p) (y := p₀)).symm ▸ hp
        exact lt_of_le_of_lt (le_max_right _ _) this
      have hW0 : Wf p₀ = us (torusProj p₀.2) := by simp [hWf, hzero]
      rw [hW0, Real.dist_eq]
      have h2 : |us (torusProj p.2) - us (torusProj p₀.2)| < ε / 2 := by
        have := hus' p.2 (hp2.trans_le (min_le_right _ _))
        rwa [Real.dist_eq] at this
      by_cases hp0 : 0 < p.1
      · have hmem : min p.1 T ∈ Ioc (0 : ℝ) T := ⟨lt_min hp0 hT0, min_le_right _ _⟩
        have hb := hEb _ hmem p.2
        have hEs : dist (E (min p.1 T)) 0 < ε / 2 := by
          refine hE' (show min p.1 T ∈ Ioi 0 from hmem.1) ?_
          rw [Real.dist_eq, sub_zero, abs_of_pos hmem.1]
          exact (min_le_left _ _).trans_lt ((le_abs_self _).trans_lt (hp1.trans_le (min_le_left _ _)))
        rw [Real.dist_eq, sub_zero] at hEs
        have e1 : Wf p = Wt p := by simp [hWf, hp0]
        calc |Wf p - us (torusProj p₀.2)| = |(Wt p - us (torusProj p.2)) +
              (us (torusProj p.2) - us (torusProj p₀.2))| := by rw [e1]; ring_nf
          _ ≤ |Wt p - us (torusProj p.2)| + |us (torusProj p.2) - us (torusProj p₀.2)| :=
              abs_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (lt_of_le_of_lt hb ((le_abs_self _).trans_lt hEs)) h2
          _ = ε := by ring
      · have e1 : Wf p = us (torusProj p.2) := by simp [hWf, hp0]
        rw [e1]
        linarith
    · have : Wf =ᶠ[𝓝 p₀] Wt := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hpos] with p hp
        simp [hWf, hp]
      exact (hWtc p₀ hpos).congr this.symm
  have hWfp : ∀ (t : ℝ) (a b : Fin 3 → ℝ), torusProj a = torusProj b → Wf (t, a) = Wf (t, b) := by
    intro t a b hab
    have hc : torusProj (b - a) = 0 := (torusProj_eq_iff_sub b a).1 hab.symm
    by_cases ht : 0 < t
    · have hb : b = a + (b - a) := by abel
      have hmem : min t T ∈ Ioc (0 : ℝ) T := ⟨lt_min ht hT0, min_le_right _ _⟩
      simp only [hWf, ht, ↓reduceIte, hWt]
      rw [hb, hper _ hmem a (b - a) hc]
      have := hψ.periodic (min t T + s, a) (b - a) hc
      simp only at this
      rw [this]
    · simp [hWf, ht, hab]
  refine ⟨(descend2 Wf hWfc hWfp).curry, ContinuousMap.continuous _, ?_, ?_⟩
  · ext xb
    obtain ⟨x, rfl⟩ := torusProj_surjective xb
    change descend2 Wf hWfc hWfp (0, torusProj x) = us (torusProj x)
    rw [descend2_apply]
    simp [hWf]
  · intro t ht x
    have hmin : min t T = t := min_eq_left ht.2
    change descend2 Wf hWfc hWfp (t, torusProj x) = _
    rw [descend2_apply]
    simp only [hWf, ht.1, ↓reduceIte, hWt, hmin]
    rw [restartPoint_add]

end RegularityStructures.Phi43

end

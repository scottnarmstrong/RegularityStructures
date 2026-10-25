/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Jet
public import RegularityStructures.PDE.DuhamelTime

/-!
# Mild solutions with smooth data solve the equation pointwise

Let `G` be a smooth nonlinearity, `u₀` a smooth function on `T³` and `u` a continuous mild solution
of `∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]`. Then `u(t)` has continuous first and
second partial derivatives `w(t)`, `w2(t)`, and for `t ∈ (0, T)`
`∂_t u(t, x) = Δu(t, x) + G(t, x, u(t, x))` with `Δu = Σᵢ w2ᵢᵢ` (`hasDerivAt_of_isMildSolution`).

The second derivatives come from the jet of the jet system (`exists_jet_of_isMildSolution` applied
twice). The time derivative combines `∂_t P_t u₀ = P_t Δu₀` with the time derivative of the
Duhamel integral, which needs the Laplacian of `x ↦ G(s, x, u(s, x))`; this is computed with the
chain rule from the jets.
-/

open scoped ContDiff

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_prodMk_path {F : Type*} [NormedAddCommGroup F]
    {a : ℝ → C(Torus3, E)} {b : ℝ → C(Torus3, F)} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun t => (a t).prodMk (b t) := by
  have h1 : Continuous fun q : ℝ × Torus3 => a q.1 q.2 :=
    continuous_eval.comp ((ha.comp continuous_fst).prodMk continuous_snd)
  have h2 : Continuous fun q : ℝ × Torus3 => b q.1 q.2 :=
    continuous_eval.comp ((hb.comp continuous_fst).prodMk continuous_snd)
  exact (ContinuousMap.curry ⟨fun q : ℝ × Torus3 => (a q.1 q.2, b q.1 q.2),
    h1.prodMk h2⟩).continuous

omit [FiniteDimensional ℝ E] in
/-- The second component of a function with values in `E × (Fin 3 → E)`. -/
theorem snd_compLeft_prodMk (a : C(Torus3, E)) (b : C(Torus3, Fin 3 → E)) :
    (ContinuousLinearMap.snd ℝ E (Fin 3 → E)).compLeftContinuous ℝ Torus3 (a.prodMk b) = b := by
  ext x
  rfl

/-- **Mild solutions with smooth data are classical.** -/
theorem hasDerivAt_of_isMildSolution {G : C(ℝ × Torus3 × E, E)}
    (hG : ContDiff ℝ ∞ (nonlinLift G)) {u₀ : C(Torus3, E)}
    (hu₀ : ContDiff ℝ ∞ fun y => u₀ (torusProj y)) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → C(Torus3, E)} (hu : Continuous u) (hmild : IsMildSolution G u₀ T u) :
    ∃ (w : ℝ → C(Torus3, Fin 3 → E)) (w2 : ℝ → C(Torus3, Fin 3 → Fin 3 → E)),
      Continuous w ∧ Continuous w2 ∧ (∀ t ∈ Icc 0 T, HasTorusDeriv (u t) (w t)) ∧
      (∀ t ∈ Icc 0 T, HasTorusDeriv (E := Fin 3 → E) (w t) (w2 t)) ∧
      ∀ t ∈ Ioo 0 T, ∀ x,
        HasDerivAt (fun s => u s x) (torusLap (w2 t) x + G (t, x, u t x)) t := by
  have hG1 : ContDiff ℝ 1 (nonlinLift G) := hG.of_le (by exact_mod_cast le_top)
  have hu₀1 : ContDiff ℝ 1 fun y => u₀ (torusProj y) := hu₀.of_le (by exact_mod_cast le_top)
  set Du₀ := torusDerivOf u₀ hu₀1 with hDu₀def
  have hDu₀ : HasTorusDeriv u₀ Du₀ := hasTorusDeriv_torusDerivOf u₀ hu₀1
  have hDu₀s : ContDiff ℝ ∞ fun y => Du₀ (torusProj y) := contDiff_torusDerivOf_lift hu₀
  have hDu₀1 : ContDiff ℝ 1 fun y => Du₀ (torusProj y) := hDu₀s.of_le (by exact_mod_cast le_top)
  set D2u₀ := torusDerivOf (F := Fin 3 → E) Du₀ hDu₀1 with hD2u₀def
  have hD2u₀ : HasTorusDeriv (E := Fin 3 → E) Du₀ D2u₀ :=
    hasTorusDeriv_torusDerivOf (F := Fin 3 → E) Du₀ hDu₀1
  -- the first jet
  obtain ⟨w, hw, hdw, hmw, hmJ⟩ := exists_jet_of_isMildSolution hG1 hDu₀ hT hu hmild
  -- the second jet
  have hGJ : ContDiff ℝ ∞ (nonlinLift (F := E × (Fin 3 → E)) (jetNonlin G hG1)) :=
    contDiff_nonlinLift_jetNonlin hG
  have hGJ1 : ContDiff ℝ 1 (nonlinLift (F := E × (Fin 3 → E)) (jetNonlin G hG1)) :=
    hGJ.of_le (by exact_mod_cast le_top)
  have hJ₀s : ContDiff ℝ ∞ fun y => (u₀.prodMk Du₀) (torusProj y) := hu₀.prodMk hDu₀s
  have hJ₀1 : ContDiff ℝ 1 fun y => (u₀.prodMk Du₀) (torusProj y) :=
    hJ₀s.of_le (by exact_mod_cast le_top)
  have hDJ₀ := hasTorusDeriv_torusDerivOf (F := E × (Fin 3 → E)) (u₀.prodMk Du₀) hJ₀1
  have hJc : Continuous fun t => (u t).prodMk (w t) := continuous_prodMk_path hu hw
  obtain ⟨W, hW, hdW, -, -⟩ := exists_jet_of_isMildSolution (E := E × (Fin 3 → E)) hGJ1 hDJ₀ hT
    hJc hmJ
  -- second derivatives of `u`
  set S : (Fin 3 → E × (Fin 3 → E)) →L[ℝ] (Fin 3 → Fin 3 → E) :=
    ContinuousLinearMap.pi fun i => (ContinuousLinearMap.snd ℝ E (Fin 3 → E)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => E × (Fin 3 → E)) i) with hSdef
  set w2 : ℝ → C(Torus3, Fin 3 → Fin 3 → E) := fun t => S.compLeftContinuous ℝ Torus3 (W t)
    with hw2def
  have hw2c : Continuous w2 := (S.compLeftContinuous ℝ Torus3).continuous.comp hW
  have hdw2 : ∀ t ∈ Icc 0 T, HasTorusDeriv (E := Fin 3 → E) (w t) (w2 t) := by
    intro t ht
    have h := (hdW t ht).compLeft (ContinuousLinearMap.snd ℝ E (Fin 3 → E))
    rwa [snd_compLeft_prodMk] at h
  refine ⟨w, w2, hw, hw2c, hdw, hdw2, fun t ht x => ?_⟩
  -- the nonlinear term and its derivatives
  set H : ℝ → C(Torus3, E) := fun s => nemytskii G s (u s) with hHdef
  set DH : ℝ → C(Torus3, Fin 3 → E) := fun s => nemytskiiDeriv G hG1 s (u s) (w s) with hDHdef
  set D2H : ℝ → C(Torus3, Fin 3 → Fin 3 → E) := fun s => S.compLeftContinuous ℝ Torus3
    (nemytskiiDeriv (F := E × (Fin 3 → E)) (jetNonlin G hG1) hGJ1 s ((u s).prodMk (w s)) (W s))
    with hD2Hdef
  have hHc : Continuous H := continuous_nemytskii_comp G hu
  have hDHc : Continuous DH := continuous_nemytskiiDeriv_comp hG1 hu hw
  have hD2Hc : Continuous D2H := (S.compLeftContinuous ℝ Torus3).continuous.comp
    (continuous_nemytskiiDeriv_comp (F := E × (Fin 3 → E)) hGJ1 hJc hW)
  have hdH : ∀ s ∈ Icc 0 T, HasTorusDeriv (H s) (DH s) := fun s hs =>
    hasTorusDeriv_nemytskii hG1 s (hdw s hs)
  have hdDH : ∀ s ∈ Icc 0 T, HasTorusDeriv (E := Fin 3 → E) (DH s) (D2H s) := by
    intro s hs
    have h := (hasTorusDeriv_nemytskii (F := E × (Fin 3 → E)) hGJ1 s (hdW s hs)).compLeft
      (ContinuousLinearMap.snd ℝ E (Fin 3 → E))
    have heq : (ContinuousLinearMap.snd ℝ E (Fin 3 → E)).compLeftContinuous ℝ Torus3
        (nemytskii (E := E × (Fin 3 → E)) (jetNonlin G hG1) s ((u s).prodMk (w s))) = DH s := by
      ext x
      rfl
    rwa [heq] at h
  -- `Δu(t) = P_t Δu₀ + ∫₀ᵗ P_{t-s} ΔH(s) ds`
  have hTt : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hw2eq : w2 t = heatOp t D2u₀ + duhamel D2H t := by
    have h1 := (hasTorusDeriv_heatOp hD2u₀ t).add (hasTorusDeriv_duhamel hDHc hD2Hc ht.1.le
      fun s hs => hdDH s ⟨hs.1, hs.2.trans ht.2.le⟩)
    rw [← hmw t hTt] at h1
    exact (hdw2 t hTt).unique h1
  have hlap : torusLap (w2 t) = heatOp t (torusLap D2u₀) +
      duhamel (fun s => torusLap (D2H s)) t := by
    simp_rw [torusLap_eq_compLeft]
    rw [hw2eq, map_add, heatOp_compLeftContinuous, duhamel_compLeftContinuous hD2Hc]
  -- the time derivative
  have hA := hasDerivAt_heatOp_apply hDu₀ hD2u₀ ht.1 x
  have hB := hasDerivAt_duhamel_apply hHc hD2Hc hdH hdDH ht x
  have hsum := hA.add hB
  have hval : heatOp t (torusLap D2u₀) x + (H t x + duhamel (fun s => torusLap (D2H s)) t x) =
      torusLap (w2 t) x + G (t, x, u t x) := by
    rw [hlap]
    simp only [ContinuousMap.add_apply, hHdef, nemytskii_apply]
    abel
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  rw [hmild s hs]
  rfl

end RegularityStructures.PDE

end

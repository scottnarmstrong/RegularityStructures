/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.MildTime
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Mild solutions with smooth data are smooth

Let `G` be a smooth nonlinearity, `u₀` a smooth function on `T³` and `u` a continuous mild solution
of `∂_t u = Δu + G(t, x, u)` on `[0, T]`. Then the lift `(t, y) ↦ u(t, torusProj y)` is smooth on
`(0, T) × ℝ³` (`contDiffOn_of_isMildSolution`).

The proof is an induction on the order `n`, simultaneously for all smooth systems. A `C¹` function
on an open set is `C^{n+1}` when its derivative is `C^n`. The derivative of the lift is assembled
from the time derivative `Δu + G(t, x, u)` and the spatial partial derivatives
(`hasStrictFDerivAt_uncurry_coprod`); the spatial partial derivatives and the Laplacian are
components of mild solutions of the jet system and of the jet of the jet system, which are again
smooth systems, so the induction hypothesis applies to them.
-/

open scoped ContDiff

public section

open Set Filter Topology

namespace RegularityStructures.PDE

universe u

/-- The lift `(t, y) ↦ u(t, torusProj y)` of a path in `C(T³, E)`. -/
theorem continuous_pathLift {E : Type*} [TopologicalSpace E] {u : ℝ → C(Torus3, E)}
    (hu : Continuous u) : Continuous fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2) :=
  continuous_eval.comp ((hu.comp continuous_fst).prodMk (continuous_torusProj.comp continuous_snd))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the lift of a path that is differentiable in time and in space, with
continuous partial derivatives. -/
theorem hasFDerivAt_pathLift {u : ℝ → C(Torus3, E)} {w : ℝ → C(Torus3, Fin 3 → E)}
    {q : ℝ × (Fin 3 → ℝ) → E} (hw : Continuous w) (hq : Continuous q) {T : ℝ}
    (hdt : ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun s => u s (torusProj y)) (q (t, y)) t)
    (hdx : ∀ t ∈ Ioo 0 T, HasTorusDeriv (u t) (w t)) {p : ℝ × (Fin 3 → ℝ)}
    (hp : p ∈ Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ))) :
    HasFDerivAt (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (q p)).coprod (ofPartials (w p.1 (torusProj p.2)))) p := by
  have hΩ : Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ)) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := fun t y => u t (torusProj y))
    (f₁ := fun t y => (1 : ℝ →L[ℝ] ℝ).smulRight (q (t, y)))
    (f₂ := fun t y => ofPartials (w t (torusProj y)))
    (Filter.mem_of_superset hΩ fun v hv => (hdt v.1 hv.1 v.2).hasFDerivAt)
    (Filter.mem_of_superset hΩ fun v hv => hdx v.1 hv.1 v.2)
    ((ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous.comp hq).continuousAt
    ((ofPartials.continuous.comp (continuous_pathLift hw)).continuousAt)
  exact h.hasFDerivAt

/-- The derivative assembled from `C^n` time and space derivatives is `C^n`. -/
theorem contDiffOn_coprod_smulRight {n : ℕ} {s : Set (ℝ × (Fin 3 → ℝ))}
    {q : ℝ × (Fin 3 → ℝ) → E} {w : ℝ × (Fin 3 → ℝ) → Fin 3 → E} (hq : ContDiffOn ℝ n q s)
    (hw : ContDiffOn ℝ n w s) :
    ContDiffOn ℝ n (fun p => ((1 : ℝ →L[ℝ] ℝ).smulRight (q p)).coprod (ofPartials (w p))) s := by
  rw [contDiffOn_clm_apply]
  intro v
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self]
  exact (contDiffOn_const.smul hq).add
    ((ofPartials.contDiff.comp_contDiffOn hw).clm_apply contDiffOn_const)

/-- The trace map `(aᵢⱼ) ↦ Σᵢ aᵢᵢ`. -/
theorem torusLap_apply_eq_trace (D2g : C(Torus3, Fin 3 → Fin 3 → E)) (x : Torus3) :
    torusLap D2g x = (∑ i : Fin 3, (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => E) i).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 3 => Fin 3 → E) i)) (D2g x) := by
  simp [torusLap_apply]

/-- **Mild solutions with smooth data are smooth.** If `G` is a smooth nonlinearity, `u₀` is
smooth and `u` is a continuous mild solution on `[0, T]`, then the lift of `u` is `C^n` on
`(0, T) × ℝ³` for every `n`. -/
theorem contDiffOn_of_isMildSolution_nat (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {G : C(ℝ × Torus3 × E, E)} (_ : ContDiff ℝ ∞ (nonlinLift G)) {u₀ : C(Torus3, E)}
      (_ : ContDiff ℝ ∞ fun y => u₀ (torusProj y)) {T : ℝ} (_ : 0 ≤ T)
      {u : ℝ → C(Torus3, E)} (_ : Continuous u) (_ : IsMildSolution G u₀ T u),
      ContDiffOn ℝ n (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
        (Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ))) := by
  induction n with
  | zero =>
    intro E _ _ _ G _ u₀ _ T _ u hu _
    exact contDiffOn_zero.2 (continuous_pathLift hu).continuousOn
  | succ n ih =>
    intro E _ _ _ G hG u₀ hu₀ T hT u hu hmild
    set Ω : Set (ℝ × (Fin 3 → ℝ)) := Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ)) with hΩdef
    have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
    have hΩI : ∀ p ∈ Ω, p.1 ∈ Icc 0 T := fun p hp => Ioo_subset_Icc_self hp.1
    have hG1 : ContDiff ℝ 1 (nonlinLift G) := hG.of_le (by exact_mod_cast le_top)
    have hu₀1 : ContDiff ℝ 1 fun y => u₀ (torusProj y) := hu₀.of_le (by exact_mod_cast le_top)
    have hDu₀ := hasTorusDeriv_torusDerivOf u₀ hu₀1
    -- first and second derivatives, and the time derivative
    obtain ⟨w, w2, hw, hw2, hdw, hdw2, hdt⟩ := hasDerivAt_of_isMildSolution hG hu₀ hT hu hmild
    -- the jet system
    obtain ⟨w', hw', hdw', -, hmJ⟩ := exists_jet_of_isMildSolution hG1 hDu₀ hT hu hmild
    have hww' : ∀ t ∈ Icc 0 T, w t = w' t := fun t ht => (hdw t ht).unique (hdw' t ht)
    have hGJ : ContDiff ℝ ∞ (nonlinLift (F := E × (Fin 3 → E)) (jetNonlin G hG1)) :=
      contDiff_nonlinLift_jetNonlin hG
    have hGJ1 : ContDiff ℝ 1 (nonlinLift (F := E × (Fin 3 → E)) (jetNonlin G hG1)) :=
      hGJ.of_le (by exact_mod_cast le_top)
    have hJ₀s : ContDiff ℝ ∞ fun y => (u₀.prodMk (torusDerivOf u₀ hu₀1)) (torusProj y) :=
      hu₀.prodMk (contDiff_torusDerivOf_lift hu₀)
    have hJ₀1 : ContDiff ℝ 1 fun y => (u₀.prodMk (torusDerivOf u₀ hu₀1)) (torusProj y) :=
      hJ₀s.of_le (by exact_mod_cast le_top)
    have hDJ₀ := hasTorusDeriv_torusDerivOf (F := E × (Fin 3 → E))
      (u₀.prodMk (torusDerivOf u₀ hu₀1)) hJ₀1
    have hJc : Continuous fun t => (u t).prodMk (w' t) := continuous_prodMk_path hu hw'
    -- the jet of the jet system
    obtain ⟨W, hW, hdW, -, hmJJ⟩ := exists_jet_of_isMildSolution (E := E × (Fin 3 → E)) hGJ1
      hDJ₀ hT hJc hmJ
    have hGJJ := contDiff_nonlinLift_jetNonlin (F := E × (Fin 3 → E)) hGJ
    have hJJ₀s := hJ₀s.prodMk (contDiff_torusDerivOf_lift (F := E × (Fin 3 → E)) hJ₀s)
    have hJJc : Continuous fun t => ((u t).prodMk (w' t)).prodMk (W t) :=
      continuous_prodMk_path hJc hW
    -- second derivatives are components of the jet of the jet
    set S : (Fin 3 → E × (Fin 3 → E)) →L[ℝ] (Fin 3 → Fin 3 → E) :=
      ContinuousLinearMap.pi fun i => (ContinuousLinearMap.snd ℝ E (Fin 3 → E)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => E × (Fin 3 → E)) i) with hSdef
    have hw2W : ∀ t ∈ Icc 0 T, w2 t = S.compLeftContinuous ℝ Torus3 (W t) := by
      intro t ht
      have h := (hdW t ht).compLeft (ContinuousLinearMap.snd ℝ E (Fin 3 → E))
      rw [snd_compLeft_prodMk, ← hww' t ht] at h
      exact (hdw2 t ht).unique h
    -- induction hypotheses
    have ihU := ih hG hu₀ hT hu hmild
    have ihJ := ih (E := E × (Fin 3 → E)) hGJ hJ₀s hT hJc hmJ
    have ihJJ := ih (E := (E × (Fin 3 → E)) × (Fin 3 → E × (Fin 3 → E))) hGJJ hJJ₀s hT hJJc
      hmJJ
    -- the spatial derivative is `C^n`
    have hwn : ContDiffOn ℝ n (fun p : ℝ × (Fin 3 → ℝ) => w p.1 (torusProj p.2)) Ω := by
      refine (contDiff_snd.comp_contDiffOn ihJ).congr fun p hp => ?_
      simp only [Function.comp_apply, hww' p.1 (hΩI p hp)]
      rfl
    -- the time derivative is `C^n`
    set Tr : (Fin 3 → Fin 3 → E) →L[ℝ] E := ∑ i : Fin 3, (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => E) i).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 3 => Fin 3 → E) i) with hTrdef
    set q : ℝ × (Fin 3 → ℝ) → E := fun p =>
      torusLap (w2 p.1) (torusProj p.2) + G (p.1, torusProj p.2, u p.1 (torusProj p.2)) with hqdef
    have hqc : Continuous q :=
      (continuous_pathLift (continuous_torusLap_comp hw2)).add (G.continuous.comp
        (continuous_fst.prodMk ((continuous_torusProj.comp continuous_snd).prodMk
          (continuous_pathLift hu))))
    have hqn : ContDiffOn ℝ n q Ω := by
      have h1 : ContDiffOn ℝ n (fun p : ℝ × (Fin 3 → ℝ) =>
          Tr (S (((u p.1).prodMk (w' p.1)).prodMk (W p.1) (torusProj p.2)).2)) Ω :=
        (Tr.contDiff.comp (S.contDiff.comp contDiff_snd)).comp_contDiffOn ihJJ
      have h2 : ContDiffOn ℝ n (fun p : ℝ × (Fin 3 → ℝ) =>
          nonlinLift G (p.1, p.2, u p.1 (torusProj p.2))) Ω :=
        hG.of_le (by exact_mod_cast le_top) |>.comp_contDiffOn
          (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk ihU))
      refine (h1.add h2).congr fun p hp => ?_
      simp only [hqdef, torusLap_apply_eq_trace, hw2W p.1 (hΩI p hp), nonlinLift]
      rfl
    have hdt' : ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun s => u s (torusProj y)) (q (t, y)) t :=
      fun t ht y => hdt t ht (torusProj y)
    have hdx' : ∀ t ∈ Ioo 0 T, HasTorusDeriv (u t) (w t) := fun t ht =>
      hdw t (Ioo_subset_Icc_self ht)
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun p hp => (hasFDerivAt_pathLift hw hqc hdt' hdx' hp).differentiableAt
      |>.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    exact (contDiffOn_coprod_smulRight hqn hwn).congr fun p hp =>
      (hasFDerivAt_pathLift hw hqc hdt' hdx' hp).fderiv

/-- **Mild solutions with smooth data are smooth** on `(0, T) × ℝ³`. -/
theorem contDiffOn_of_isMildSolution {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : C(ℝ × Torus3 × E, E)} (hG : ContDiff ℝ ∞ (nonlinLift G))
    {u₀ : C(Torus3, E)} (hu₀ : ContDiff ℝ ∞ fun y => u₀ (torusProj y)) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → C(Torus3, E)} (hu : Continuous u) (hmild : IsMildSolution G u₀ T u) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (Ioo 0 T ×ˢ (univ : Set (Fin 3 → ℝ))) :=
  contDiffOn_infty.2 fun n => contDiffOn_of_isMildSolution_nat n hG hu₀ hT hu hmild

end RegularityStructures.PDE

end

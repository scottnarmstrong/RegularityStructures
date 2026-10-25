/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelSpatial
public import RegularityStructures.PDE.MildTime
public import RegularityStructures.PDE.Semigroup
public import RegularityStructures.PDE.SpatialDeriv
public import RegularityStructures.PDE.Jet

/-!
# The Duhamel principle for smooth spatially periodic functions

`duhamel_principle`: if `a` is smooth and spatially periodic and `g = ∂_t a - Δ a` (smooth), then
`a(t, ·) = P_t a(0, ·) + ∫₀ᵗ P_{t-r} g(r, ·) dr` as functions on the torus.  Proof: the right-hand
side is a mild solution of the linear heat equation with forcing `g` (hence classical, by
`hasDerivAt_of_isMildSolution`); the difference with `a` solves the homogeneous heat equation with
zero datum, hence vanishes (`eq_zero_of_heat_equation`).
-/

public section

open Set Filter Topology RegularityStructures.PDE RegularityStructures.Inhomogeneity
open scoped ContDiff

namespace RegularityStructures.Phi43

variable {a : ParabolicSpace → ℝ}

/-- Second partial derivative data of the slices of a smooth periodic function. -/
theorem exists_hasTorusDeriv₂_forcePath (ha : PerSmooth a) (r : ℝ) :
    ∃ D2 : C(Torus3, Fin 3 → Fin 3 → ℝ),
      HasTorusDeriv (E := Fin 3 → ℝ) (forceVec ha r) D2 ∧
      ∀ y : Fin 3 → ℝ, torusLap D2 (torusProj y) =
        ∑ i : Fin 3, ddv i.succ (ddv i.succ a) (r, y) := by
  have hsm : ContDiff ℝ 1 fun y => forceVec ha r (torusProj y) := by
    have : (fun y => forceVec ha r (torusProj y)) = fun y => fun j : Fin 3 => ddv j.succ a (r, y) := by
      funext y j
      exact forceVec_apply ha r y j
    rw [this]
    refine contDiff_pi.2 fun j => ?_
    exact ((ha.ddv j.succ).smooth.of_le (by exact_mod_cast le_top)).comp
      (contDiff_const.prodMk contDiff_id)
  refine ⟨torusDerivOf (F := Fin 3 → ℝ) (forceVec ha r) hsm,
    hasTorusDeriv_torusDerivOf (F := Fin 3 → ℝ) (forceVec ha r) hsm, fun y => ?_⟩
  set D2 := torusDerivOf (F := Fin 3 → ℝ) (forceVec ha r) hsm with hD2
  have hD : HasTorusDeriv (E := Fin 3 → ℝ) (forceVec ha r) D2 :=
    hasTorusDeriv_torusDerivOf (F := Fin 3 → ℝ) (forceVec ha r) hsm
  rw [torusLap_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hD.compLeft (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
  rw [comp_forceVec] at h1
  have h2 := hasTorusDeriv_forcePath (ha.ddv i.succ) r
  have h3 := h1.unique h2
  have h4 := congrArg (fun F : C(Torus3, Fin 3 → ℝ) => F (torusProj y) i) h3
  simp only [compLeftContinuous_apply_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, forceVec_apply] at h4
  exact h4

theorem hasDerivAt_forcePath_apply (ha : PerSmooth a) (t : ℝ) (y : Fin 3 → ℝ) :
    HasDerivAt (fun s => forcePath ha s (torusProj y)) (ddv 0 a (t, y)) t := by
  have h : (fun s => forcePath ha s (torusProj y)) = fun s => a (s, y) :=
    funext fun s => forcePath_apply ha s y
  rw [h]
  have hd : DifferentiableAt ℝ a (t, y) := (ha.smooth.differentiable (by simp)) (t, y)
  have hι : HasDerivAt (fun s : ℝ => ((s, y) : ParabolicSpace)) ((1 : ℝ), (0 : Fin 3 → ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have := hd.hasFDerivAt.comp_hasDerivAt t hι
  have e : ddv 0 a (t, y) = fderiv ℝ a (t, y) ((1 : ℝ), (0 : Fin 3 → ℝ)) := by
    rw [ddv, Datum.stBasis_zero]
  rw [e]
  exact this

/-- **The Duhamel principle for smooth periodic functions.** -/
theorem duhamel_principle (ha : PerSmooth a) {g : ParabolicSpace → ℝ} (hg : PerSmooth g)
    (hag : ∀ z, ddv 0 a z - ∑ j : Fin 3, ddv j.succ (ddv j.succ a) z = g z) {t : ℝ} (ht : 0 ≤ t) :
    forcePath ha t = heatOp t (forcePath ha 0) + duhamel (forcePath hg) t := by
  set a0 := forcePath ha 0 with ha0
  set Wm : ℝ → C(Torus3, ℝ) := fun r => heatOp r a0 + duhamel (forcePath hg) r with hWm
  have hWmc : Continuous Wm :=
    (continuous_heatOp_left a0).add (continuous_duhamel (continuous_forcePath hg))
  set T' := t + 1 with hT'
  set T'' := T' + 1 with hT''
  have hT''0 : 0 ≤ T'' := by linarith
  have hmild : IsMildSolution (forcing hg) a0 T'' Wm := by
    intro r _
    have h : (fun s => nemytskii (forcing hg) s (Wm s)) = forcePath hg := by
      funext s; ext x; rfl
    rw [h]
  have ha0s : ContDiff ℝ ∞ fun y => a0 (torusProj y) := by
    have : (fun y => a0 (torusProj y)) = fun y => a (0, y) :=
      funext fun y => forcePath_apply ha 0 y
    rw [this]
    exact ha.smooth.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨w, w2, hwc, hw2c, hdw, hdw2, hdt⟩ := hasDerivAt_of_isMildSolution
    (contDiff_nonlinLift_forcing hg) ha0s hT''0 hWmc hmild
  choose D2 hD2 hD2lap using fun r => exists_hasTorusDeriv₂_forcePath ha r
  have hD0 : (forcePath ha 0 - Wm 0) = 0 := by
    have : Wm 0 = a0 := by simp [hWm, heatOp_zero_left, duhamel_zero]
    rw [this]
    exact sub_self _
  have key := eq_zero_of_heat_equation (w := fun r => forcePath ha r - Wm r)
    (Dw := fun r => forceVec ha r - w r) (D2w := fun r => D2 r - w2 r) (T := T')
    ((continuous_forcePath ha).sub hWmc) hD0
    (fun r hr => (hasTorusDeriv_forcePath ha r).sub (hdw r ⟨hr.1.le, hr.2.trans (by linarith)⟩))
    (fun r hr => (hD2 r).sub (hdw2 r ⟨hr.1.le, hr.2.trans (by linarith)⟩))
    (fun r hr x => by
      obtain ⟨y, rfl⟩ := torusProj_surjective x
      have hrI : r ∈ Ioo 0 T'' := ⟨hr.1, by linarith [hr.2]⟩
      have hA := hasDerivAt_forcePath_apply ha r y
      have hW := hdt r hrI (torusProj y)
      have hsub := hA.sub hW
      have hF : (forcing hg) (r, torusProj y, Wm r (torusProj y)) = g (r, y) := by
        rw [forcing_apply]
        exact hg.eq_of_torusProj_eq r (torusProj_torusRep _)
      rw [hF] at hsub
      convert hsub using 1
      rw [torusLap_sub]
      simp only [ContinuousMap.sub_apply, hD2lap, ← hag (r, y)]
      ring)
  have := key t ⟨ht, by linarith⟩
  exact sub_eq_zero.1 this

end RegularityStructures.Phi43

end

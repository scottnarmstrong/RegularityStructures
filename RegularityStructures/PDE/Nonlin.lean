/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Mild
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Smooth nonlinearities and their jets

A nonlinearity `G : ℝ × T³ × F → F` is smooth when its lift
`nonlinLift G (s, y, v) = G(s, torusProj y, v)` is smooth on `ℝ × ℝ³ × F`. Its derivative in
`(x, u)` descends to a continuous map `nonlinDeriv G` on `ℝ × T³ × F`.

* `hasTorusDeriv_nemytskii`: the chain rule for `x ↦ G(s, x, v(x))`;
* `jetNonlin G`: the nonlinearity `(s, x, v, ω) ↦ (G(s, x, v), (D G(s, x, v)(eᵢ, ωᵢ))ᵢ)` of the
  system satisfied by a solution together with its first partial derivatives;
* `contDiff_nonlinLift_jetNonlin`: the jet nonlinearity of a smooth nonlinearity is smooth.
-/

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

/-- The lift `(s, y, v) ↦ G(s, torusProj y, v)` of a nonlinearity on `ℝ × T³ × F`. -/
def nonlinLift (G : C(ℝ × Torus3 × F, F)) (p : ℝ × (Fin 3 → ℝ) × F) : F :=
  G (p.1, torusProj p.2.1, p.2.2)

/-- A continuous function on `ℝ × ℝ³ × F` that is constant on the fibres of `torusProj` in the
middle variable, as a continuous function on `ℝ × T³ × F`. -/
def descend3 (h : ℝ × (Fin 3 → ℝ) × F → X) (hc : Continuous h)
    (hp : ∀ s a b v, torusProj a = torusProj b → h (s, a, v) = h (s, b, v)) :
    C(ℝ × Torus3 × F, X) where
  toFun p := h (p.1, torusRep p.2.1, p.2.2)
  continuous_toFun := by
    have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) (Prod.map torusProj (id : F → F))) :=
      IsOpenQuotientMap.id.prodMap ((IsOpenQuotientMap.piMap fun _ =>
        QuotientAddGroup.isOpenQuotientMap_mk).prodMap IsOpenQuotientMap.id)
    rw [hq.isQuotientMap.continuous_iff]
    refine hc.congr fun p => ?_
    refine (hp _ _ _ _ ?_).symm
    funext i
    simp [torusProj, torusRep]

/-- The derivative of the lift of `G` in the `(y, v)` directions. -/
def liftDeriv (G : C(ℝ × Torus3 × F, F)) (p : ℝ × (Fin 3 → ℝ) × F) :
    ((Fin 3 → ℝ) × F) →L[ℝ] F :=
  (fderiv ℝ (nonlinLift G) p).comp (ContinuousLinearMap.inr ℝ ℝ ((Fin 3 → ℝ) × F))

end RegularityStructures.PDE

end

public section

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem nonlinLift_add_of_torusProj_eq_zero (G : C(ℝ × Torus3 × F, F)) {c : Fin 3 → ℝ}
    (hc : torusProj c = 0) :
    (fun p : ℝ × (Fin 3 → ℝ) × F => nonlinLift G (p + (0, c, 0))) = nonlinLift G := by
  funext p
  simp [nonlinLift, torusProj_add, hc]

theorem liftDeriv_eq_of_torusProj_eq (G : C(ℝ × Torus3 × F, F)) {s : ℝ} {a b : Fin 3 → ℝ}
    {v : F} (hab : torusProj a = torusProj b) : liftDeriv G (s, a, v) = liftDeriv G (s, b, v) := by
  have hc : torusProj (a - b) = 0 := (torusProj_eq_iff_sub a b).1 hab
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := nonlinLift G) (x := (s, b, v))
    ((0, a - b, 0) : ℝ × (Fin 3 → ℝ) × F)
  rw [nonlinLift_add_of_torusProj_eq_zero G hc] at h
  have hp : ((s, b, v) : ℝ × (Fin 3 → ℝ) × F) + (0, a - b, 0) = (s, a, v) := by
    simp
  rw [hp] at h
  simp only [liftDeriv, h]

theorem continuous_liftDeriv {G : C(ℝ × Torus3 × F, F)} (hG : ContDiff ℝ 1 (nonlinLift G)) :
    Continuous (liftDeriv G) :=
  (hG.continuous_fderiv one_ne_zero).clm_comp continuous_const

end RegularityStructures.PDE

end

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative in `(x, u)` of a `C¹` nonlinearity, as a continuous map on `ℝ × T³ × F`. -/
def nonlinDeriv (G : C(ℝ × Torus3 × F, F)) (hG : ContDiff ℝ 1 (nonlinLift G)) :
    C(ℝ × Torus3 × F, ((Fin 3 → ℝ) × F) →L[ℝ] F) :=
  descend3 (liftDeriv G) (continuous_liftDeriv hG)
    fun _ _ _ _ hab => liftDeriv_eq_of_torusProj_eq G hab

/-- The jet nonlinearity `(s, x, v, ω) ↦ (G(s, x, v), (D G(s, x, v)(eᵢ, ωᵢ))ᵢ)`: if `u` solves
`∂_t u = Δu + G(t, x, u)`, then `(u, ∂u)` solves `∂_t J = ΔJ + jetNonlin G (t, x, J)`. -/
def jetNonlin (G : C(ℝ × Torus3 × F, F)) (hG : ContDiff ℝ 1 (nonlinLift G)) :
    C(ℝ × Torus3 × (F × (Fin 3 → F)), F × (Fin 3 → F)) where
  toFun p := (G (p.1, p.2.1, p.2.2.1),
    fun i => nonlinDeriv G hG (p.1, p.2.1, p.2.2.1) (Pi.single i 1, p.2.2.2 i))
  continuous_toFun := by
    have h1 : Continuous fun p : ℝ × Torus3 × (F × (Fin 3 → F)) => (p.1, p.2.1, p.2.2.1) := by
      fun_prop
    refine (G.continuous.comp h1).prodMk (continuous_pi fun i => ?_)
    exact ((nonlinDeriv G hG).continuous.comp h1).clm_apply (continuous_const.prodMk (by fun_prop))

/-- The partial derivatives `x ↦ (D G(s, x, v(x))(eᵢ, Dv(x)ᵢ))ᵢ` of `x ↦ G(s, x, v(x))`. -/
def nemytskiiDeriv (G : C(ℝ × Torus3 × F, F)) (hG : ContDiff ℝ 1 (nonlinLift G)) (s : ℝ)
    (v : C(Torus3, F)) (Dv : C(Torus3, Fin 3 → F)) : C(Torus3, Fin 3 → F) :=
  ⟨fun x i => nonlinDeriv G hG (s, x, v x) (Pi.single i 1, Dv x i), by
    refine continuous_pi fun i => ?_
    exact ((nonlinDeriv G hG).continuous.comp (by fun_prop)).clm_apply
      (continuous_const.prodMk (by fun_prop))⟩

end RegularityStructures.PDE

end

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The partial derivatives of a `C¹` function on `T³`, descended from its periodic lift. -/
def torusDerivOf (g : C(Torus3, F)) (hg : ContDiff ℝ 1 fun y => g (torusProj y)) :
    C(Torus3, Fin 3 → F) :=
  torusDescend (fun y i => fderiv ℝ (fun y => g (torusProj y)) y (Pi.single i 1))
    (continuous_pi fun _ => (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    fun _ _ hab => funext fun _ => by rw [fderiv_lift_eq_of_torusProj_eq hab]

end RegularityStructures.PDE

end

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem nonlinDeriv_torusProj {G : C(ℝ × Torus3 × F, F)} (hG : ContDiff ℝ 1 (nonlinLift G))
    (s : ℝ) (y : Fin 3 → ℝ) (v : F) :
    nonlinDeriv G hG (s, torusProj y, v) = liftDeriv G (s, y, v) :=
  liftDeriv_eq_of_torusProj_eq G (torusProj_torusRep _)

/-- `nonlinDeriv G` is the derivative of the lift of `G` in `(y, v)`. -/
theorem hasFDerivAt_nonlinLift {G : C(ℝ × Torus3 × F, F)} (hG : ContDiff ℝ 1 (nonlinLift G))
    (s : ℝ) (y : Fin 3 → ℝ) (v : F) :
    HasFDerivAt (fun q : (Fin 3 → ℝ) × F => G (s, torusProj q.1, q.2))
      (nonlinDeriv G hG (s, torusProj y, v)) (y, v) := by
  rw [nonlinDeriv_torusProj]
  have hd : HasFDerivAt (nonlinLift G) (fderiv ℝ (nonlinLift G) (s, y, v)) (s, y, v) :=
    (hG.differentiable one_ne_zero _).hasFDerivAt
  have hi : HasFDerivAt (fun q : (Fin 3 → ℝ) × F => ((s, q) : ℝ × (Fin 3 → ℝ) × F))
      (ContinuousLinearMap.inr ℝ ℝ ((Fin 3 → ℝ) × F)) (y, v) :=
    (hasFDerivAt_const s (y, v)).prodMk (hasFDerivAt_id (y, v))
  exact hd.comp (y, v) hi

/-- The derivative of `(y, v) ↦ G(s, y, v)` applied along `(k, ofPartials ω k)` is the
combination of its values on coordinate directions. -/
theorem ofPartials_clm_single (L : ((Fin 3 → ℝ) × F) →L[ℝ] F) (ω : Fin 3 → F)
    (k : Fin 3 → ℝ) :
    ofPartials (fun i => L (Pi.single i 1, ω i)) k = L (k, ofPartials ω k) := by
  rw [ofPartials_apply, ofPartials_apply]
  simp only [← map_smul, ← map_sum]
  congr 1
  ext j
  · rw [Prod.fst_sum, Finset.sum_apply]
    simp [Pi.single_apply]
  · rw [Prod.snd_sum]
    simp

/-- **Chain rule for Nemytskii operators.** If `v` has partial derivatives `Dv`, then
`x ↦ G(s, x, v(x))` has partial derivatives `nemytskiiDeriv G hG s v Dv`. -/
theorem hasTorusDeriv_nemytskii {G : C(ℝ × Torus3 × F, F)} (hG : ContDiff ℝ 1 (nonlinLift G))
    (s : ℝ) {v : C(Torus3, F)} {Dv : C(Torus3, Fin 3 → F)} (hv : HasTorusDeriv v Dv) :
    HasTorusDeriv (nemytskii G s v) (nemytskiiDeriv G hG s v Dv) := by
  intro y
  have h1 : HasFDerivAt (fun y : Fin 3 → ℝ => (y, v (torusProj y)))
      ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod (ofPartials (Dv (torusProj y)))) y :=
    (hasFDerivAt_id y).prodMk (hv y)
  have h2 := (hasFDerivAt_nonlinLift hG s y (v (torusProj y))).comp y h1
  have heq : ofPartials (nemytskiiDeriv G hG s v Dv (torusProj y)) =
      (nonlinDeriv G hG (s, torusProj y, v (torusProj y))).comp
        ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod (ofPartials (Dv (torusProj y)))) := by
    refine ContinuousLinearMap.ext fun k => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
    exact ofPartials_clm_single _ _ k
  rw [heq]
  exact h2

theorem torusDerivOf_torusProj (g : C(Torus3, F)) (hg : ContDiff ℝ 1 fun y => g (torusProj y))
    (y : Fin 3 → ℝ) (i : Fin 3) :
    torusDerivOf g hg (torusProj y) i = fderiv ℝ (fun y => g (torusProj y)) y (Pi.single i 1) := by
  simp [torusDerivOf]

theorem hasTorusDeriv_torusDerivOf (g : C(Torus3, F))
    (hg : ContDiff ℝ 1 fun y => g (torusProj y)) : HasTorusDeriv g (torusDerivOf g hg) := by
  intro y
  have : ofPartials (torusDerivOf g hg (torusProj y)) = fderiv ℝ (fun y => g (torusProj y)) y := by
    rw [← ofPartials_apply_single (fderiv ℝ (fun y => g (torusProj y)) y)]
    congr 1
    funext i
    exact torusDerivOf_torusProj g hg y i
  rw [this]
  exact (hg.differentiable one_ne_zero y).hasFDerivAt

open scoped ContDiff in
theorem contDiff_torusDerivOf_lift {g : C(Torus3, F)}
    (hg : ContDiff ℝ ∞ fun y => g (torusProj y)) :
    ContDiff ℝ ∞ fun y => torusDerivOf g (hg.of_le (by exact_mod_cast le_top)) (torusProj y) := by
  have h : (fun y => torusDerivOf g (hg.of_le (by exact_mod_cast le_top)) (torusProj y)) =
      fun y i => fderiv ℝ (fun y => g (torusProj y)) y (Pi.single i 1) := by
    funext y i
    exact torusDerivOf_torusProj _ _ y i
  rw [h]
  exact contDiff_pi.2 fun i =>
    (hg.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const

theorem nonlinLift_jetNonlin {G : C(ℝ × Torus3 × F, F)} (hG : ContDiff ℝ 1 (nonlinLift G)) :
    nonlinLift (F := F × (Fin 3 → F)) (jetNonlin G hG) =
      fun p : ℝ × (Fin 3 → ℝ) × (F × (Fin 3 → F)) => ((nonlinLift G (p.1, p.2.1, p.2.2.1),
        fun i => liftDeriv G (p.1, p.2.1, p.2.2.1) (Pi.single i 1, p.2.2.2 i)) :
          F × (Fin 3 → F)) := by
  funext p
  simp only [nonlinLift, jetNonlin, ContinuousMap.coe_mk, nonlinDeriv_torusProj]

open scoped ContDiff in
/-- The jet nonlinearity of a smooth nonlinearity is smooth. -/
theorem contDiff_nonlinLift_jetNonlin {G : C(ℝ × Torus3 × F, F)}
    (hG : ContDiff ℝ ∞ (nonlinLift G)) :
    ContDiff ℝ ∞ (nonlinLift (F := F × (Fin 3 → F))
      (jetNonlin G (hG.of_le (by exact_mod_cast le_top)))) := by
  rw [nonlinLift_jetNonlin]
  have hp : ContDiff ℝ ∞ fun p : ℝ × (Fin 3 → ℝ) × (F × (Fin 3 → F)) => (p.1, p.2.1, p.2.2.1) :=
    contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
      (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))
  refine (hG.comp hp).prodMk (contDiff_pi.2 fun i => ?_)
  have hD : ContDiff ℝ ∞ (liftDeriv G) :=
    (hG.fderiv_right (by exact_mod_cast le_top)).clm_comp contDiff_const
  exact (hD.comp hp).clm_apply (contDiff_const.prodMk
    ((contDiff_apply ℝ F i).comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))))

theorem continuous_nemytskiiDeriv_comp {G : C(ℝ × Torus3 × F, F)}
    (hG : ContDiff ℝ 1 (nonlinLift G)) {v : ℝ → C(Torus3, F)} {Dv : ℝ → C(Torus3, Fin 3 → F)}
    (hv : Continuous v) (hDv : Continuous Dv) :
    Continuous fun s => nemytskiiDeriv G hG s (v s) (Dv s) := by
  have hv' : Continuous fun q : ℝ × Torus3 => v q.1 q.2 :=
    continuous_eval.comp ((hv.comp continuous_fst).prodMk continuous_snd)
  have hDv' : Continuous fun q : ℝ × Torus3 => Dv q.1 q.2 :=
    continuous_eval.comp ((hDv.comp continuous_fst).prodMk continuous_snd)
  let K : C(ℝ × Torus3, Fin 3 → F) :=
    ⟨fun q i => nonlinDeriv G hG (q.1, q.2, v q.1 q.2) (Pi.single i 1, Dv q.1 q.2 i), by
      refine continuous_pi fun i => ?_
      exact ((nonlinDeriv G hG).continuous.comp (continuous_fst.prodMk
        (continuous_snd.prodMk hv'))).clm_apply (continuous_const.prodMk
          ((continuous_apply i).comp hDv'))⟩
  exact K.curry.continuous

end RegularityStructures.PDE

end

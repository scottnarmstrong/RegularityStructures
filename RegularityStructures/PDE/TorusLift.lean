/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Lifting functions between `T³` and `ℝ³`

The projection `torusProj : ℝ³ → T³` is a continuous additive open quotient map that does not
increase distances. A continuous function on `ℝ³` that is constant on the fibres of `torusProj`
descends to a continuous function on `T³` (`torusDescend`). Derivatives of functions on `T³` are
those of their periodic lifts (`HasTorusDeriv`). Finally `torusShift a` is the translation
`g ↦ g(· + a)` on `C(T³, E)`, as a continuous linear map.

These are the bookkeeping tools of the semilinear heat theory in `RegularityStructures/PDE/`.
-/

@[expose] public noncomputable section

open Set

namespace RegularityStructures.PDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous function on `ℝ³` that is constant on the fibres of `torusProj`, as a continuous
function on `T³`. Its value at `x` is the value at the representative `torusRep x`. -/
def torusDescend [TopologicalSpace F] (h : (Fin 3 → ℝ) → F) (hc : Continuous h)
    (hp : ∀ a b, torusProj a = torusProj b → h a = h b) : C(Torus3, F) where
  toFun x := h (torusRep x)
  continuous_toFun := by
    have hq : IsOpenQuotientMap torusProj :=
      IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
    rw [hq.isQuotientMap.continuous_iff]
    refine hc.congr fun y => ?_
    refine (hp _ _ ?_).symm
    funext i
    simp [torusProj, torusRep]

/-- The linear map `ℝ³ → E` with partial derivatives `v`: `k ↦ Σᵢ kᵢ vᵢ`. -/
def ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E :=
  ∑ i : Fin 3, (ContinuousLinearMap.smulRightL ℝ (Fin 3 → ℝ) E
    (ContinuousLinearMap.proj i)).comp (ContinuousLinearMap.proj i)

/-- `g` has partial derivatives `Dg` on the torus: the periodic lift of `g` has Fréchet derivative
`k ↦ Σᵢ kᵢ Dg(y)ᵢ` at every `y ∈ ℝ³`. Derivatives are recorded through their partial derivatives,
so higher derivatives take values in iterated products `Fin 3 → Fin 3 → E`. -/
def HasTorusDeriv (g : C(Torus3, E)) (Dg : C(Torus3, Fin 3 → E)) : Prop :=
  ∀ y : Fin 3 → ℝ, HasFDerivAt (fun y => g (torusProj y)) (ofPartials (Dg (torusProj y))) y

/-- Translation `g ↦ g(· + a)` on `C(T³, E)`. -/
def torusShift (a : Torus3) : C(Torus3, E) →L[ℝ] C(Torus3, E) :=
  ContinuousMap.compCLM (R := ℝ) E (Homeomorph.addRight a : C(Torus3, Torus3))

/-- The directional derivative `x ↦ Σᵢ kᵢ Dg(x)ᵢ` of a function with partial derivatives `Dg`. -/
def evalAt (k : Fin 3 → ℝ) : C(Torus3, Fin 3 → E) →L[ℝ] C(Torus3, E) :=
  ((ContinuousLinearMap.apply ℝ E k).comp ofPartials).compLeftContinuous ℝ Torus3

end RegularityStructures.PDE

end

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The projection `ℝ³ → T³` -/

theorem torusProj_add (a b : Fin 3 → ℝ) : torusProj (a + b) = torusProj a + torusProj b := by
  funext i
  simp [torusProj]

theorem torusProj_neg (a : Fin 3 → ℝ) : torusProj (-a) = -torusProj a := by
  funext i
  simp [torusProj]

theorem torusProj_sub (a b : Fin 3 → ℝ) : torusProj (a - b) = torusProj a - torusProj b := by
  rw [sub_eq_add_neg, torusProj_add, torusProj_neg, ← sub_eq_add_neg]

theorem torusProj_zero : torusProj 0 = 0 := by
  funext i
  simp [torusProj]

@[fun_prop]
theorem continuous_torusProj : Continuous torusProj :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem torusProj_torusRep (x : Torus3) : torusProj (torusRep x) = x := by
  funext i
  simp [torusProj, torusRep]

theorem torusProj_surjective : Function.Surjective torusProj :=
  fun x => ⟨torusRep x, torusProj_torusRep x⟩

theorem dist_torusProj_le (a b : Fin 3 → ℝ) : dist (torusProj a) (torusProj b) ≤ dist a b := by
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖torusProj a i - torusProj b i‖ = ‖((a i - b i : ℝ) : UnitAddCircle)‖ := by
        simp [torusProj]
    _ ≤ ‖a i - b i‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ ‖a - b‖ := norm_le_pi_norm (a - b) i

/-- Translating the lift of a function on `T³` by a vector of `ker torusProj` changes nothing. -/
theorem lift_comp_add_of_torusProj_eq_zero {X : Type*} (g : Torus3 → X) {c : Fin 3 → ℝ}
    (hc : torusProj c = 0) : (fun y => g (torusProj (y + c))) = fun y => g (torusProj y) := by
  funext y
  rw [torusProj_add, hc, add_zero]

theorem torusProj_eq_iff_sub (a b : Fin 3 → ℝ) :
    torusProj a = torusProj b ↔ torusProj (a - b) = 0 := by
  rw [torusProj_sub, sub_eq_zero]

/-- The derivative of the lift of a function on `T³` is constant on the fibres of `torusProj`. -/
theorem fderiv_lift_eq_of_torusProj_eq {g : Torus3 → F} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : Fin 3 → ℝ} (hab : torusProj a = torusProj b) :
    fderiv ℝ (fun y => g (torusProj y)) a = fderiv ℝ (fun y => g (torusProj y)) b := by
  have hc : torusProj (a - b) = 0 := (torusProj_eq_iff_sub a b).1 hab
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => g (torusProj y)) (x := b) (a - b)
  rw [lift_comp_add_of_torusProj_eq_zero g hc, add_sub_cancel] at h
  exact h.symm

@[simp]
theorem torusDescend_torusProj [TopologicalSpace F] (h : (Fin 3 → ℝ) → F) (hc : Continuous h)
    (hp : ∀ a b, torusProj a = torusProj b → h a = h b) (y : Fin 3 → ℝ) :
    torusDescend h hc hp (torusProj y) = h y :=
  hp _ _ (torusProj_torusRep _)

/-- Pointwise form of postcomposition with a continuous linear map. -/
@[simp]
theorem compLeftContinuous_apply_apply [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (g : C(Torus3, E)) (x : Torus3) : L.compLeftContinuous ℝ Torus3 g x = L (g x) := rfl

theorem ofPartials_apply (v : Fin 3 → E) (k : Fin 3 → ℝ) :
    ofPartials v k = ∑ i, k i • v i := by
  simp [ofPartials]

theorem ofPartials_single (v : Fin 3 → E) (i : Fin 3) : ofPartials v (Pi.single i 1) = v i := by
  rw [ofPartials_apply]
  simp [Pi.single_apply]

/-- A linear map on `ℝ³` is determined by its values on the coordinate vectors. -/
theorem ofPartials_apply_single (L : (Fin 3 → ℝ) →L[ℝ] E) :
    ofPartials (fun i => L (Pi.single i 1)) = L := by
  refine ContinuousLinearMap.ext fun k => ?_
  rw [ofPartials_apply]
  conv_rhs => rw [← Finset.univ_sum_single k]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

@[simp]
theorem evalAt_apply_apply (k : Fin 3 → ℝ) (g : C(Torus3, Fin 3 → E)) (x : Torus3) :
    evalAt k g x = ofPartials (g x) k := rfl

/-! ### Translations -/

@[simp]
theorem torusShift_apply (a : Torus3) (g : C(Torus3, E)) (x : Torus3) :
    torusShift a g x = g (x + a) := rfl

end RegularityStructures.PDE

end

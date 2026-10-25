/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.MaxPrinciple
public import RegularityStructures.PDE.Nonlin
public import RegularityStructures.PDE.Jet
public import RegularityStructures.PDE.DuhamelTime
public import RegularityStructures.PDE.SmoothDense
public import RegularityStructures.PDE.HeatOpBridge
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The semigroup property of the heat operator

`heatOp b (heatOp a g) = heatOp (a + b) g` for `a, b ≥ 0` and every `g ∈ C(T³, E)`
(`heatOp_heatOp`).

For smooth scalar `g` both sides solve the heat equation in `b` with the same initial value, so
their difference vanishes by the maximum principle (`eq_zero_of_heat_equation`). The general case
follows by density of smooth functions (Stone–Weierstrass) and the contraction property, and for
vector-valued `g` by testing against continuous linear functionals.
-/

open scoped ContDiff

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasTorusDeriv.sub {g h : C(Torus3, E)} {Dg Dh : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) (hh : HasTorusDeriv h Dh) : HasTorusDeriv (g - h) (Dg - Dh) := by
  simpa [sub_eq_add_neg] using hg.add hh.neg

theorem hasTorusDeriv_const (c : E) :
    HasTorusDeriv (ContinuousMap.const Torus3 c) (0 : C(Torus3, Fin 3 → E)) := by
  intro y
  simpa using hasFDerivAt_const c y

/-- One half of the uniqueness for the heat equation: a solution vanishing at time zero is
nonpositive. -/
theorem le_zero_of_heat_equation {w : ℝ → C(Torus3, ℝ)} {Dw : ℝ → C(Torus3, Fin 3 → ℝ)}
    {D2w : ℝ → C(Torus3, Fin 3 → Fin 3 → ℝ)} {T : ℝ} (hw : Continuous w) (h0 : w 0 = 0)
    (hdw : ∀ t ∈ Ioc 0 T, HasTorusDeriv (w t) (Dw t))
    (hdw2 : ∀ t ∈ Ioc 0 T, HasTorusDeriv (E := Fin 3 → ℝ) (Dw t) (D2w t))
    (hdt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => w s x) (torusLap (D2w t) x) t) :
    ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ 0 := by
  have key : ∀ ε > 0, ∀ t ∈ Icc 0 T, ∀ x, w t x < ε * (1 + t) := by
    intro ε hε
    have hu : Continuous fun s => w s - ContinuousMap.const Torus3 (ε * (1 + s)) :=
      hw.sub (ContinuousMap.continuous_const'.comp
        (continuous_const.mul (continuous_const.add continuous_id)))
    have h := lt_of_maxPrinciple (u := fun s => w s - ContinuousMap.const Torus3 (ε * (1 + s)))
      (w := fun s => Dw s - 0) (w2 := fun s => D2w s - 0) (L := 0) (T := T)
      (D := fun s x => torusLap (D2w s) x - ε) hu
      (fun x => by simp [h0, hε])
      (fun t ht => (hdw t ht).sub (hasTorusDeriv_const _))
      (fun t ht => (hdw2 t ht).sub (hasTorusDeriv_const (E := Fin 3 → ℝ) _))
      (fun t ht x => by
        have h1 := (hdt t ht x).fun_sub (((hasDerivAt_id' t).const_add 1).const_mul ε)
        simpa using h1)
      (fun t ht x _ => by simp [hε])
    intro t ht x
    have := h t ht x
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply] at this
    linarith
  intro t ht x
  have ht1 : 0 < 1 + t := by linarith [ht.1]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have := key (ε / (1 + t)) (div_pos hε ht1) t ht x
  rw [div_mul_cancel₀ ε ht1.ne'] at this
  linarith

/-- **Uniqueness for the heat equation** on `T³`. -/
theorem eq_zero_of_heat_equation {w : ℝ → C(Torus3, ℝ)} {Dw : ℝ → C(Torus3, Fin 3 → ℝ)}
    {D2w : ℝ → C(Torus3, Fin 3 → Fin 3 → ℝ)} {T : ℝ} (hw : Continuous w) (h0 : w 0 = 0)
    (hdw : ∀ t ∈ Ioc 0 T, HasTorusDeriv (w t) (Dw t))
    (hdw2 : ∀ t ∈ Ioc 0 T, HasTorusDeriv (E := Fin 3 → ℝ) (Dw t) (D2w t))
    (hdt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => w s x) (torusLap (D2w t) x) t) :
    ∀ t ∈ Icc 0 T, w t = 0 := by
  intro t ht
  ext x
  have h1 := le_zero_of_heat_equation hw h0 hdw hdw2 hdt t ht x
  have h2 := le_zero_of_heat_equation (w := fun s => -w s) (Dw := fun s => -Dw s)
    (D2w := fun s => -D2w s) hw.neg (by simp [h0]) (fun t ht => (hdw t ht).neg)
    (fun t ht => (hdw2 t ht).neg)
    (fun t ht x => by
      have := (hdt t ht x).fun_neg
      have hlap : torusLap (-D2w t) x = -torusLap (D2w t) x := by
        simp [torusLap_apply, Finset.sum_neg_distrib]
      simpa [hlap] using this) t ht x
  simp only [ContinuousMap.neg_apply] at h2
  simp only [ContinuousMap.zero_apply]
  linarith

theorem torusLap_heatOp (t : ℝ) (D2g : C(Torus3, Fin 3 → Fin 3 → ℝ)) :
    torusLap (heatOp t D2g) = heatOp t (torusLap D2g) := by
  rw [torusLap_eq_compLeft, torusLap_eq_compLeft, heatOp_compLeftContinuous]

theorem torusLap_sub (D2g D2h : C(Torus3, Fin 3 → Fin 3 → ℝ)) :
    torusLap (D2g - D2h) = torusLap D2g - torusLap D2h := by
  rw [torusLap_eq_compLeft, torusLap_eq_compLeft, torusLap_eq_compLeft, map_sub]

/-- The semigroup property for smooth scalar functions. -/
theorem heatOp_heatOp_of_smooth {g : C(Torus3, ℝ)} (hg : ContDiff ℝ ∞ fun y => g (torusProj y))
    {a : ℝ} (ha : 0 ≤ a) {b : ℝ} (hb : 0 ≤ b) : heatOp b (heatOp a g) = heatOp (a + b) g := by
  have hg1 : ContDiff ℝ 1 fun y => g (torusProj y) := hg.of_le (by exact_mod_cast le_top)
  set Dg := torusDerivOf g hg1 with hDgdef
  have hDg : HasTorusDeriv g Dg := hasTorusDeriv_torusDerivOf g hg1
  have hDgs : ContDiff ℝ ∞ fun y => Dg (torusProj y) := contDiff_torusDerivOf_lift hg
  have hDg1 : ContDiff ℝ 1 fun y => Dg (torusProj y) := hDgs.of_le (by exact_mod_cast le_top)
  set D2g := torusDerivOf (F := Fin 3 → ℝ) Dg hDg1 with hD2gdef
  have hD2g : HasTorusDeriv (E := Fin 3 → ℝ) Dg D2g :=
    hasTorusDeriv_torusDerivOf (F := Fin 3 → ℝ) Dg hDg1
  set w : ℝ → C(Torus3, ℝ) := fun s => heatOp (a + s) g - heatOp s (heatOp a g) with hwdef
  have hw : Continuous w :=
    ((continuous_const.add continuous_id).heatOp continuous_const).sub
      (continuous_id.heatOp continuous_const)
  have h0 : w 0 = 0 := by simp [hwdef, heatOp_zero_left]
  have hzero := eq_zero_of_heat_equation (T := b) (w := w)
    (Dw := fun s => heatOp (a + s) Dg - heatOp s (heatOp a Dg))
    (D2w := fun s => heatOp (a + s) D2g - heatOp s (heatOp a D2g)) hw h0
    (fun t _ => (hasTorusDeriv_heatOp hDg _).sub
      (hasTorusDeriv_heatOp (hasTorusDeriv_heatOp hDg a) t))
    (fun t _ => (hasTorusDeriv_heatOp hD2g _).sub
      (hasTorusDeriv_heatOp (hasTorusDeriv_heatOp hD2g a) t))
    (fun t ht x => by
      have hat : 0 < a + t := by linarith [ht.1]
      have h1 := (hasDerivAt_heatOp_apply hDg hD2g hat x).scomp t
        ((hasDerivAt_id' t).const_add a)
      have h2 := hasDerivAt_heatOp_apply (hasTorusDeriv_heatOp hDg a)
        (hasTorusDeriv_heatOp hD2g a) ht.1 x
      have h3 := h1.fun_sub h2
      rw [torusLap_heatOp] at h3
      rw [torusLap_sub, torusLap_heatOp, torusLap_heatOp, torusLap_heatOp]
      simpa [Function.comp_def, hwdef] using h3) b ⟨hb, le_rfl⟩
  have := sub_eq_zero.1 hzero
  exact this.symm

end RegularityStructures.PDE

end

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The semigroup property for continuous scalar functions. -/
theorem heatOp_heatOp_real {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : C(Torus3, ℝ)) :
    heatOp b (heatOp a g) = heatOp (a + b) g := by
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨h, hh, hgh⟩ := exists_smooth_near g (half_pos hε)
  have hsm := heatOp_heatOp_of_smooth hh ha hb
  calc ‖heatOp b (heatOp a g) - heatOp (a + b) g‖
      = ‖heatOp b (heatOp a (g - h)) - heatOp (a + b) (g - h)‖ := by
        rw [heatOp_sub, heatOp_sub, heatOp_sub, hsm]
        abel_nf
    _ ≤ ‖heatOp b (heatOp a (g - h))‖ + ‖heatOp (a + b) (g - h)‖ := norm_sub_le _ _
    _ ≤ ‖g - h‖ + ‖g - h‖ :=
        add_le_add ((norm_heatOp_le _ _).trans (norm_heatOp_le _ _)) (norm_heatOp_le _ _)
    _ ≤ 0 + ε := by linarith

/-- **The semigroup property** `P_b P_a = P_{a + b}` for `a, b ≥ 0`. -/
theorem heatOp_heatOp [CompleteSpace E] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (g : C(Torus3, E)) : heatOp b (heatOp a g) = heatOp (a + b) g := by
  ext x
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  have h := congrArg (fun f : C(Torus3, ℝ) => f x)
    (heatOp_heatOp_real ha hb (ℓ.compLeftContinuous ℝ Torus3 g))
  simp only [heatOp_compLeftContinuous, compLeftContinuous_apply_apply] at h
  exact h

/-- The semigroup property for the project's `heatSemigroup`, whose values are written as
functions: `P_t (P_s f) = P_{s+t} f` for `s, t > 0`. -/
theorem heatSemigroup_heatOp {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (f : C(Torus3, ℝ))
    (x : Torus3) : heatSemigroup t (heatOp s f) x = heatSemigroup (s + t) f x := by
  rw [← heatOp_eq_heatSemigroup ht, ← heatOp_eq_heatSemigroup (by linarith),
    heatOp_heatOp hs.le ht.le]

end RegularityStructures.PDE

end

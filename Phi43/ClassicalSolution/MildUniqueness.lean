/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MildComparison
public import Phi43.ClassicalSolution.MildRegularity

/-!
# Finite-window stability for smooth cubic solutions

This localizes the maximum-principle stability estimate to two paths continuous on a finite closed interval and smooth on its
interior. It is a comparison input for the identification of the abstract Φ⁴₃ solution with the
classical solution; it does not assume either path extends as a solution beyond the window.
-/

public section

open MeasureTheory Set Function Filter
open scoped ContDiff Topology

namespace RegularityStructures.Phi43

private theorem torusProj_update_add_period (i : Fin 3) (y : Fin 3 → ℝ) :
    torusProj (Function.update y i (y i + 1)) = torusProj y := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [torusProj]
    simp [Function.update]
  · change ((Function.update y i (y i + 1)) j : UnitAddCircle) = (y j : UnitAddCircle)
    simp [Function.update, h]


theorem finiteWindow_cubic_classical_sup_stability (c : ℝ) {f f' : SpaceTime → ℝ}
    {u₀ : C(Torus3, ℝ)} {u u' : ℝ → C(Torus3, ℝ)} {T S : ℝ}
    (hcu : ContinuousOn (fun z : SpaceTime => u z.1 z.2) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (fun z : SpaceTime => u' z.1 z.2) (Icc 0 T ×ˢ univ))
    (hinitU : u 0 = u₀) (hinitV : u' 0 = u₀)
    (hsmU : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (Ioo 0 T ×ˢ univ))
    (hsmV : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u' p.1 (torusProj p.2))
      (Ioo 0 T ×ˢ univ))
    (heqU0 : ∀ s ∈ Ioo 0 T, ∀ y : Fin 3 → ℝ,
      deriv (fun r => u r (torusProj y)) s =
        (∑ i, deriv (deriv fun r => u s (torusProj (Function.update y i r))) (y i)) -
          u s (torusProj y) ^ 3 + c * u s (torusProj y) + f (s, torusProj y))
    (heqV0 : ∀ s ∈ Ioo 0 T, ∀ y : Fin 3 → ℝ,
      deriv (fun r => u' r (torusProj y)) s =
        (∑ i, deriv (deriv fun r => u' s (torusProj (Function.update y i r))) (y i)) -
          u' s (torusProj y) ^ 3 + c * u' s (torusProj y) + f' (s, torusProj y))
    (hT : 0 ≤ S) (hST : S < T) (B : ℝ) (hB : 0 ≤ B)
    (hforce : ∀ s ∈ Icc 0 S, ∀ x : Torus3, |f (s, x) - f' (s, x)| ≤ B) :
    ∀ t ∈ Icc 0 S, ‖u t - u' t‖ ≤ B * t * Real.exp (|c| * t) := by
  by_cases hT0 : S = 0
  · subst S
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    rw [hinitU, hinitV]
    simp
  have hTpos : 0 < S := lt_of_le_of_ne hT (Ne.symm hT0)
  let Ω : Set (ℝ × (Fin 3 → ℝ)) := Ioo 0 T ×ˢ Set.univ
  let U : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => u p.1 (torusProj p.2)
  let V : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => u' p.1 (torusProj p.2)
  let W : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => U p - V p
  have hU : ContDiffOn ℝ ∞ U Ω := by
    simpa [U, Ω] using hsmU
  have hV : ContDiffOn ℝ ∞ V Ω := by
    simpa [V, Ω] using hsmV
  have hW : ContDiffOn ℝ ∞ W Ω := hU.sub hV
  have hperiod : ∀ (s : ℝ) (i : Fin 3) (y : Fin 3 → ℝ),
      W (s, Function.update y i (y i + 1)) = W (s, y) := by
    intro s i y
    simp only [W, U, V]
    rw [torusProj_update_add_period]
  have htorus : Continuous torusProj :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
  have hmap : Continuous (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) :=
    continuous_fst.prodMk (htorus.comp continuous_snd)
  have hUc : ContinuousOn U (Icc 0 T ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (Icc 0 T ×ˢ Set.univ)
    exact hcu.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ p.2⟩)
  have hVc : ContinuousOn V (Icc 0 T ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => u' p.1 (torusProj p.2))
      (Icc 0 T ×ˢ Set.univ)
    exact hcv.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ p.2⟩)
  have hWc : ContinuousOn W (Icc 0 T ×ˢ Set.univ) := hUc.sub hVc
  have hWzero : ∀ y : Fin 3 → ℝ, W (0, y) = 0 := by
    intro y
    simp [W, U, V, hinitU, hinitV]
  have hUspace {s : ℝ} (hs : s ∈ Ioo 0 T) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => U (s, y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hAt : ContDiffAt ℝ ∞ U (s, y) :=
      (hU (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    exact (hAt.comp y (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
      (by norm_num)
  have hVspace {s : ℝ} (hs : s ∈ Ioo 0 T) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => V (s, y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hAt : ContDiffAt ℝ ∞ V (s, y) :=
      (hV (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    exact (hAt.comp y (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
      (by norm_num)
  have hWspace {s : ℝ} (hs : s ∈ Ioo 0 T) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => W (s, y)) :=
    (hUspace hs).sub (hVspace hs)
  have hsecondW {s : ℝ} (hs : s ∈ Ioo 0 T) (i : Fin 3) (y : Fin 3 → ℝ) :
      deriv (deriv (fun r => W (s, Function.update y i r))) (y i) =
        deriv (deriv (fun r => U (s, Function.update y i r))) (y i) -
          deriv (deriv (fun r => V (s, Function.update y i r))) (y i) := by
    have hUs : ContDiff ℝ 2 (fun r => U (s, Function.update y i r)) :=
      (hUspace hs).comp (contDiff_update 2 y i)
    have hVs : ContDiff ℝ 2 (fun r => V (s, Function.update y i r)) :=
      (hVspace hs).comp (contDiff_update 2 y i)
    have hWs : ContDiff ℝ 2 (fun r => W (s, Function.update y i r)) := by
      simpa [W] using hUs.sub hVs
    have hUd : ContDiff ℝ 1
        (fun r => deriv (fun z => U (s, Function.update y i z)) r) := by
      unfold deriv
      exact (hUs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hVd : ContDiff ℝ 1
        (fun r => deriv (fun z => V (s, Function.update y i z)) r) := by
      unfold deriv
      exact (hVs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hinner : (fun r => deriv (fun z => W (s, Function.update y i z)) r) =
        (fun r => deriv (fun z => U (s, Function.update y i z)) r -
          deriv (fun z => V (s, Function.update y i z)) r) := by
      funext r
      rw [show (fun z => W (s, Function.update y i z)) =
          (fun z => U (s, Function.update y i z) - V (s, Function.update y i z)) by
            funext z; rfl]
      exact deriv_fun_sub (hUs.differentiable (by norm_num) _)
        (hVs.differentiable (by norm_num) _)
    change deriv (fun r => deriv (fun z => W (s, Function.update y i z)) r) (y i) = _
    rw [hinner]
    exact deriv_fun_sub (hUd.differentiable (by norm_num) _)
      (hVd.differentiable (by norm_num) _)
  have hWtime {s : ℝ} (hs : s ∈ Ioo 0 T) (y : Fin 3 → ℝ) :
      HasDerivAt (fun r => W (r, y)) (deriv (fun r => W (r, y)) s) s := by
    have hAt : ContDiffAt ℝ ∞ W (s, y) :=
      (hW (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    have hpath : HasDerivAt (fun r : ℝ => (r, y)) (1, 0) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
    have hcomp :=
      (hAt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hpath
    have hcomp' := hcomp.congr_deriv hcomp.deriv.symm
    simpa [Function.comp_def] using hcomp'
  let q : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p =>
    U p ^ 2 + U p * V p + V p ^ 2
  have hq : ∀ s y, 0 ≤ q (s, y) := by
    intro s y
    dsimp [q]
    nlinarith [sq_nonneg (U (s, y) + V (s, y)), sq_nonneg (U (s, y)),
      sq_nonneg (V (s, y))]
  have hEq {s : ℝ} (hs : s ∈ Ioo 0 T) (y : Fin 3 → ℝ) :
      deriv (fun r => W (r, y)) s =
        (∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) -
          q (s, y) * W (s, y) + c * W (s, y) +
            (f (s, torusProj y) - f' (s, torusProj y)) := by
    have hAtU : ContDiffAt ℝ ∞ U (s, y) :=
      (hU (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    have hAtV : ContDiffAt ℝ ∞ V (s, y) :=
      (hV (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    have hpathU : ContDiffAt ℝ ∞ (fun r => U (r, y)) s :=
      hAtU.comp s (contDiff_id.prodMk contDiff_const).contDiffAt
    have hpathV : ContDiffAt ℝ ∞ (fun r => V (r, y)) s :=
      hAtV.comp s (contDiff_id.prodMk contDiff_const).contDiffAt
    have heqU := heqU0 s hs y
    have heqV := heqV0 s hs y
    change deriv (fun r => U (r, y)) s =
      (∑ i, deriv (deriv (fun r => U (s, Function.update y i r))) (y i)) -
        U (s, y) ^ 3 + c * U (s, y) + f (s, torusProj y) at heqU
    change deriv (fun r => V (r, y)) s =
      (∑ i, deriv (deriv (fun r => V (s, Function.update y i r))) (y i)) -
        V (s, y) ^ 3 + c * V (s, y) + f' (s, torusProj y) at heqV
    calc
      deriv (fun r => W (r, y)) s =
          deriv (fun r => U (r, y)) s - deriv (fun r => V (r, y)) s := by
        exact deriv_fun_sub (hpathU.differentiableAt (by norm_num))
          (hpathV.differentiableAt (by norm_num))
      _ = ((∑ i, deriv (deriv (fun r => U (s, Function.update y i r))) (y i)) -
          U (s, y) ^ 3 + c * U (s, y) + f (s, torusProj y)) -
          ((∑ i, deriv (deriv (fun r => V (s, Function.update y i r))) (y i)) -
          V (s, y) ^ 3 + c * V (s, y) + f' (s, torusProj y)) := by rw [heqU, heqV]
      _ = (∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) -
          q (s, y) * W (s, y) + c * W (s, y) +
            (f (s, torusProj y) - f' (s, torusProj y)) := by
        simp_rw [hsecondW hs]
        simp only [Finset.sum_sub_distrib]
        simp [W, q]
        ring
  let D : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)
  have hforce_le : ∀ s ∈ Icc (0 : ℝ) S, ∀ y,
      f (s, torusProj y) - f' (s, torusProj y) ≤ B := by
    intro s hs y
    exact (le_abs_self _).trans (hforce s hs (torusProj y))
  have hupper : ∀ s ∈ Icc (0 : ℝ) S, ∀ y ∈ D,
      W (s, y) ≤ B * s * Real.exp (|c| * s) := by
    exact finiteWindow_upper_comparison_bound (q := q)
      (g := fun p => f (p.1, torusProj p.2) - f' (p.1, torusProj p.2))
      hTpos hB (hWc.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hST.le⟩, hp.2⟩))
      (fun hs => hWspace ⟨hs.1, hs.2.trans_lt hST⟩)
      (fun hs => hWtime ⟨hs.1, hs.2.trans_lt hST⟩) hperiod hWzero
      (fun hs => hEq ⟨hs.1, hs.2.trans_lt hST⟩) hq
      hforce_le
  let Wn : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => -W p
  have hWnc : ContinuousOn Wn (Icc 0 T ×ˢ Set.univ) := hWc.neg
  have hWnspace {s : ℝ} (hs : s ∈ Ioo 0 T) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => Wn (s, y)) := by
    simpa [Wn] using (hWspace hs).neg
  have hWntime {s : ℝ} (hs : s ∈ Ioo 0 T) (y : Fin 3 → ℝ) :
      HasDerivAt (fun r => Wn (r, y)) (deriv (fun r => Wn (r, y)) s) s := by
    have hn := (hWtime hs y).neg
    change HasDerivAt (fun r => -W (r, y))
      (deriv (fun r => -W (r, y)) s) s
    exact hn.congr_deriv hn.deriv.symm
  have hWnperiod : ∀ (s : ℝ) (i : Fin 3) (y : Fin 3 → ℝ),
      Wn (s, Function.update y i (y i + 1)) = Wn (s, y) := by
    intro s i y
    simp [Wn, hperiod s i y]
  have hWnzero : ∀ y, Wn (0, y) = 0 := by
    intro y
    simp [Wn, hWzero y]
  have hEqn {s : ℝ} (hs : s ∈ Ioo 0 T) (y : Fin 3 → ℝ) :
      deriv (fun r => Wn (r, y)) s =
        (∑ i, deriv (deriv (fun r => Wn (s, Function.update y i r))) (y i)) -
          q (s, y) * Wn (s, y) + c * Wn (s, y) +
            (f' (s, torusProj y) - f (s, torusProj y)) := by
    have h := hEq hs y
    have hder := (hWtime hs y).neg.deriv
    have hsecondN : ∀ i,
        deriv (deriv (fun r => Wn (s, Function.update y i r))) (y i) =
          -deriv (deriv (fun r => W (s, Function.update y i r))) (y i) := by
      intro i
      simp [Wn]
    change deriv (fun r => -W (r, y)) s = _
    have hder' : deriv (fun r => -W (r, y)) s = -deriv (fun r => W (r, y)) s := by
      rw [show (fun r => -W (r, y)) = -(fun r => W (r, y)) by
        funext r; rfl]
      exact hder
    rw [hder']
    simp_rw [hsecondN]
    simp [Wn]
    ring_nf at h ⊢
    linarith
  have hforce_neg : ∀ s ∈ Icc (0 : ℝ) S, ∀ y,
      f' (s, torusProj y) - f (s, torusProj y) ≤ B := by
    intro s hs y
    have hf := hforce s hs (torusProj y)
    rw [abs_sub_comm] at hf
    exact (le_abs_self _).trans hf
  have hupperN : ∀ s ∈ Icc (0 : ℝ) S, ∀ y ∈ D,
      Wn (s, y) ≤ B * s * Real.exp (|c| * s) := by
    exact finiteWindow_upper_comparison_bound (q := q)
      (g := fun p => f' (p.1, torusProj p.2) - f (p.1, torusProj p.2))
      hTpos hB (hWnc.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hST.le⟩, hp.2⟩))
      (fun hs => hWnspace ⟨hs.1, hs.2.trans_lt hST⟩)
      (fun hs => hWntime ⟨hs.1, hs.2.trans_lt hST⟩) hWnperiod hWnzero
      (fun hs => hEqn ⟨hs.1, hs.2.trans_lt hST⟩) hq
      hforce_neg
  intro t ht
  have hbound0 : 0 ≤ B * t * Real.exp (|c| * t) :=
    mul_nonneg (mul_nonneg hB ht.1) (Real.exp_nonneg _)
  apply (ContinuousMap.norm_le (u t - u' t) hbound0).2
  intro x
  let y : Fin 3 → ℝ := fun i => (AddCircle.equivIoc (1 : ℝ) 0 (x i) : ℝ)
  have hy : y ∈ D := by
    intro i hi
    change (AddCircle.equivIoc (1 : ℝ) 0 (x i) : ℝ) ∈ Icc 0 1
    have hi' := (AddCircle.equivIoc (1 : ℝ) 0 (x i)).property
    exact ⟨hi'.1.le, by simpa using hi'.2⟩
  have hproj : torusProj y = x := by
    funext i
    dsimp [torusProj, y]
    exact AddCircle.coe_equivIoc
  have hup := hupper t ht y hy
  have hlow := hupperN t ht y hy
  have habs : |W (t, y)| ≤ B * t * Real.exp (|c| * t) := by
    apply abs_le.2
    constructor
    · linarith [hlow]
    · exact hup
  simpa [W, U, V, hproj, Real.norm_eq_abs] using habs

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MeasurableSupport
public import Phi43.ClassicalSolution.CubicMonotonicity
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Order.Compact

/-!
# Sup-norm stability of classical solutions

This module supplies the comparison estimate used for the measurability half of item (W5) of
Lemma 4.1 of the statement.  The spatial maximum principle is
applied to the periodic lift on one closed fundamental cube; periodicity also handles a maximum
on a cube face.  The cubic term enters only through
`a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2)`.

The comparison argument is the classical maximum-principle estimate for the classical solutions
of Definition 2.6 of the statement.
-/

public section

open MeasureTheory Set Function Filter
open scoped ContDiff
open scoped Topology

namespace RegularityStructures.Phi43

private theorem spatial_second_deriv_nonpos
    {F : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hper : ∀ (i : Fin 3) (z : Fin 3 → ℝ),
      F (Function.update z i (z i + 1)) = F z)
    (hy : ∀ z, z ∈ Set.univ.pi (fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) → F z ≤ F y)
    (hyi : y ∈ Set.univ.pi (fun _ : Fin 3 => Set.Icc (0 : ℝ) 1))
    (i : Fin 3) : deriv (deriv (fun r => F (Function.update y i r))) (y i) ≤ 0 := by
  have hloc : IsLocalMax (fun r => F (Function.update y i r)) (y i) := by
    unfold IsLocalMax IsMaxFilter
    by_cases h0 : y i = 0
    · filter_upwards [Metric.ball_mem_nhds (y i) (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
      rw [Metric.mem_ball, Real.dist_eq] at hr
      rw [h0] at hr
      rcases abs_lt.mp hr with ⟨hrlo, hrhi⟩
      by_cases hr0 : 0 ≤ r
      · have hmem : Function.update y i r ∈ Set.univ.pi
            (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [Function.update]
            constructor <;> linarith
          · simpa [Function.update, hji] using (hyi j (by simp))
        simpa using hy _ hmem
      · have hr1 : r + 1 ∈ Icc (0 : ℝ) 1 := by
          constructor <;> linarith
        have hmem : Function.update y i (r + 1) ∈ Set.univ.pi
            (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
          intro j hj
          by_cases hji : j = i
          · subst j
            simpa [Function.update] using hr1
          · simpa [Function.update, hji] using (hyi j (by simp))
        have hper' := hper i (Function.update y i r)
        have heq : F (Function.update y i r) = F (Function.update y i (r + 1)) := by
          simpa [Function.update] using hper'.symm
        rw [heq]
        simpa using hy _ hmem
    · have h0or : 0 < y i := lt_of_le_of_ne (hyi i (by simp)).1 (Ne.symm h0)
      by_cases h1 : y i = 1
      · filter_upwards [Metric.ball_mem_nhds (y i) (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
        rw [Metric.mem_ball, Real.dist_eq] at hr
        rw [h1] at hr
        rcases abs_lt.mp hr with ⟨hrlo, hrhi⟩
        by_cases hr1 : r ≤ 1
        · have hmem : Function.update y i r ∈ Set.univ.pi
              (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
            intro j hj
            by_cases hji : j = i
            · subst j
              simp [Function.update]
              constructor
              · have := (abs_lt.1 hr).1
                linarith
              · exact hr1
            · simpa [Function.update, hji] using (hyi j (by simp))
          simpa using hy _ hmem
        · have hr0 : r - 1 ∈ Icc (0 : ℝ) 1 := by
            constructor <;> linarith
          have hmem : Function.update y i (r - 1) ∈ Set.univ.pi
              (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
            intro j hj
            by_cases hji : j = i
            · subst j
              simpa [Function.update] using hr0
            · simpa [Function.update, hji] using (hyi j (by simp))
          have hper' := hper i (Function.update y i (r - 1))
          have heq : F (Function.update y i r) = F (Function.update y i (r - 1)) := by
            simpa [Function.update] using hper'
          rw [heq]
          simpa using hy _ hmem
      · have h1or : y i < 1 := lt_of_le_of_ne (hyi i (by simp)).2 h1
        let δ : ℝ := min (y i) (1 - y i)
        have hδ : 0 < δ := lt_min h0or (sub_pos.mpr h1or)
        filter_upwards [Metric.ball_mem_nhds (y i) hδ] with r hr
        rw [Metric.mem_ball, Real.dist_eq] at hr
        have hmem : Function.update y i r ∈ Set.univ.pi
            (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [Function.update]
            rcases abs_lt.mp hr with ⟨hrl, hrr⟩
            constructor <;> linarith [min_le_left (y i) (1 - y i),
              min_le_right (y i) (1 - y i)]
          · simpa [Function.update, hji] using (hyi j (by simp))
        simpa using hy _ hmem
  exact second_deriv_nonpos_of_isLocalMax hloc
    (hF.comp (contDiff_update 2 y i))

private theorem endpoint_deriv_nonneg {T : ℝ} {f : ℝ → ℝ} {f' : ℝ}
    (hT : 0 < T) (hmax : ∀ z ∈ Icc 0 T, f z ≤ f T)
    (hf : HasDerivAt f f' T) : 0 ≤ f' := by
  have hslope : ∀ᶠ z in 𝓝[<] T, 0 ≤ slope f T z := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hT)] with z hz hzpos
    have hzmax := hmax z ⟨le_of_lt hzpos, le_of_lt hz⟩
    rw [slope]
    change 0 ≤ (z - T)⁻¹ * (f z - f T)
    exact mul_nonneg_of_nonpos_of_nonpos
      (inv_nonpos.mpr (sub_nonpos.mpr (le_of_lt hz))) (sub_nonpos.mpr hzmax)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((hasDerivAt_iff_tendsto_slope_left_right.mp hf).1) hslope

private theorem upper_comparison_bound
    {W q g : (ℝ × (Fin 3 → ℝ)) → ℝ} {c B T : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B)
    (hWc : ContinuousOn W (Ici 0 ×ˢ Set.univ))
    (hWspace : ∀ {s : ℝ}, 0 < s → ContDiff ℝ 2 (fun y => W (s, y)))
    (hWtime : ∀ {s : ℝ}, 0 < s → ∀ y,
      HasDerivAt (fun r => W (r, y)) (deriv (fun r => W (r, y)) s) s)
    (hperiod : ∀ (s : ℝ) (i : Fin 3) (y : Fin 3 → ℝ),
      W (s, Function.update y i (y i + 1)) = W (s, y))
    (hWzero : ∀ y, W (0, y) = 0)
    (hEq : ∀ {s : ℝ}, 0 < s → ∀ y,
      deriv (fun r => W (r, y)) s =
        (∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) -
          q (s, y) * W (s, y) + c * W (s, y) + g (s, y))
    (hq : ∀ s y, 0 ≤ q (s, y))
    (hg : ∀ s ∈ Icc 0 T, ∀ y, g (s, y) ≤ B) :
    ∀ s ∈ Icc 0 T, ∀ y ∈ Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1),
      W (s, y) ≤ B * s * Real.exp (|c| * s) := by
  let D : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)
  let K : Set (ℝ × (Fin 3 → ℝ)) := Icc 0 T ×ˢ D
  have hK : IsCompact K := by
    exact isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hKne : K.Nonempty := by
    refine ⟨(0, fun _ => 0), ⟨⟨le_rfl, le_of_lt hT⟩, ?_⟩⟩
    intro i hi
    exact ⟨le_rfl, zero_le_one⟩
  have hWcK : ContinuousOn W K := hWc.mono fun p hp => ⟨hp.1.1, mem_univ _⟩
  have habs : 0 ≤ |c| := abs_nonneg c
  have hbarrier : ∀ ε : ℝ, 0 < ε →
      ∀ p ∈ K, Real.exp (-|c| * p.1) * W p - B * p.1 - ε * (p.1 + 1) ≤ 0 := by
    intro ε hε
    let V : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p =>
      Real.exp (-|c| * p.1) * W p - B * p.1 - ε * (p.1 + 1)
    have harg : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => -|c| * p.1) K :=
      continuousOn_const.mul continuousOn_fst
    have hexp : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) =>
        Real.exp (-|c| * p.1)) K :=
      Real.continuous_exp.continuousOn.comp harg (fun _ _ => mem_univ _)
    have hBt : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => B * p.1) K :=
      continuousOn_const.mul continuousOn_fst
    have hEt : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => ε * (p.1 + 1)) K :=
      continuousOn_const.mul (continuousOn_fst.add continuousOn_const)
    have hVcont : ContinuousOn V K := by
      dsimp [V]
      exact (hexp.mul hWcK).sub hBt |>.sub hEt
    have hVnonpos : ∀ p ∈ K, V p ≤ 0 := by
      intro p hp
      by_contra hnot
      have hp_pos : 0 < V p := lt_of_not_ge hnot
      rcases hK.exists_isMaxOn hKne hVcont with ⟨pm, hpm, hmax⟩
      have hmax' : ∀ z ∈ K, V z ≤ V pm := isMaxOn_iff.mp hmax
      have hpm_pos : 0 < V pm := lt_of_lt_of_le hp_pos (hmax' p hp)
      rcases pm with ⟨s, y⟩
      have hs : s ∈ Icc (0 : ℝ) T := hpm.1
      have hy : y ∈ D := hpm.2
      have hspmax : ∀ z, z ∈ D → W (s, z) ≤ W (s, y) := by
        intro z hz
        have hVmax := hmax' (s, z) ⟨hs, hz⟩
        have hEpos : 0 < Real.exp (-|c| * s) := Real.exp_pos _
        have hmul : Real.exp (-|c| * s) * W (s, z) ≤
            Real.exp (-|c| * s) * W (s, y) := by
          dsimp [V] at hVmax
          linarith
        exact le_of_mul_le_mul_left hmul hEpos
      have hWpos : 0 < W (s, y) := by
        have hsum : 0 < Real.exp (-|c| * s) * W (s, y) := by
          calc
            0 < V (s, y) := hp_pos.trans_le (hmax' p hp)
            _ ≤ V (s, y) + B * s + ε * (s + 1) := by
              have hs0 : 0 ≤ s := hs.1
              have hε0 : 0 ≤ ε * (s + 1) :=
                mul_nonneg hε.le (by linarith)
              linarith [mul_nonneg hB hs0]
            _ = Real.exp (-|c| * s) * W (s, y) := by
              dsimp [V]
              ring
        rcases (mul_pos_iff.mp hsum) with h | h
        · exact h.2
        · exact False.elim (not_lt_of_ge (Real.exp_pos _).le h.1)
      have hspos : 0 < s := by
        by_contra hs0
        have hs_eq : s = 0 := le_antisymm (not_lt.mp hs0) hs.1
        subst s
        have : V (0, y) < 0 := by
          dsimp [V]
          rw [hWzero y]
          have := mul_pos hε (by norm_num : (0 : ℝ) < (1 : ℝ))
          linarith
        exact (not_lt_of_ge (le_of_lt hp_pos))
          (lt_of_le_of_lt (hmax' p hp) this)
      have hlap : (∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) ≤ 0 := by
        apply Finset.sum_nonpos
        intro i hi
        exact spatial_second_deriv_nonpos (hWspace hspos)
          (hperiod s) (hspmax) hy i
      have hqW : 0 ≤ q (s, y) * W (s, y) := mul_nonneg (hq s y) hWpos.le
      have hg' : g (s, y) ≤ B := hg s hs y
      have hinside :
          (∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) -
              q (s, y) * W (s, y) + c * W (s, y) + g (s, y) ≤
            c * W (s, y) + B := by
        linarith
      have hEderiv : HasDerivAt (fun r : ℝ => Real.exp (-|c| * r))
          (-|c| * Real.exp (-|c| * s)) s := by
        have harg' : HasDerivAt (fun r : ℝ => -|c| * r) (-|c|) s := by
          simpa using (hasDerivAt_id s).const_mul (-|c|)
        convert (Real.hasDerivAt_exp (-|c| * s)).comp s harg' using 1
        · simp [Function.comp_def]
        · ring
      have hVderiv : HasDerivAt (fun r : ℝ => V (r, y))
          (Real.exp (-|c| * s) * deriv (fun r => W (r, y)) s -
            |c| * Real.exp (-|c| * s) * W (s, y) - B - ε) s := by
        have hB' : HasDerivAt (fun r : ℝ => B * r) B s := by
          simpa using (hasDerivAt_id s).const_mul B
        have hε' : HasDerivAt (fun r : ℝ => ε * (r + 1)) ε s := by
          convert (hasDerivAt_const s ε).mul ((hasDerivAt_id s).add_const 1) using 1
          · funext r
            simp
          · simp
        dsimp [V]
        convert (hEderiv.mul (hWtime hspos y)).sub hB' |>.sub hε' using 1;
          ring
      have hderiv_le : deriv (fun r : ℝ => V (r, y)) s ≤ -ε := by
        calc
          deriv (fun r : ℝ => V (r, y)) s =
              Real.exp (-|c| * s) * deriv (fun r => W (r, y)) s -
                |c| * Real.exp (-|c| * s) * W (s, y) - B - ε := hVderiv.deriv
          _ = Real.exp (-|c| * s) *
                ((∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) -
                  q (s, y) * W (s, y) + c * W (s, y) + g (s, y)) -
                |c| * Real.exp (-|c| * s) * W (s, y) - B - ε := by
              rw [hEq hspos y]
          _ ≤ Real.exp (-|c| * s) * (c * W (s, y) + B) -
                |c| * Real.exp (-|c| * s) * W (s, y) - B - ε := by
              linarith [mul_le_mul_of_nonneg_left hinside
                (Real.exp_nonneg (-|c| * s))]
          _ ≤ -ε := by
            have hcw : (c - |c|) * W (s, y) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_abs_self c)) hWpos.le
            have hEcw : Real.exp (-|c| * s) * ((c - |c|) * W (s, y)) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hcw
            have hEone : Real.exp (-|c| * s) ≤ 1 := by
              apply Real.exp_le_one_iff.mpr
              exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr habs) hs.1
            have hEB : Real.exp (-|c| * s) * B - B ≤ 0 := by
              apply sub_nonpos.mpr
              calc
                Real.exp (-|c| * s) * B ≤ 1 * B :=
                  mul_le_mul_of_nonneg_right hEone hB
                _ = B := one_mul B
            linarith
      by_cases hsT : s < T
      · have hlocal : IsLocalMax (fun r : ℝ => V (r, y)) s := by
          unfold IsLocalMax IsMaxFilter
          have hIoo : Ioo (0 : ℝ) T ∈ 𝓝 s :=
            isOpen_Ioo.mem_nhds ⟨hspos, hsT⟩
          filter_upwards [hIoo] with r hr
          exact hmax' (r, y) ⟨⟨hr.1.le, hr.2.le⟩, hy⟩
        have hz : deriv (fun r : ℝ => V (r, y)) s = 0 := hlocal.deriv_eq_zero
        linarith
      · have hsT' : s = T := le_antisymm hs.2 (not_lt.mp hsT)
        subst s
        have hmaxT : ∀ r ∈ Icc (0 : ℝ) T, V (r, y) ≤ V (T, y) := by
          intro r hr
          exact hmax' (r, y) ⟨hr, hy⟩
        have hz := endpoint_deriv_nonneg hT hmaxT hVderiv
        have hz' := hVderiv.deriv
        linarith
    exact hVnonpos
  intro s hs y hy
  by_cases hs0 : s = 0
  · subst s
    simp [hWzero y]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / (Real.exp (|c| * s) * (s + 1))
  have hs0 : 0 ≤ s := hs.1
  have hden : 0 < Real.exp (|c| * s) * (s + 1) :=
    mul_pos (Real.exp_pos _) (by linarith)
  have hε : 0 < ε := div_pos hδ hden
  have hb := hbarrier ε hε (s, y) ⟨hs, hy⟩
  have hmain : W (s, y) ≤ Real.exp (|c| * s) *
      (B * s + ε * (s + 1)) := by
    have hmul : Real.exp (-|c| * s) * W (s, y) ≤ B * s + ε * (s + 1) := by
      linarith
    have hprod : Real.exp (|c| * s) * Real.exp (-|c| * s) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      W (s, y) = 1 * W (s, y) := by simp
      _ = (Real.exp (|c| * s) * Real.exp (-|c| * s)) * W (s, y) := by rw [hprod]
      _ = Real.exp (|c| * s) * (Real.exp (-|c| * s) * W (s, y)) := by ring
      _ ≤ Real.exp (|c| * s) * (B * s + ε * (s + 1)) :=
        mul_le_mul_of_nonneg_left hmul (Real.exp_nonneg _)
  calc
    W (s, y) ≤ Real.exp (|c| * s) * (B * s + ε * (s + 1)) := hmain
    _ = B * s * Real.exp (|c| * s) + δ := by
      dsimp [ε]
      field_simp

private theorem torusProj_update_add_period (i : Fin 3) (y : Fin 3 → ℝ) :
    torusProj (Function.update y i (y i + 1)) = torusProj y := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [torusProj]
    simp [Function.update]
  · change ((Function.update y i (y i + 1)) j : UnitAddCircle) = (y j : UnitAddCircle)
    simp [Function.update, h]

theorem classicalSolution_sup_stability (c : ℝ) {f f' : SpaceTime → ℝ}
    {u₀ : C(Torus3, ℝ)} {u u' : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution c f u₀ u) (hu' : IsClassicalSolution c f' u₀ u')
    {T : ℝ} (hT : 0 ≤ T) (B : ℝ) (hB : 0 ≤ B)
    (hforce : ∀ s ∈ Icc 0 T, ∀ x : Torus3, |f (s, x) - f' (s, x)| ≤ B) :
    ∀ t ∈ Icc 0 T, ‖u t - u' t‖ ≤ B * t * Real.exp (|c| * t) := by
  by_cases hT0 : T = 0
  · subst T
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    rw [hu.initial, hu'.initial]
    simp
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  let S : Set (ℝ × (Fin 3 → ℝ)) := Ioi 0 ×ˢ Set.univ
  let U : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => u p.1 (torusProj p.2)
  let V : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => u' p.1 (torusProj p.2)
  let W : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => U p - V p
  have hU : ContDiffOn ℝ ∞ U S := by
    simpa [U, S] using hu.contDiffOn
  have hV : ContDiffOn ℝ ∞ V S := by
    simpa [V, S] using hu'.contDiffOn
  have hW : ContDiffOn ℝ ∞ W S := hU.sub hV
  have hperiod : ∀ (s : ℝ) (i : Fin 3) (y : Fin 3 → ℝ),
      W (s, Function.update y i (y i + 1)) = W (s, y) := by
    intro s i y
    simp only [W, U, V]
    rw [torusProj_update_add_period]
  have htorus : Continuous torusProj :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
  have hmap : Continuous (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) :=
    continuous_fst.prodMk (htorus.comp continuous_snd)
  have hUc : ContinuousOn U (Ici 0 ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (Ici 0 ×ˢ Set.univ)
    exact hu.continuousOn.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ p.2⟩)
  have hVc : ContinuousOn V (Ici 0 ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => u' p.1 (torusProj p.2))
      (Ici 0 ×ˢ Set.univ)
    exact hu'.continuousOn.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ p.2⟩)
  have hWc : ContinuousOn W (Ici 0 ×ˢ Set.univ) := hUc.sub hVc
  have hWzero : ∀ y : Fin 3 → ℝ, W (0, y) = 0 := by
    intro y
    simp [W, U, V, hu.initial, hu'.initial]
  have hUspace {s : ℝ} (hs : 0 < s) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => U (s, y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hAt : ContDiffAt ℝ ∞ U (s, y) :=
      (hU (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    exact (hAt.comp y (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
      (by norm_num)
  have hVspace {s : ℝ} (hs : 0 < s) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => V (s, y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hAt : ContDiffAt ℝ ∞ V (s, y) :=
      (hV (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    exact (hAt.comp y (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
      (by norm_num)
  have hWspace {s : ℝ} (hs : 0 < s) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => W (s, y)) :=
    (hUspace hs).sub (hVspace hs)
  have hsecondW {s : ℝ} (hs : 0 < s) (i : Fin 3) (y : Fin 3 → ℝ) :
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
  have hWtime {s : ℝ} (hs : 0 < s) (y : Fin 3 → ℝ) :
      HasDerivAt (fun r => W (r, y)) (deriv (fun r => W (r, y)) s) s := by
    have hAt : ContDiffAt ℝ ∞ W (s, y) :=
      (hW (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
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
  have hEq {s : ℝ} (hs : 0 < s) (y : Fin 3 → ℝ) :
      deriv (fun r => W (r, y)) s =
        (∑ i, deriv (deriv (fun r => W (s, Function.update y i r))) (y i)) -
          q (s, y) * W (s, y) + c * W (s, y) +
            (f (s, torusProj y) - f' (s, torusProj y)) := by
    have hAtU : ContDiffAt ℝ ∞ U (s, y) :=
      (hU (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    have hAtV : ContDiffAt ℝ ∞ V (s, y) :=
      (hV (s, y) ⟨hs, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩)
    have hpathU : ContDiffAt ℝ ∞ (fun r => U (r, y)) s :=
      hAtU.comp s (contDiff_id.prodMk contDiff_const).contDiffAt
    have hpathV : ContDiffAt ℝ ∞ (fun r => V (r, y)) s :=
      hAtV.comp s (contDiff_id.prodMk contDiff_const).contDiffAt
    have heqU := hu.equation s hs y
    have heqV := hu'.equation s hs y
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
  have hforce_le : ∀ s ∈ Icc (0 : ℝ) T, ∀ y,
      f (s, torusProj y) - f' (s, torusProj y) ≤ B := by
    intro s hs y
    exact (le_abs_self _).trans (hforce s hs (torusProj y))
  have hupper : ∀ s ∈ Icc (0 : ℝ) T, ∀ y ∈ D,
      W (s, y) ≤ B * s * Real.exp (|c| * s) := by
    exact upper_comparison_bound (q := q)
      (g := fun p => f (p.1, torusProj p.2) - f' (p.1, torusProj p.2))
      hTpos hB hWc hWspace hWtime hperiod hWzero hEq hq
      hforce_le
  let Wn : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => -W p
  have hWnc : ContinuousOn Wn (Ici 0 ×ˢ Set.univ) := hWc.neg
  have hWnspace {s : ℝ} (hs : 0 < s) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => Wn (s, y)) := by
    simpa [Wn] using (hWspace hs).neg
  have hWntime {s : ℝ} (hs : 0 < s) (y : Fin 3 → ℝ) :
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
  have hEqn {s : ℝ} (hs : 0 < s) (y : Fin 3 → ℝ) :
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
  have hforce_neg : ∀ s ∈ Icc (0 : ℝ) T, ∀ y,
      f' (s, torusProj y) - f (s, torusProj y) ≤ B := by
    intro s hs y
    have hf := hforce s hs (torusProj y)
    rw [abs_sub_comm] at hf
    exact (le_abs_self _).trans hf
  have hupperN : ∀ s ∈ Icc (0 : ℝ) T, ∀ y ∈ D,
      Wn (s, y) ≤ B * s * Real.exp (|c| * s) := by
    exact upper_comparison_bound (q := q)
      (g := fun p => f' (p.1, torusProj p.2) - f (p.1, torusProj p.2))
      hTpos hB hWnc hWnspace hWntime hWnperiod hWnzero hEqn hq
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

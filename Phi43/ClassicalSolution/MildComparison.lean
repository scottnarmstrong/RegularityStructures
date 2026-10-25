/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MeasurableStability

/-!
# Finite-window comparison for the cubic bootstrap

The maximum-principle stability argument for classical solutions, localized to its actual compact time window. Unlike
the global stability interface it needs derivatives only on that window. It is used to identify the
abstract Φ⁴₃ solution with the classical solution of the regularised equation; no global continuation or solution regularity is assumed.
-/

public section

open MeasureTheory Set Function Filter
open scoped ContDiff Topology

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

theorem finiteWindow_upper_comparison_bound
    {W q g : (ℝ × (Fin 3 → ℝ)) → ℝ} {c B T : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B)
    (hWc : ContinuousOn W (Icc 0 T ×ˢ Set.univ))
    (hWspace : ∀ {s : ℝ}, s ∈ Ioc 0 T → ContDiff ℝ 2 (fun y => W (s, y)))
    (hWtime : ∀ {s : ℝ}, s ∈ Ioc 0 T → ∀ y,
      HasDerivAt (fun r => W (r, y)) (deriv (fun r => W (r, y)) s) s)
    (hperiod : ∀ (s : ℝ) (i : Fin 3) (y : Fin 3 → ℝ),
      W (s, Function.update y i (y i + 1)) = W (s, y))
    (hWzero : ∀ y, W (0, y) = 0)
    (hEq : ∀ {s : ℝ}, s ∈ Ioc 0 T → ∀ y,
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
  have hWcK : ContinuousOn W K := hWc.mono fun p hp => ⟨hp.1, mem_univ _⟩
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
        exact spatial_second_deriv_nonpos (hWspace ⟨hspos, hs.2⟩)
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
        convert (hEderiv.mul (hWtime ⟨hspos, hs.2⟩ y)).sub hB' |>.sub hε' using 1;
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
              rw [hEq ⟨hspos, hs.2⟩ y]
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


end RegularityStructures.Phi43

end

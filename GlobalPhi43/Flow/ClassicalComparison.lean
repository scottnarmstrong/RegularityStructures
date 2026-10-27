module

public import GlobalPhi43.MW20.LocalMaximum
public import GlobalPhi43.Flow.ClassicalBarrier
public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Finite-window scalar comparison on the torus. The paths need not have
any continuation or regularity beyond the stated closed time window. -/

public section

open Set Filter Topology RegularityStructures
open scoped ContDiff

namespace GlobalPhi43.Flow

/-- Comparison with a nonnegative scalar supersolution. The differential
inequality is only needed where the path is nonnegative. Derivatives at the
terminal face are included, and no derivatives at time zero are assumed. -/
theorem finiteWindow_scalar_comparison
    {W : SpaceTime → ℝ} {Q F : ℝ → ℝ} {k T : ℝ} (hT : 0 < T)
    (hW : ContinuousOn W (Icc 0 T ×ˢ univ))
    (hspace : ∀ t ∈ Ioc 0 T, ContDiff ℝ 2 (fun y => W (t, torusProj y)))
    (htime : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivAt (fun r => W (r, x)) (deriv (fun r => W (r, x)) t) t)
    (hQ : ContinuousOn Q (Icc 0 T))
    (hQd : ∀ t ∈ Ioc 0 T, HasDerivAt Q (k * Q t + F t) t)
    (hQpos : ∀ t ∈ Icc 0 T, 0 ≤ Q t)
    (hzero : ∀ x, W (0, x) ≤ Q 0)
    (hsub : ∀ t ∈ Ioc 0 T, ∀ y, 0 ≤ W (t, torusProj y) →
      deriv (fun r => W (r, torusProj y)) t ≤
        (∑ i : Fin 3, deriv (deriv (fun a =>
          W (t, torusProj (Function.update y i a)))) (y i)) +
          k * W (t, torusProj y) + F t) :
    ∀ t ∈ Icc 0 T, ∀ x, W (t, x) ≤ Q t := by
  let K : Set SpaceTime := Icc 0 T ×ˢ univ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKne : K.Nonempty := ⟨(0, 0), ⟨⟨le_rfl, hT.le⟩, mem_univ _⟩⟩
  have hbarrier (ε : ℝ) (hε : 0 < ε) :
      ∀ p ∈ K, Real.exp (-k * p.1) * (W p - Q p.1) - ε * (p.1 + 1) ≤ 0 := by
    let V : SpaceTime → ℝ := fun p =>
      Real.exp (-k * p.1) * (W p - Q p.1) - ε * (p.1 + 1)
    have hc : ContinuousOn V K := by
      apply ContinuousOn.sub
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn.mul
          (hW.sub (hQ.comp continuous_fst.continuousOn (fun _ hp => hp.1)))
      · exact (continuous_const.mul (continuous_fst.add continuous_const)).continuousOn
    intro p hp
    by_contra hnot
    obtain ⟨⟨t, x⟩, hm, hmax⟩ := hK.exists_isMaxOn hKne hc
    have hmax' := isMaxOn_iff.mp hmax
    have hpos : 0 < V (t, x) := (lt_of_not_ge hnot).trans_le (hmax' p hp)
    have ht : t ∈ Icc 0 T := hm.1
    have htpos : 0 < t := by
      by_contra hn
      have ht0 : t = 0 := le_antisymm (not_lt.mp hn) ht.1
      subst t
      have hz := hzero x
      dsimp [V] at hpos
      simp only [mul_zero, Real.exp_zero, one_mul, zero_add, mul_one] at hpos
      linarith
    have hdiff : 0 < W (t, x) - Q t := by
      have hh : 0 < Real.exp (-k * t) * (W (t, x) - Q t) := by
        dsimp [V] at hpos
        linarith [mul_nonneg hε.le (show 0 ≤ t + 1 by linarith [ht.1])]
      exact (mul_pos_iff.mp hh).resolve_right (fun h => (Real.exp_pos _).not_gt h.1) |>.2
    have hsp : ∀ z : Torus3, W (t, z) ≤ W (t, x) := by
      intro z
      have hh := hmax' (t, z) ⟨ht, mem_univ _⟩
      have hh' : Real.exp (-k * t) * W (t, z) ≤ Real.exp (-k * t) * W (t, x) := by
        dsimp [V] at hh
        linarith
      exact le_of_mul_le_mul_left hh' (Real.exp_pos _)
    let y := torusRep x
    have hy : torusProj y = x := by
      ext i
      exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (x i)
    have hlap : (∑ i : Fin 3, deriv (deriv (fun a =>
        W (t, torusProj (Function.update y i a)))) (y i)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      have hmline : IsLocalMax (fun a => W (t, torusProj (Function.update y i a))) (y i) := by
        apply Filter.Eventually.of_forall
        intro a
        simpa only [Function.update_eq_self, hy] using hsp (torusProj (Function.update y i a))
      have hcline : ContinuousAt (fun a => W (t, torusProj (Function.update y i a))) (y i) :=
        ((hspace t ⟨htpos, ht.2⟩).comp (contDiff_update 2 y i)).continuous.continuousAt
      exact PDE.deriv_deriv_nonpos_of_isLocalMax hmline hcline hmline.deriv_eq_zero
    have hineq := hsub t ⟨htpos, ht.2⟩ y (by rw [hy]; linarith [hQpos t ht])
    rw [hy] at hineq
    have he : HasDerivAt (fun r : ℝ => Real.exp (-k * r))
        (-k * Real.exp (-k * t)) t := by
      simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-k)).exp
    have hd : HasDerivAt (fun r => V (r, x))
        (Real.exp (-k * t) * (deriv (fun r => W (r, x)) t - (k * Q t + F t)) -
          k * Real.exp (-k * t) * (W (t, x) - Q t) - ε) t := by
      convert (he.mul ((htime t ⟨htpos, ht.2⟩ x).sub (hQd t ⟨htpos, ht.2⟩))).sub
        (((hasDerivAt_id t).add_const 1).const_mul ε) using 1
      · funext r
        dsimp [V]
      · dsimp
        ring
    have hneg : deriv (fun r => V (r, x)) t < 0 := by
      rw [hd.deriv]
      have hineq' : deriv (fun r => W (r, x)) t ≤ k * W (t, x) + F t := by
        linarith only [hineq, hlap]
      have hh := mul_le_mul_of_nonneg_left hineq' (Real.exp_nonneg (-k * t))
      nlinarith only [hh, hε]
    have hnonneg : 0 ≤ deriv (fun r => V (r, x)) t := by
      rw [← hd.deriv] at hd
      apply MW20.nonneg_deriv_of_max_left hd
      filter_upwards [Ioo_mem_nhdsLT htpos] with s hs
      exact hmax' (s, x) ⟨⟨hs.1.le, hs.2.le.trans ht.2⟩, mem_univ _⟩
    exact (not_lt_of_ge hnonneg) hneg
  intro t ht x
  have hh : ∀ ε : ℝ, 0 < ε → W (t, x) - Q t ≤
      ε * (Real.exp (k * t) * (t + 1)) := by
    intro ε hε
    have hb := hbarrier ε hε (t, x) ⟨ht, mem_univ _⟩
    have hc := mul_le_mul_of_nonneg_left (show
      Real.exp (-k * t) * (W (t, x) - Q t) ≤ ε * (t + 1) by linarith)
        (Real.exp_nonneg (k * t))
    have he : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
      rw [← Real.exp_add, show k * t + -k * t = 0 by ring, Real.exp_zero]
    calc
      W (t, x) - Q t = (Real.exp (k * t) * Real.exp (-k * t)) * (W (t, x) - Q t) := by rw [he, one_mul]
      _ ≤ ε * (Real.exp (k * t) * (t + 1)) := by nlinarith only [hc]
  have hz : W (t, x) - Q t ≤ 0 := by
    by_contra hn
    have hp : 0 < W (t, x) - Q t := lt_of_not_ge hn
    have hden : 0 < Real.exp (k * t) * (t + 1) := mul_pos (Real.exp_pos _) (by linarith [ht.1])
    have he := hh ((W (t, x) - Q t) / (2 * (Real.exp (k * t) * (t + 1))))
      (div_pos hp (mul_pos (by norm_num) hden))
    have hh' : (W (t, x) - Q t) / (2 * (Real.exp (k * t) * (t + 1))) *
        (Real.exp (k * t) * (t + 1)) = (W (t, x) - Q t) / 2 := by
      field_simp [ne_of_gt (show 0 < t + 1 by linarith [ht.1])]
    rw [hh'] at he
    linarith
  linarith

end GlobalPhi43.Flow

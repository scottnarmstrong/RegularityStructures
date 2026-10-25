/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatTime
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Order.Compact

/-!
# A maximum principle on the torus

Let `u : ℝ → C(T³, ℝ)` be a continuous path with `u(0) < L`, which is twice differentiable in
space and differentiable in time on `(0, T]`. If at every point where `u = L` the parabolic
operator is negative, `∂_t u - Δu < 0`, then `u < L` on `[0, T] × T³` (`lt_of_maxPrinciple`).

At the first time `t*` at which `u` reaches `L` the maximum of `u(t*)` is attained at some `x*`,
where `Δu ≤ 0` by the second derivative test in each coordinate direction, and `∂_t u ≥ 0` because
`u(·, x*) < L` before `t*`.
-/

public section

open Set Filter Topology

namespace RegularityStructures.PDE

/-- At a local maximum with zero derivative the second derivative is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {φ : ℝ → ℝ} {x₀ : ℝ} (hmax : IsLocalMax φ x₀)
    (hc : ContinuousAt φ x₀) (hd : deriv φ x₀ = 0) : deriv (deriv φ) x₀ ≤ 0 := by
  by_contra h
  push Not at h
  have hmin := isLocalMin_of_deriv_deriv_pos h hd hc
  have hconst : ∀ᶠ x in 𝓝 x₀, φ x = φ x₀ := by
    filter_upwards [hmax, hmin] with x h1 h2
    exact le_antisymm h1 h2
  have hd0 : deriv φ =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventually_nhds] with x hx
    have : φ =ᶠ[𝓝 x] fun _ => φ x₀ := hx
    rw [this.deriv_eq, deriv_const]
  rw [hd0.deriv_eq, deriv_const] at h
  exact lt_irrefl _ h

/-- If `ψ < ψ(a)` just to the left of `a`, the derivative at `a` is nonnegative. -/
theorem nonneg_of_hasDerivAt_of_lt_left {ψ : ℝ → ℝ} {a d : ℝ} (hd : HasDerivAt ψ d a)
    (h : ∀ᶠ s in 𝓝[<] a, ψ s < ψ a) : 0 ≤ d := by
  have hlim : Tendsto (slope ψ a) (𝓝[<] a) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
      (nhdsWithin_mono _ fun s hs => ne_of_lt (mem_Iio.1 hs))
  refine ge_of_tendsto hlim ?_
  filter_upwards [h, self_mem_nhdsWithin] with s hs hsa
  rw [slope_def_field]
  exact (div_pos_of_neg_of_neg (sub_neg.2 hs) (sub_neg.2 (mem_Iio.1 hsa))).le

/-- Partial derivatives along a coordinate line. -/
theorem hasDerivAt_update_of_hasTorusDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)} (hg : HasTorusDeriv g Dg) (y : Fin 3 → ℝ)
    (i : Fin 3) (r : ℝ) :
    HasDerivAt (fun r => g (torusProj (Function.update y i r)))
      (Dg (torusProj (Function.update y i r)) i) r := by
  have h := (hg (Function.update y i r)).comp_hasDerivAt r (hasDerivAt_update y i r)
  simpa [Function.comp_def, ofPartials_single] using h

/-- **Maximum principle.** -/
theorem lt_of_maxPrinciple {u : ℝ → C(Torus3, ℝ)} {w : ℝ → C(Torus3, Fin 3 → ℝ)}
    {w2 : ℝ → C(Torus3, Fin 3 → Fin 3 → ℝ)} {D : ℝ → Torus3 → ℝ} {T L : ℝ}
    (hu : Continuous u) (h0 : ∀ x, u 0 x < L)
    (hdw : ∀ t ∈ Ioc 0 T, HasTorusDeriv (u t) (w t))
    (hdw2 : ∀ t ∈ Ioc 0 T, HasTorusDeriv (E := Fin 3 → ℝ) (w t) (w2 t))
    (hdt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => u s x) (D t x) t)
    (hsign : ∀ t ∈ Ioc 0 T, ∀ x, u t x = L → D t x - torusLap (w2 t) x < 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x < L := by
  by_contra hcon
  push Not at hcon
  have hU : Continuous fun p : ℝ × Torus3 => u p.1 p.2 :=
    continuous_eval.comp ((hu.comp continuous_fst).prodMk continuous_snd)
  -- the set of times at which `u` reaches `L`
  set K : Set (ℝ × Torus3) := (Icc 0 T ×ˢ univ) ∩ {p | L ≤ u p.1 p.2} with hKdef
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_univ).inter_right (isClosed_le continuous_const hU)
  obtain ⟨t₁, ht₁, x₁, hx₁⟩ := hcon
  obtain ⟨ts, ⟨⟨ts', xs⟩, hpK, hts⟩, hleast⟩ :=
    (hK.image continuous_fst).exists_isLeast ⟨t₁, ⟨(t₁, x₁), ⟨⟨ht₁, mem_univ _⟩, hx₁⟩, rfl⟩⟩
  simp only at hts
  subst hts
  have htsI : ts' ∈ Icc 0 T := hpK.1.1
  have hLxs : L ≤ u ts' xs := hpK.2
  -- before `ts'` the solution stays below `L`
  have hbefore : ∀ s ∈ Ico 0 ts', ∀ x, u s x < L := by
    intro s hs x
    by_contra hsx
    push Not at hsx
    have : ts' ≤ s := hleast ⟨(s, x), ⟨⟨⟨hs.1, hs.2.le.trans htsI.2⟩, mem_univ _⟩, hsx⟩, rfl⟩
    exact absurd hs.2 (not_lt.2 this)
  have hts0 : 0 < ts' := by
    rcases htsI.1.eq_or_lt with h | h
    · rw [← h] at hLxs
      exact absurd (h0 xs) (not_lt.2 hLxs)
    · exact h
  have htsIoc : ts' ∈ Ioc 0 T := ⟨hts0, htsI.2⟩
  have hev : ∀ᶠ s in 𝓝[<] ts', s ∈ Ico 0 ts' := by
    filter_upwards [Ioo_mem_nhdsLT hts0] with s hs
    exact ⟨hs.1.le, hs.2⟩
  -- at time `ts'` the solution is at most `L`
  have hle : ∀ x, u ts' x ≤ L := by
    intro x
    have hlim : Tendsto (fun s => u s x) (𝓝[<] ts') (𝓝 (u ts' x)) :=
      ((continuous_eval_const x).comp hu).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with s hs
    exact (hbefore s hs x).le
  have heq : u ts' xs = L := le_antisymm (hle xs) hLxs
  -- the Laplacian is nonpositive at the maximum point
  obtain ⟨y, rfl⟩ := torusProj_surjective xs
  have hlap : torusLap (w2 ts') (torusProj y) ≤ 0 := by
    rw [torusLap_apply]
    refine Finset.sum_nonpos fun i _ => ?_
    set φ : ℝ → ℝ := fun r => u ts' (torusProj (Function.update y i r)) with hφ
    have hφd : ∀ r, HasDerivAt φ (w ts' (torusProj (Function.update y i r)) i) r :=
      hasDerivAt_update_of_hasTorusDeriv (hdw ts' htsIoc) y i
    have hφ' : deriv φ = fun r => w ts' (torusProj (Function.update y i r)) i :=
      funext fun r => (hφd r).deriv
    have hφ'd : HasDerivAt (deriv φ) (w2 ts' (torusProj y) i i) (y i) := by
      rw [hφ']
      have := hasDerivAt_update_of_hasTorusDeriv (E := Fin 3 → ℝ) (hdw2 ts' htsIoc) y i (y i)
      simp only [Function.update_eq_self] at this
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt
        (y i) this
    have hmax : IsLocalMax φ (y i) := by
      refine Filter.Eventually.of_forall fun r => ?_
      simp only [hφ, Function.update_eq_self]
      rw [heq]
      exact hle _
    have hd0 : deriv φ (y i) = 0 := hmax.deriv_eq_zero
    have := deriv_deriv_nonpos_of_isLocalMax hmax (hφd (y i)).continuousAt hd0
    rwa [hφ'd.deriv] at this
  -- the time derivative is nonnegative
  have htime : 0 ≤ D ts' (torusProj y) := by
    refine nonneg_of_hasDerivAt_of_lt_left (hdt ts' htsIoc (torusProj y)) ?_
    filter_upwards [hev] with s hs
    rw [heq]
    exact hbefore s hs _
  have := hsign ts' htsIoc (torusProj y) heq
  linarith

end RegularityStructures.PDE

end

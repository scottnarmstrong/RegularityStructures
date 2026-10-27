module

public import RegularityStructures.PDE.MaxPrinciple
public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# Local parabolic maxima, including the terminal time face

Calculus estimates for MW20 Lemma 2.7, valid at the terminal time face
as well as in the time interior. No cubic bound or barrier existence
is assumed.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set Filter Topology

/-- The coordinate expression for `∂t - Δ` on the source space-time. -/
@[expose] noncomputable def sourceHeat (w : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  deriv (fun t => w (t, z.2)) z.1 -
    ∑ i : Fin 3, deriv (deriv (fun x => w (z.1, Function.update z.2 i x))) (z.2 i)

/-- A maximum relative to the past gives a nonnegative time derivative.
The inequalities may be non-strict, and the evaluation point may be on the top face. -/
theorem nonneg_deriv_of_max_left {ψ : ℝ → ℝ} {a d : ℝ} (hd : HasDerivAt ψ d a)
    (h : ∀ᶠ s in 𝓝[<] a, ψ s ≤ ψ a) : 0 ≤ d := by
  have hlim : Tendsto (slope ψ a) (𝓝[<] a) (𝓝 d) :=
    hd.tendsto_slope.mono_left (nhdsWithin_mono _ fun s hs => ne_of_lt (mem_Iio.1 hs))
  refine ge_of_tendsto hlim ?_
  filter_upwards [h, self_mem_nhdsWithin] with s hs hsa
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.2 hs) (sub_neg.2 (mem_Iio.1 hsa)).le

/-- At a maximum in a closed cylinder, interior in space and strictly after
its initial time, the heat operator is nonnegative. No inset is needed from
the terminal time. -/
theorem sourceHeat_nonneg_at_max {w : ParabolicSpace → ℝ}
    {s₀ a b t T : ℝ} {x : Fin 3 → ℝ}
    (hw : ContinuousOn w (Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b)))
    (ht : s₀ < t) (htT : t ≤ T) (hx : ∀ i, a < x i ∧ x i < b)
    (hmax : ∀ z ∈ Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b), w z ≤ w (t, x))
    (hdt : DifferentiableAt ℝ (fun s => w (s, x)) t) : 0 ≤ sourceHeat w (t, x) := by
  have htime : 0 ≤ deriv (fun s => w (s, x)) t := by
    apply nonneg_deriv_of_max_left hdt.hasDerivAt
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact hmax (s, x) ⟨⟨hs.1.le, fun i => (hx i).1.le⟩,
      ⟨hs.2.le.trans htT, fun i => (hx i).2.le⟩⟩
  have hspace (i : Fin 3) :
      deriv (deriv (fun y => w (t, Function.update x i y))) (x i) ≤ 0 := by
    have hline_mem (y : ℝ) (hy : y ∈ Ioo a b) : (t, Function.update x i y) ∈
        Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b) := by
      refine ⟨⟨ht.le, ?_⟩, ⟨htT, ?_⟩⟩
      · intro j
        by_cases hj : j = i
        · subst j; simpa using hy.1.le
        · simpa [Function.update_of_ne hj] using (hx j).1.le
      · intro j
        by_cases hj : j = i
        · subst j; simpa using hy.2.le
        · simpa [Function.update_of_ne hj] using (hx j).2.le
    have hlocal : IsLocalMax (fun y => w (t, Function.update x i y)) (x i) := by
      filter_upwards [Ioo_mem_nhds (hx i).1 (hx i).2] with y hy
      simpa using hmax _ (hline_mem y hy)
    have hpath : Continuous (fun y : ℝ => (t, Function.update x i y)) := by fun_prop
    have hc : ContinuousAt (fun y => w (t, Function.update x i y)) (x i) :=
      (hw.comp hpath.continuousOn hline_mem).continuousAt (Ioo_mem_nhds (hx i).1 (hx i).2)
    exact PDE.deriv_deriv_nonpos_of_isLocalMax hlocal hc hlocal.deriv_eq_zero
  exact sub_nonneg.mpr ((Finset.sum_nonpos fun i _ => hspace i).trans htime)

end GlobalPhi43.MW20

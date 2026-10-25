/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Duhamel
public import Mathlib.Topology.ContinuousMap.Ordered
import RegularityStructures.PDE.Gronwall
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Mild solutions of semilinear heat equations on `T³`

For a continuous nonlinearity `G : ℝ × T³ × E → E` and `u₀ ∈ C(T³, E)`, a path
`u : ℝ → C(T³, E)` is a mild solution of `∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]` if
`u(t) = P_t u₀ + ∫₀ᵗ P_{t-s} G(s, ·, u(s)) ds` for `t ∈ [0, T]`.

## Main results

* `IsMildSolution.eqOn`: two continuous mild solutions agree on `[0, T]` when `G` is Lipschitz in
  `u` (Grönwall);
* `exists_isMildSolution`: a continuous mild solution exists on `[0, T]` when `G` is globally
  Lipschitz in `u` for `t ∈ [0, T]` (Banach's fixed point theorem in the weighted norm
  `sup_t e^{-λt} ‖u(t)‖`, which makes the Picard map a contraction on the whole interval).
-/

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Nemytskii operator `v ↦ G(s, ·, v(·))` on `C(T³, E)`. -/
def nemytskii (G : C(ℝ × Torus3 × E, E)) (s : ℝ) (v : C(Torus3, E)) : C(Torus3, E) :=
  ⟨fun x => G (s, x, v x), by fun_prop⟩

/-- `u` is a mild solution of `∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]`. -/
def IsMildSolution (G : C(ℝ × Torus3 × E, E)) (u₀ : C(Torus3, E)) (T : ℝ)
    (u : ℝ → C(Torus3, E)) : Prop :=
  ∀ t ∈ Set.Icc 0 T, u t = heatOp t u₀ + duhamel (fun s => nemytskii G s (u s)) t

end RegularityStructures.PDE

end

public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Nemytskii

omit [NormedSpace ℝ E]

@[simp]
theorem nemytskii_apply (G : C(ℝ × Torus3 × E, E)) (s : ℝ) (v : C(Torus3, E)) (x : Torus3) :
    nemytskii G s v x = G (s, x, v x) := rfl

/-- The Nemytskii operator is jointly continuous in `(s, v)`. -/
theorem continuous_nemytskii (G : C(ℝ × Torus3 × E, E)) :
    Continuous fun p : ℝ × C(Torus3, E) => nemytskii G p.1 p.2 := by
  let H : C((ℝ × C(Torus3, E)) × Torus3, E) :=
    ⟨fun q => G (q.1.1, q.2, q.1.2 q.2), by fun_prop⟩
  exact H.curry.continuous

theorem continuous_nemytskii_comp (G : C(ℝ × Torus3 × E, E)) {u : ℝ → C(Torus3, E)}
    (hu : Continuous u) : Continuous fun s => nemytskii G s (u s) :=
  (continuous_nemytskii G).comp (continuous_id.prodMk hu)

theorem norm_nemytskii_sub_le (G : C(ℝ × Torus3 × E, E)) {L : ℝ≥0} {s : ℝ}
    (hL : ∀ x, LipschitzWith L fun v => G (s, x, v)) (v w : C(Torus3, E)) :
    ‖nemytskii G s v - nemytskii G s w‖ ≤ L * ‖v - w‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [ContinuousMap.sub_apply, nemytskii_apply, nemytskii_apply, ← dist_eq_norm]
  calc dist (G (s, x, v x)) (G (s, x, w x)) ≤ L * dist (v x) (w x) := (hL x).dist_le_mul _ _
    _ ≤ L * ‖v - w‖ := by
        gcongr
        rw [dist_eq_norm, ← ContinuousMap.sub_apply]
        exact ContinuousMap.norm_coe_le_norm _ x

end Nemytskii

/-- **Uniqueness of mild solutions** for nonlinearities that are Lipschitz in `u`. -/
theorem IsMildSolution.eqOn {G : C(ℝ × Torus3 × E, E)} {u₀ : C(Torus3, E)} {T : ℝ} {L : ℝ≥0}
    (hL : ∀ s ∈ Icc 0 T, ∀ x, LipschitzWith L fun v => G (s, x, v))
    {u v : ℝ → C(Torus3, E)} (hu : Continuous u) (hv : Continuous v)
    (hmu : IsMildSolution G u₀ T u) (hmv : IsMildSolution G u₀ T v) :
    ∀ t ∈ Icc 0 T, u t = v t := by
  have hφ : Continuous fun t => ‖u t - v t‖ := (hu.sub hv).norm
  have key : ∀ t ∈ Icc 0 T, ‖u t - v t‖ ≤ L * ∫ s in (0 : ℝ)..t, ‖u s - v s‖ := by
    intro t ht
    have hNu := continuous_nemytskii_comp G hu
    have hNv := continuous_nemytskii_comp G hv
    rw [hmu t ht, hmv t ht, add_sub_add_left_eq_sub, ← duhamel_sub hNu hNv]
    refine (norm_duhamel_le (hNu.sub hNv) ht.1).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ht.1 ((hNu.sub hNv).norm.intervalIntegrable 0 t)
      ((continuous_const.mul hφ).intervalIntegrable 0 t) fun s hs => ?_
    exact norm_nemytskii_sub_le G (hL s ⟨hs.1, hs.2.trans ht.2⟩) _ _
  intro t ht
  have := le_zero_of_le_integral hφ L.2 key t ht
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-! ### Existence by a weighted contraction -/

section Existence

variable (G : C(ℝ × Torus3 × E, E)) (u₀ : C(Torus3, E)) {T : ℝ} (hT : 0 ≤ T) (lam : ℝ)

/-- The extension to `ℝ` of a path on `[0, T]`, multiplied by the weight `e^{λ s}`. -/
noncomputable def weightedExtend (w : C(Icc (0 : ℝ) T, C(Torus3, E))) (s : ℝ) : C(Torus3, E) :=
  exp (lam * s) • ContinuousMap.IccExtend hT w s

theorem continuous_weightedExtend (w : C(Icc (0 : ℝ) T, C(Torus3, E))) :
    Continuous (weightedExtend hT lam w) :=
  ((continuous_const.mul continuous_id).rexp).smul (ContinuousMap.IccExtend hT w).continuous

/-- The weighted Picard map `w ↦ e^{-λt} (P_t u₀ + ∫₀ᵗ P_{t-s} G(s, ·, e^{λs} w(s)) ds)`. -/
noncomputable def weightedPicard (w : C(Icc (0 : ℝ) T, C(Torus3, E))) : C(Icc (0 : ℝ) T, C(Torus3, E)) where
  toFun t := exp (-(lam * t)) • (heatOp t u₀ +
    duhamel (fun s => nemytskii G s (weightedExtend hT lam w s)) t)
  continuous_toFun := by
    refine Continuous.comp (g := fun t : ℝ => exp (-(lam * t)) • (heatOp t u₀ +
      duhamel (fun s => nemytskii G s (weightedExtend hT lam w s)) t)) ?_ continuous_subtype_val
    exact ((continuous_const.mul continuous_id).neg.rexp).smul
      ((continuous_heatOp_left u₀).add (continuous_duhamel
        (continuous_nemytskii_comp G (continuous_weightedExtend hT lam w))))

theorem integral_exp_mul_le {lam t : ℝ} (hlam : 0 < lam) :
    ∫ s in (0 : ℝ)..t, exp (lam * s) ≤ exp (lam * t) / lam := by
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s => exp (lam * s) / lam) (exp (lam * s)) s := by
    intro s _
    have := ((hasDerivAt_id s).const_mul lam).exp.div_const lam
    simpa [mul_comm, hlam.ne'] using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul continuous_id).rexp.intervalIntegrable 0 t)]
  have : 0 ≤ exp (lam * 0) / lam := div_nonneg (exp_pos _).le hlam.le
  linarith

theorem dist_weightedPicard_le {L : ℝ≥0} (hL : ∀ s ∈ Icc 0 T, ∀ x, LipschitzWith L fun v => G (s, x, v))
    (hlam : 0 < lam) (w w' : C(Icc (0 : ℝ) T, C(Torus3, E))) :
    dist (weightedPicard G u₀ hT lam w) (weightedPicard G u₀ hT lam w') ≤
      (L / lam) * dist w w' := by
  have hD : 0 ≤ (L / lam) * dist w w' := mul_nonneg (div_nonneg L.2 hlam.le) dist_nonneg
  refine (ContinuousMap.dist_le hD).2 fun t => ?_
  have hc := continuous_nemytskii_comp G (continuous_weightedExtend hT lam w)
  have hc' := continuous_nemytskii_comp G (continuous_weightedExtend hT lam w')
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  simp only [weightedPicard, ContinuousMap.coe_mk, dist_eq_norm]
  rw [← smul_sub, add_sub_add_left_eq_sub, ← duhamel_sub hc hc', norm_smul,
    Real.norm_of_nonneg (exp_pos _).le]
  have hpt : ∀ s ∈ Icc (0 : ℝ) t, ‖nemytskii G s (weightedExtend hT lam w s) -
      nemytskii G s (weightedExtend hT lam w' s)‖ ≤ L * dist w w' * exp (lam * s) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans t.2.2⟩
    refine (norm_nemytskii_sub_le G (hL s hsT) _ _).trans ?_
    rw [weightedExtend, weightedExtend, ← smul_sub, norm_smul, Real.norm_of_nonneg (exp_pos _).le,
      ← dist_eq_norm, mul_comm (exp _), ← mul_assoc]
    gcongr
    rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend]
    exact ContinuousMap.dist_apply_le_dist _
  calc exp (-(lam * t)) * ‖duhamel (fun s => nemytskii G s (weightedExtend hT lam w s) -
        nemytskii G s (weightedExtend hT lam w' s)) t‖
      ≤ exp (-(lam * t)) * ∫ s in (0 : ℝ)..t, L * dist w w' * exp (lam * s) := by
        gcongr
        refine (norm_duhamel_le (hc.sub hc') ht0).trans ?_
        exact intervalIntegral.integral_mono_on ht0 ((hc.sub hc').norm.intervalIntegrable 0 t)
          ((continuous_const.mul (continuous_const.mul continuous_id).rexp).intervalIntegrable
            0 t) hpt
    _ = L * dist w w' * (exp (-(lam * t)) * ∫ s in (0 : ℝ)..t, exp (lam * s)) := by
        rw [intervalIntegral.integral_const_mul]
        ring
    _ ≤ L * dist w w' * (exp (-(lam * t)) * (exp (lam * t) / lam)) := by
        gcongr
        exact integral_exp_mul_le hlam
    _ = (L / lam) * dist w w' := by
        rw [mul_div_assoc', ← exp_add, neg_add_cancel, exp_zero]
        ring

end Existence

/-- **Existence of mild solutions** for nonlinearities that are globally Lipschitz in `u` on
`[0, T]`. -/
theorem exists_isMildSolution [CompleteSpace E] (G : C(ℝ × Torus3 × E, E)) (u₀ : C(Torus3, E)) {T : ℝ}
    (hT : 0 ≤ T) {L : ℝ≥0} (hL : ∀ s ∈ Icc 0 T, ∀ x, LipschitzWith L fun v => G (s, x, v)) :
    ∃ u : ℝ → C(Torus3, E), Continuous u ∧ IsMildSolution G u₀ T u := by
  set lam : ℝ := 2 * L + 1 with hlam_def
  have hlam : 0 < lam := by positivity
  have hK : (L : ℝ) / lam ≤ 1 / 2 := by
    rw [div_le_iff₀ hlam]
    linarith [L.2]
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (weightedPicard G u₀ hT lam) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    refine (dist_weightedPicard_le G u₀ hT lam hL hlam w w').trans ?_
    have : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right hK dist_nonneg
  set w := ContractingWith.fixedPoint _ hcontr
  have hw : weightedPicard G u₀ hT lam w = w := ContractingWith.fixedPoint_isFixedPt hcontr
  refine ⟨weightedExtend hT lam w, continuous_weightedExtend hT lam w, fun t ht => ?_⟩
  have hwt := congrArg (fun w' => w' ⟨t, ht⟩) hw
  simp only [weightedPicard, ContinuousMap.coe_mk] at hwt
  rw [weightedExtend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hT _ ht, ← hwt,
    smul_smul, ← exp_add, add_neg_cancel, exp_zero, one_smul]

end RegularityStructures.PDE

end

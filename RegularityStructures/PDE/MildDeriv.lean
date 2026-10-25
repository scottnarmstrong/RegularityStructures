/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Mild
import RegularityStructures.PDE.Gronwall
import RegularityStructures.PDE.UniformTaylor
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.Interval.Set.Pi

/-!
# Mild solutions are differentiable in space

Let `G : ℝ × T³ × E → E` have a continuous derivative `DG` in `(x, u)` (on the periodic lift), let
`u₀ ∈ C(T³, E)` have a continuous derivative `Du₀`, and let `u` be a continuous mild solution of
`∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]`. Then every `u(t)`, `t ∈ [0, T]`, is
differentiable on the lift, and its derivative is a continuous path `w` in `C(T³, ℝ³ →L E)`.

The candidate `w` is the mild solution of the linearised equation
`∂_t w = Δw + D_x G(t, x, u) + D_u G(t, x, u) ∘ w`, `w(0) = Du₀`. For a fixed increment `k ∈ ℝ³`,
the error `e_k(t) = u(t, · + k) - u(t) - w(t) k` solves a linear mild equation whose forcing is a
first-order Taylor remainder of `G` and of `u₀`. A uniform Taylor estimate on a compact set and
Grönwall's inequality give `‖e_k(t)‖ = o(|k|)` uniformly in `t ∈ [0, T]`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonlinearity of the linearised equation along a path `u`, acting on partial derivatives:
`(s, x, ω) ↦ (D_x G(s, x, u(s, x)) eᵢ + D_u G(s, x, u(s, x)) ωᵢ)ᵢ`. -/
def linearisedNonlin (DG : C(ℝ × Torus3 × E, ((Fin 3 → ℝ) × E) →L[ℝ] E))
    (u : ℝ → C(Torus3, E)) (hu : Continuous u) :
    C(ℝ × Torus3 × (Fin 3 → E), Fin 3 → E) where
  toFun p i := DG (p.1, p.2.1, u p.1 p.2.1) (Pi.single i 1, p.2.2 i)
  continuous_toFun := by
    have hU : Continuous fun p : ℝ × Torus3 × (Fin 3 → E) => u p.1 p.2.1 :=
      continuous_eval.comp ((hu.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
    have hD : Continuous fun p : ℝ × Torus3 × (Fin 3 → E) =>
        DG (p.1, p.2.1, u p.1 p.2.1) :=
      DG.continuous.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk hU))
    exact continuous_pi fun i => hD.clm_apply (continuous_const.prodMk
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))

end RegularityStructures.PDE

end

public section

open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linearisedNonlin_apply (DG : C(ℝ × Torus3 × E, ((Fin 3 → ℝ) × E) →L[ℝ] E))
    (u : ℝ → C(Torus3, E)) (hu : Continuous u) (s : ℝ) (x : Torus3)
    (ω : Fin 3 → E) (k : Fin 3 → ℝ) :
    ofPartials (linearisedNonlin DG u hu (s, x, ω)) k = DG (s, x, u s x) (k, ofPartials ω k) := by
  rw [ofPartials_apply, ofPartials_apply]
  simp only [linearisedNonlin, ContinuousMap.coe_mk, ← map_smul, ← map_sum]
  congr 1
  ext j
  · rw [Prod.fst_sum, Finset.sum_apply]
    simp [Pi.single_apply]
  · rw [Prod.snd_sum]
    simp

theorem norm_linearisedNonlin_sub_le (DG : C(ℝ × Torus3 × E, ((Fin 3 → ℝ) × E) →L[ℝ] E))
    (u : ℝ → C(Torus3, E)) (hu : Continuous u) (s : ℝ) (x : Torus3)
    (ω ω' : Fin 3 → E) :
    ‖linearisedNonlin DG u hu (s, x, ω) - linearisedNonlin DG u hu (s, x, ω')‖ ≤
      ‖DG (s, x, u s x)‖ * ‖ω - ω'‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [linearisedNonlin, ContinuousMap.coe_mk, Pi.sub_apply]
  rw [← map_sub, Prod.mk_sub_mk, sub_self]
  refine ((DG _).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), ← Pi.sub_apply]
  exact norm_le_pi_norm (ω - ω') i

/-- A continuous path is bounded on `[0, T]`. -/
theorem exists_norm_le_of_continuous {X : Type*} [SeminormedAddCommGroup X] {f : ℝ → X}
    (hf : Continuous f) (T : ℝ) : ∃ M, ∀ s ∈ Icc 0 T, ‖f s‖ ≤ M :=
  isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn

theorem torusRep_mem_Icc (x : Torus3) : torusRep x ∈ Icc (0 : Fin 3 → ℝ) 1 := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact (AddCircle.equivIco (1 : ℝ) 0 (x i)).2.1
  · have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2.2
    simp only [zero_add] at this
    exact this.le

variable [CompleteSpace E]

/-- The error `u(t, · + k) - u(t) - w(t) k` of a linearisation, written in mild form. -/
theorem shift_sub_sub_evalAt_eq {G : C(ℝ × Torus3 × E, E)}
    {Gl : C(ℝ × Torus3 × (Fin 3 → E), Fin 3 → E)}
    {u₀ : C(Torus3, E)} {Du₀ : C(Torus3, Fin 3 → E)} {T : ℝ}
    {u : ℝ → C(Torus3, E)} {w : ℝ → C(Torus3, Fin 3 → E)}
    (hu : Continuous u) (hw : Continuous w) (hmu : IsMildSolution G u₀ T u)
    (hmw : IsMildSolution (E := Fin 3 → E) Gl Du₀ T w) (k : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    torusShift (torusProj k) (u t) - u t - evalAt (E := E) k (w t) =
      heatOp t (torusShift (torusProj k) u₀ - u₀ - evalAt (E := E) k Du₀) +
        duhamel (fun s => torusShift (torusProj k) (nemytskii G s (u s)) - nemytskii G s (u s) -
          evalAt (E := E) k (nemytskii (E := Fin 3 → E) Gl s (w s))) t := by
  have hN := continuous_nemytskii_comp G hu
  have hNl := continuous_nemytskii_comp (E := Fin 3 → E) Gl hw
  have hτN : Continuous fun s => torusShift (torusProj k) (nemytskii G s (u s)) :=
    (torusShift (torusProj k)).continuous.comp hN
  have hevNl : Continuous fun s => evalAt (E := E) k (nemytskii (E := Fin 3 → E) Gl s (w s)) :=
    (evalAt (E := E) k).continuous.comp hNl
  have hA : Continuous fun s => torusShift (torusProj k) (nemytskii G s (u s)) -
      nemytskii G s (u s) := hτN.sub hN
  rw [duhamel_sub (h₁ := fun s => torusShift (torusProj k) (nemytskii G s (u s)) -
      nemytskii G s (u s)) hA hevNl,
    duhamel_sub (h₁ := fun s => torusShift (torusProj k) (nemytskii G s (u s))) hτN hN,
    duhamel_torusShift hN, heatOp_sub, heatOp_sub, heatOp_torusShift, hmu t ht, hmw t ht]
  have h1 : evalAt (E := E) k (heatOp t Du₀) = heatOp t (evalAt (E := E) k Du₀) :=
    (heatOp_compLeftContinuous t ((ContinuousLinearMap.apply ℝ E k).comp ofPartials) Du₀).symm
  have h2 : evalAt (E := E) k (duhamel (fun s => nemytskii (E := Fin 3 → E) Gl s (w s)) t) =
      duhamel (fun s => evalAt (E := E) k (nemytskii (E := Fin 3 → E) Gl s (w s))) t :=
    (duhamel_compLeftContinuous hNl ((ContinuousLinearMap.apply ℝ E k).comp ofPartials) t).symm
  rw [map_add, map_add, h1, h2]
  abel

omit [CompleteSpace E] in
/-- Pointwise bound on the forcing of the error equation. -/
theorem norm_shift_nemytskii_sub_le {G : C(ℝ × Torus3 × E, E)}
    {DG : C(ℝ × Torus3 × E, ((Fin 3 → ℝ) × E) →L[ℝ] E)} {u : ℝ → C(Torus3, E)}
    (hu : Continuous u) {w : ℝ → C(Torus3, Fin 3 → E)} {s ε₁ δ₁ M W : ℝ}
    {k : Fin 3 → ℝ} (hε₁ : 0 ≤ ε₁) (hk : ‖k‖ < δ₁)
    (hTG : ∀ x, ∀ h : (Fin 3 → ℝ) × E, ‖h‖ < δ₁ →
      ‖G (s, torusProj (torusRep x + h.1), u s x + h.2) - G (s, x, u s x) -
        DG (s, x, u s x) h‖ ≤ ε₁ * ‖h‖)
    (hM : ∀ x, ‖DG (s, x, u s x)‖ ≤ M) (hW : ∀ x, ‖ofPartials (w s x)‖ ≤ W)
    (hΔ : ∀ x, ‖u s (x + torusProj k) - u s x‖ < δ₁) :
    ‖torusShift (torusProj k) (nemytskii G s (u s)) - nemytskii G s (u s) -
        evalAt (E := E) k (nemytskii (E := Fin 3 → E) (linearisedNonlin DG u hu) s (w s))‖ ≤
      ε₁ * (1 + W) * ‖k‖ + (ε₁ + M) *
        ‖torusShift (torusProj k) (u s) - u s - evalAt (E := E) k (w s)‖ := by
  set e := torusShift (torusProj k) (u s) - u s - evalAt (E := E) k (w s) with he
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  set Δ := u s (x + torusProj k) - u s x with hΔdef
  have hex : e x = Δ - ofPartials (w s x) k := by simp [he, hΔdef]
  have hΔle : ‖Δ‖ ≤ ‖e‖ + W * ‖k‖ := by
    have : Δ = e x + ofPartials (w s x) k := by rw [hex]; abel
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add (e.norm_coe_le_norm x) ?_)
    exact ((ofPartials (w s x)).le_opNorm k).trans
      (mul_le_mul_of_nonneg_right (hW x) (norm_nonneg _))
  have hh : ‖((k, Δ) : (Fin 3 → ℝ) × E)‖ < δ₁ := by
    rw [Prod.norm_def]
    exact max_lt hk (hΔ x)
  have hT := hTG x (k, Δ) hh
  have hx1 : torusProj (torusRep x + k) = x + torusProj k := by
    rw [torusProj_add, torusProj_torusRep]
  have hx2 : u s x + Δ = u s (x + torusProj k) := by rw [hΔdef]; abel
  simp only [hx1, hx2] at hT
  have hlin : ofPartials (linearisedNonlin DG u hu (s, x, w s x)) k =
      DG (s, x, u s x) (k, ofPartials (w s x) k) :=
    linearisedNonlin_apply DG u hu s x (w s x) k
  have hsplit : (torusShift (torusProj k) (nemytskii G s (u s)) - nemytskii G s (u s) -
      evalAt (E := E) k (nemytskii (E := Fin 3 → E) (linearisedNonlin DG u hu) s (w s))) x =
      (G (s, x + torusProj k, u s (x + torusProj k)) - G (s, x, u s x) -
        DG (s, x, u s x) (k, Δ)) + DG (s, x, u s x) (0, e x) := by
    simp only [ContinuousMap.sub_apply, torusShift_apply, nemytskii_apply, evalAt_apply_apply,
      hlin, hex]
    have : DG (s, x, u s x) (k, Δ) = DG (s, x, u s x) (k, ofPartials (w s x) k) +
        DG (s, x, u s x) (0, Δ - ofPartials (w s x) k) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    rw [this]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖DG (s, x, u s x) (0, e x)‖ ≤ M * ‖e‖ := by
    refine ((DG (s, x, u s x)).le_opNorm _).trans ?_
    rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact mul_le_mul (hM x) (e.norm_coe_le_norm x) (norm_nonneg _) hM0
  have h1 : ε₁ * ‖((k, Δ) : (Fin 3 → ℝ) × E)‖ ≤ ε₁ * (‖k‖ + (‖e‖ + W * ‖k‖)) := by
    gcongr
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · linarith [norm_nonneg e, norm_nonneg k, hΔle, norm_nonneg Δ]
    · linarith [norm_nonneg k]
  calc _ ≤ ε₁ * ‖((k, Δ) : (Fin 3 → ℝ) × E)‖ + M * ‖e‖ := add_le_add hT h2
    _ ≤ ε₁ * (‖k‖ + (‖e‖ + W * ‖k‖)) + M * ‖e‖ := by linarith
    _ = ε₁ * (1 + W) * ‖k‖ + (ε₁ + M) * ‖e‖ := by ring

/-- **Mild solutions are differentiable in space.** If `G` has a continuous derivative `DG` in
`(x, u)`, `u₀` has a continuous derivative `Du₀` and `u` is a continuous mild solution on `[0, T]`,
then every `u(t)`, `t ∈ [0, T]`, has derivative `w(t)`, where `w` is the continuous mild solution of
the linearised equation with initial datum `Du₀`. -/
theorem exists_hasTorusDeriv_of_isMildSolution [FiniteDimensional ℝ E]
    {G : C(ℝ × Torus3 × E, E)} {DG : C(ℝ × Torus3 × E, ((Fin 3 → ℝ) × E) →L[ℝ] E)}
    (hDG : ∀ s y v, HasFDerivAt (fun q : (Fin 3 → ℝ) × E => G (s, torusProj q.1, q.2))
      (DG (s, torusProj y, v)) (y, v))
    {u₀ : C(Torus3, E)} {Du₀ : C(Torus3, Fin 3 → E)} (hu₀ : HasTorusDeriv u₀ Du₀)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → C(Torus3, E)} (hu : Continuous u)
    (hmild : IsMildSolution G u₀ T u) :
    ∃ w : ℝ → C(Torus3, Fin 3 → E), Continuous w ∧
      IsMildSolution (E := Fin 3 → E) (linearisedNonlin DG u hu) Du₀ T w ∧
      ∀ t ∈ Icc 0 T, HasTorusDeriv (u t) (w t) := by
  have hU : Continuous fun p : ℝ × Torus3 => u p.1 p.2 :=
    continuous_eval.comp ((hu.comp continuous_fst).prodMk continuous_snd)
  -- bound on `D G` along the solution, and the Lipschitz constant of the linearised nonlinearity
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ Icc 0 T, ∀ x, ‖DG (s, x, u s x)‖ ≤ M := by
    have hc : Continuous fun p : ℝ × Torus3 => DG (p.1, p.2, u p.1 p.2) :=
      DG.continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk hU))
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_univ (X := Torus3))).exists_bound_of_continuousOn
      hc.continuousOn
    exact ⟨M, fun s hs x => hM (s, x) ⟨hs, mem_univ _⟩⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩ 0)
  have hLip : ∀ s ∈ Icc 0 T, ∀ x,
      LipschitzWith M.toNNReal fun ω => linearisedNonlin DG u hu (s, x, ω) := by
    intro s hs x
    refine LipschitzWith.of_dist_le_mul fun ω ω' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hM0]
    exact (norm_linearisedNonlin_sub_le DG u hu s x ω ω').trans
      (mul_le_mul_of_nonneg_right (hM s hs x) (norm_nonneg _))
  obtain ⟨w, hw, hmw⟩ := exists_isMildSolution (E := Fin 3 → E) (linearisedNonlin DG u hu) Du₀ hT hLip
  refine ⟨w, hw, hmw, ?_⟩
  obtain ⟨R, hR⟩ := exists_norm_le_of_continuous hu T
  obtain ⟨W₀, hW₀⟩ := exists_norm_le_of_continuous hw T
  set W := ‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ * W₀ with hWdef
  have hW : ∀ s ∈ Icc 0 T, ∀ x, ‖ofPartials (w s x)‖ ≤ W := fun s hs x =>
    ((ofPartials (E := E)).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (((w s).norm_coe_le_norm x).trans (hW₀ s hs)) (norm_nonneg _))
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 ⟨le_rfl, hT⟩ 0)
  -- the main estimate: `‖u(t, · + k) - u(t) - w(t) k‖ ≤ ε |k|` uniformly in `t`
  have key : ∀ ε > 0, ∃ δ > 0, ∀ k : Fin 3 → ℝ, ‖k‖ < δ → ∀ t ∈ Icc 0 T,
      ‖torusShift (torusProj k) (u t) - u t - evalAt (E := E) k (w t)‖ ≤ ε * ‖k‖ := by
    intro ε hε
    set C₀ := (1 + T * (1 + W)) * exp ((1 + M) * T) with hC₀def
    have hC₀ : 0 < C₀ := by positivity
    set ε₁ := min 1 (ε / C₀) with hε₁def
    have hε₁ : 0 < ε₁ := lt_min one_pos (div_pos hε hC₀)
    -- uniform Taylor estimate for `G`
    obtain ⟨δ₁, hδ₁, hTG⟩ := exists_uniform_taylor
      (f := fun p : ℝ × ((Fin 3 → ℝ) × E) => G (p.1, torusProj p.2.1, p.2.2))
      (f' := fun p => DG (p.1, torusProj p.2.1, p.2.2))
      (DG.continuous.comp (continuous_fst.prodMk
        ((continuous_torusProj.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd))))
      (fun s q => hDG s q.1 q.2)
      (K := Icc 0 T ×ˢ (Icc (0 : Fin 3 → ℝ) 1 ×ˢ Metric.closedBall 0 R))
      (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall 0 R))) hε₁
    -- uniform Taylor estimate for `u₀`
    obtain ⟨δ₂, hδ₂, hTu⟩ := exists_uniform_taylor
      (f := fun p : ℝ × (Fin 3 → ℝ) => u₀ (torusProj p.2))
      (f' := fun p => ofPartials (Du₀ (torusProj p.2)))
      (ofPartials.continuous.comp (Du₀.continuous.comp (continuous_torusProj.comp continuous_snd)))
      (fun _ y => hu₀ y)
      (K := ({0} : Set ℝ) ×ˢ Icc (0 : Fin 3 → ℝ) 1)
      (isCompact_singleton.prod isCompact_Icc) hε₁
    -- uniform continuity of `u` on `[0, T] × T³`
    obtain ⟨δ₃, hδ₃, hUC⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc.prod (isCompact_univ (X := Torus3))).uniformContinuousOn_of_continuous
        hU.continuousOn) δ₁ hδ₁
    refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun k hk t ht => ?_⟩
    have hk₁ : ‖k‖ < δ₁ := hk.trans_le (min_le_left _ _)
    have hk₂ : ‖k‖ < δ₂ := hk.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hk₃ : ‖k‖ < δ₃ := hk.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    set e : ℝ → C(Torus3, E) := fun s => torusShift (torusProj k) (u s) - u s - evalAt (E := E) k (w s)
      with he
    have he_cont : Continuous fun s => ‖e s‖ :=
      ((((torusShift (torusProj k)).continuous.comp hu).sub hu).sub
        ((evalAt (E := E) k).continuous.comp hw)).norm
    -- the initial term
    have hinit : ‖torusShift (torusProj k) u₀ - u₀ - evalAt (E := E) k Du₀‖ ≤ ε₁ * ‖k‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
      have := hTu (0, torusRep x) ⟨rfl, torusRep_mem_Icc x⟩ k hk₂
      simpa [torusProj_add, torusProj_torusRep] using this
    -- the forcing term
    have hforce : ∀ s ∈ Icc 0 T, ‖torusShift (torusProj k) (nemytskii G s (u s)) -
        nemytskii G s (u s) - evalAt (E := E) k (nemytskii (E := Fin 3 → E) (linearisedNonlin DG u hu) s (w s))‖ ≤
        ε₁ * (1 + W) * ‖k‖ + (ε₁ + M) * ‖e s‖ := by
      intro s hs
      refine norm_shift_nemytskii_sub_le hu hε₁.le hk₁ (fun x h hh => ?_) (hM s hs) (hW s hs)
        (fun x => ?_)
      · have hp : ((s, (torusRep x, u s x)) : ℝ × ((Fin 3 → ℝ) × E)) ∈
            Icc 0 T ×ˢ (Icc (0 : Fin 3 → ℝ) 1 ×ˢ Metric.closedBall 0 R) :=
          ⟨hs, torusRep_mem_Icc x, mem_closedBall_zero_iff.2
            (((u s).norm_coe_le_norm x).trans (hR s hs))⟩
        have := hTG _ hp h hh
        simpa [torusProj_torusRep] using this
      · have hd : dist ((s, x + torusProj k) : ℝ × Torus3) (s, x) < δ₃ := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm,
            add_sub_cancel_left]
          calc ‖torusProj k‖ = dist (torusProj k) (torusProj 0) := by
                rw [torusProj_zero, dist_zero_right]
            _ ≤ dist k 0 := dist_torusProj_le k 0
            _ = ‖k‖ := dist_zero_right k
            _ < δ₃ := hk₃
        have := hUC (s, x + torusProj k) ⟨hs, mem_univ _⟩ (s, x) ⟨hs, mem_univ _⟩ hd
        rwa [dist_eq_norm] at this
    -- Grönwall
    have hgr : ∀ t ∈ Icc 0 T, ‖e t‖ ≤ ε₁ * ‖k‖ * (1 + T * (1 + W)) +
        (ε₁ + M) * ∫ s in (0 : ℝ)..t, ‖e s‖ := by
      intro t ht
      have hF : Continuous fun s => torusShift (torusProj k) (nemytskii G s (u s)) -
          nemytskii G s (u s) - evalAt (E := E) k (nemytskii (E := Fin 3 → E) (linearisedNonlin DG u hu) s (w s)) :=
        (((torusShift (torusProj k)).continuous.comp (continuous_nemytskii_comp G hu)).sub
          (continuous_nemytskii_comp G hu)).sub
          ((evalAt (E := E) k).continuous.comp (continuous_nemytskii_comp _ hw))
      have hdec := shift_sub_sub_evalAt_eq hu hw hmild hmw k ht
      have h1 : ‖e t‖ ≤ ε₁ * ‖k‖ + ∫ s in (0 : ℝ)..t,
          (ε₁ * (1 + W) * ‖k‖ + (ε₁ + M) * ‖e s‖) := by
        simp only [he]
        rw [hdec]
        refine (norm_add_le _ _).trans (add_le_add ((norm_heatOp_le _ _).trans hinit) ?_)
        refine (norm_duhamel_le hF ht.1).trans ?_
        exact intervalIntegral.integral_mono_on ht.1 (hF.norm.intervalIntegrable 0 t)
          ((continuous_const.add (continuous_const.mul he_cont)).intervalIntegrable 0 t)
          fun s hs => hforce s ⟨hs.1, hs.2.trans ht.2⟩
      have hint : ∫ s in (0 : ℝ)..t, (ε₁ * (1 + W) * ‖k‖ + (ε₁ + M) * ‖e s‖) =
          t * (ε₁ * (1 + W) * ‖k‖) + (ε₁ + M) * ∫ s in (0 : ℝ)..t, ‖e s‖ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((he_cont.intervalIntegrable 0 t).const_mul (ε₁ + M)),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, sub_zero,
          smul_eq_mul]
      rw [hint] at h1
      have h2 : t * (ε₁ * (1 + W) * ‖k‖) ≤ T * (ε₁ * (1 + W) * ‖k‖) :=
        mul_le_mul_of_nonneg_right ht.2 (by positivity)
      nlinarith [h1, h2]
    have hfin := le_mul_exp_of_le_add_integral he_cont (by positivity) hgr t ht
    calc ‖e t‖ ≤ ε₁ * ‖k‖ * (1 + T * (1 + W)) * exp ((ε₁ + M) * t) := hfin
      _ ≤ ε₁ * ‖k‖ * (1 + T * (1 + W)) * exp ((1 + M) * T) := by
          have hε1 : ε₁ ≤ 1 := min_le_left _ _
          have : (ε₁ + M) * t ≤ (1 + M) * T :=
            mul_le_mul (by linarith) ht.2 ht.1 (by linarith)
          gcongr
      _ = ε₁ * C₀ * ‖k‖ := by rw [hC₀def]; ring
      _ ≤ (ε / C₀) * C₀ * ‖k‖ := by gcongr; exact min_le_right _ _
      _ = ε * ‖k‖ := by field_simp
  -- conclusion
  intro t ht y
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hkey⟩ := key c hc
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with k hk
  rw [mem_ball_zero_iff] at hk
  calc ‖u t (torusProj (y + k)) - u t (torusProj y) - ofPartials (w t (torusProj y)) k‖
      = ‖(torusShift (torusProj k) (u t) - u t - evalAt (E := E) k (w t)) (torusProj y)‖ := by
        simp [torusProj_add]
    _ ≤ ‖torusShift (torusProj k) (u t) - u t - evalAt (E := E) k (w t)‖ :=
        ContinuousMap.norm_coe_le_norm _ _
    _ ≤ c * ‖k‖ := hkey k hk t ht

end RegularityStructures.PDE

end

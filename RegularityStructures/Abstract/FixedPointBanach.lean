/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The abstract fixed-point argument for `u = 𝒦 (F u) + v`

This is the functional-analytic core of [Hai14, Theorem 7.8], with every hypothesis explicit.
`X` (the space of solutions, `D^{γ,η}_P` on a time slab) is a complete normed group, `Y` (the
space of right-hand sides, `D^{γ̄,η̄}_P` on the slab) a normed group,

* `𝒦 : Y → X` is additive with `‖𝒦 y‖ ≤ c ‖y‖` (on a slab of length `T`, `c = C T^θ`: the
  short-time gain of [Hai14, Theorem 7.1, Lemma 7.3]);
* `F : X → Y` is Lipschitz on balls, `‖F u − F u'‖ ≤ L(R) ‖u − u'‖` for `‖u‖, ‖u'‖ ≤ R`, with
  `L(R) = L₀ (1 + R)^p` polynomial in the radius, and `‖F 0‖ ≤ A`;
* `v ∈ X` is the datum, `‖v‖ ≤ V`.

Main statements:

* `exists_unique_fixedPoint_of_ball`: if `‖v‖ + c (A + L R) ≤ R` and `c L < 1`, the map
  `u ↦ 𝒦 (F u) + v` has a unique fixed point in the closed ball of radius `R` (Banach's fixed
  point theorem, `ContractingWith.exists_fixedPoint'`);
* `fixedPointTime C θ L₀ A V p`: an explicit time `T₀ > 0` depending only on the bounds;
* `exists_unique_fixedPoint_of_le_fixedPointTime`: for `0 < T ≤ T₀` and `c = C T^θ` there is a
  unique solution with `‖u‖ ≤ V + 1`;
* `norm_sub_le_of_isFixedPt`: Lipschitz dependence on the datum and on the operators:
  `‖u − u'‖ ≤ (‖v − v'‖ + δ) / (1 − c L)` when `‖𝒦 (F w) − 𝒦' (F' w)‖ ≤ δ` on the ball;
* `eq_of_isFixedPt_of_norm_le`: two solutions of norm `≤ R` coincide once `c L(R) < 1`;
* `le_of_forall_imp_mul_add`: the scalar iteration used for continuity in the model.

**Uniqueness is local.** Uniqueness holds in a ball (or among solutions of norm `≤ R` for
`T ≤ T₀(R)`), not among all solutions: for `X = Y = ℝ`, `𝒦 = c · id`, `F u = u³`, `v = 0` the
equation `u = c u³` has the solutions `± c^{-1/2}` for every `c > 0`. Hairer's uniqueness in all
of `D^{γ,η}_P` on `(0, T)` ("a simple continuity argument") uses the time structure of the
problem (restarting the equation at intermediate times, Proposition 7.11), which the abstract
hypotheses do not contain.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.8 and its proof.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The existence time of [Hai14, Theorem 7.8] in terms of the bounds: with
`B = A + L₀ (2 + V)^p (3 + V)`, `T₀ = ((C + 1)(B + 1))^{-1/θ}`. Here `C T^θ` bounds `𝒦`,
`L₀ (1 + R)^p` is the Lipschitz constant of `F` on the ball of radius `R`, `A ≥ ‖F 0‖` and
`V ≥ ‖v‖`. -/
def fixedPointTime (C θ L₀ A V : ℝ) (p : ℕ) : ℝ :=
  ((C + 1) * (A + L₀ * (2 + V) ^ p * (3 + V) + 1))⁻¹ ^ θ⁻¹

end RegularityStructures

end

public section

open Set Function Metric
open scoped NNReal

namespace RegularityStructures

section Scalar

/-- **Iteration of an affine contraction on a closed predicate.** If `P` is monotone and closed
under decreasing limits, holds at some `a₀`, and `P a → P (q a + ε)` with `0 ≤ q < 1`, then
`P (ε / (1 − q))`. -/
theorem le_of_forall_imp_mul_add {P : ℝ → Prop} {q ε a₀ : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (hε : 0 ≤ ε) (hmono : ∀ a b, a ≤ b → P a → P b) (hclosed : ∀ a, (∀ b, a < b → P b) → P a)
    (h₀ : P a₀) (hstep : ∀ a, 0 ≤ a → P a → P (q * a + ε)) : P (ε / (1 - q)) := by
  have h1q : 0 < 1 - q := by linarith
  set s := ε / (1 - q) with hs
  have hs0 : 0 ≤ s := div_nonneg hε h1q.le
  have hsfix : q * s + ε = s := by
    rw [hs]
    field_simp
    ring
  -- start from `b₀ = max a₀ s + 1 > s`
  set b₀ := max a₀ s + 1 with hb₀
  have hb₀s : s < b₀ := by
    have := le_max_right a₀ s
    linarith
  have hP₀ : P b₀ := hmono _ _ (by have := le_max_left a₀ s; linarith) h₀
  -- the iterates `s + qⁿ (b₀ − s)` all satisfy `P`
  have hiter : ∀ n : ℕ, P (s + q ^ n * (b₀ - s)) := by
    intro n
    induction n with
    | zero => simpa using hP₀
    | succ n ih =>
      have hnn : 0 ≤ s + q ^ n * (b₀ - s) :=
        add_nonneg hs0 (mul_nonneg (pow_nonneg hq0 n) (by linarith))
      have h := hstep _ hnn ih
      have heq : q * (s + q ^ n * (b₀ - s)) + ε = s + q ^ (n + 1) * (b₀ - s) := by
        rw [pow_succ]
        linear_combination hsfix
      rwa [heq] at h
  refine hclosed s fun b hb => ?_
  have hpos : 0 < (b - s) / (b₀ - s) := div_pos (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hq
  refine hmono _ _ ?_ (hiter n)
  have := (lt_div_iff₀ (by linarith : (0 : ℝ) < b₀ - s)).1 hn
  linarith

/-- The smallness condition behind `fixedPointTime`: for `0 < T ≤ T₀`,
`C T^θ (A + L₀ (2 + V)^p (3 + V)) ≤ 1`. -/
theorem mul_rpow_mul_le_one_of_le_fixedPointTime {C θ L₀ A V T : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hθ : 0 < θ) (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A) (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hTT₀ : T ≤ fixedPointTime C θ L₀ A V p) :
    C * T ^ θ * (A + L₀ * (2 + V) ^ p * (3 + V)) ≤ 1 := by
  set B := A + L₀ * (2 + V) ^ p * (3 + V) with hB
  have hB0 : 0 ≤ B := by positivity
  have hD : 0 < (C + 1) * (B + 1) := by positivity
  have hTθ : T ^ θ ≤ ((C + 1) * (B + 1))⁻¹ := by
    have h := Real.rpow_le_rpow hT hTT₀ hθ.le
    rwa [fixedPointTime, ← hB, Real.rpow_inv_rpow (inv_nonneg.2 hD.le) hθ.ne'] at h
  calc C * T ^ θ * B ≤ C * ((C + 1) * (B + 1))⁻¹ * B := by gcongr
    _ = (C * B) / ((C + 1) * (B + 1)) := by field_simp
    _ ≤ 1 := by
        rw [div_le_one hD]
        nlinarith

theorem fixedPointTime_pos (C θ L₀ A V : ℝ) (p : ℕ) (hC : 0 ≤ C) (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A)
    (hV : 0 ≤ V) : 0 < fixedPointTime C θ L₀ A V p := by
  unfold fixedPointTime
  exact Real.rpow_pos_of_pos (inv_pos.2 (by positivity)) _

end Scalar

section Banach

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {𝓚 : Type*}
  [FunLike 𝓚 Y X] [AddMonoidHomClass 𝓚 Y X]

/-- The fixed-point map is `c L`-Lipschitz on a ball where `F` is `L`-Lipschitz. -/
theorem norm_sub_le_of_lipschitz_ball (𝒦 : 𝓚) {c L R : ℝ} (hc : 0 ≤ c)
    (h𝒦 : ∀ y, ‖𝒦 y‖ ≤ c * ‖y‖) {F : X → Y}
    (hF : ∀ u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L * ‖u - u'‖) (v : X) {u u' : X}
    (hu : ‖u‖ ≤ R) (hu' : ‖u'‖ ≤ R) :
    ‖(𝒦 (F u) + v) - (𝒦 (F u') + v)‖ ≤ c * L * ‖u - u'‖ := by
  rw [add_sub_add_right_eq_sub, ← map_sub]
  calc ‖𝒦 (F u - F u')‖ ≤ c * ‖F u - F u'‖ := h𝒦 _
    _ ≤ c * (L * ‖u - u'‖) := mul_le_mul_of_nonneg_left (hF u u' hu hu') hc
    _ = c * L * ‖u - u'‖ := by ring

/-- **Uniqueness of the fixed point in a ball.** Two solutions of `u = 𝒦 (F u) + v` of norm
`≤ R` coincide when `F` is `L`-Lipschitz on the ball and `c L < 1`. -/
theorem eq_of_isFixedPt_of_norm_le (𝒦 : 𝓚) {c L R : ℝ} (hc : 0 ≤ c)
    (h𝒦 : ∀ y, ‖𝒦 y‖ ≤ c * ‖y‖) {F : X → Y}
    (hF : ∀ u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L * ‖u - u'‖) (hcL : c * L < 1) {v : X}
    {u u' : X} (hu : ‖u‖ ≤ R) (hu' : ‖u'‖ ≤ R) (hfix : u = 𝒦 (F u) + v)
    (hfix' : u' = 𝒦 (F u') + v) : u = u' := by
  have h := norm_sub_le_of_lipschitz_ball 𝒦 hc h𝒦 hF v hu hu'
  rw [← hfix, ← hfix'] at h
  have h0 : ‖u - u'‖ ≤ 0 := by nlinarith [norm_nonneg (u - u')]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

omit [AddMonoidHomClass 𝓚 Y X] in
/-- The fixed-point map sends the ball of radius `R` into itself when
`‖v‖ + c (A + L R) ≤ R`. -/
theorem norm_le_of_norm_le (𝒦 : 𝓚) {c L R A : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L)
    (h𝒦 : ∀ y, ‖𝒦 y‖ ≤ c * ‖y‖) {F : X → Y}
    (hF : ∀ u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L * ‖u - u'‖) (hF0 : ‖F 0‖ ≤ A)
    {v : X} (hR : ‖v‖ + c * (A + L * R) ≤ R) {u : X} (hu : ‖u‖ ≤ R) :
    ‖𝒦 (F u) + v‖ ≤ R := by
  have hR0 : 0 ≤ R := (norm_nonneg u).trans hu
  have hFu : ‖F u‖ ≤ A + L * R := by
    have h := hF u 0 hu (by simpa using hR0)
    rw [sub_zero] at h
    calc ‖F u‖ ≤ ‖F u - F 0‖ + ‖F 0‖ := norm_le_norm_sub_add _ _
      _ ≤ L * ‖u‖ + A := add_le_add h hF0
      _ ≤ A + L * R := by nlinarith
  calc ‖𝒦 (F u) + v‖ ≤ ‖𝒦 (F u)‖ + ‖v‖ := norm_add_le _ _
    _ ≤ c * ‖F u‖ + ‖v‖ := add_le_add_left (h𝒦 _) _
    _ ≤ c * (A + L * R) + ‖v‖ := add_le_add_left (mul_le_mul_of_nonneg_left hFu hc) _
    _ ≤ R := by linarith

/-- **Banach fixed point on a ball** ([Hai14, proof of Theorem 7.8]). If `‖𝒦 y‖ ≤ c ‖y‖`, `F`
is `L`-Lipschitz on the ball of radius `R` with `‖F 0‖ ≤ A`, `‖v‖ + c (A + L R) ≤ R` and
`c L < 1`, then `u = 𝒦 (F u) + v` has exactly one solution with `‖u‖ ≤ R`. -/
theorem exists_unique_fixedPoint_of_ball [CompleteSpace X] (𝒦 : 𝓚) {c L R A : ℝ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (h𝒦 : ∀ y, ‖𝒦 y‖ ≤ c * ‖y‖) {F : X → Y}
    (hF : ∀ u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L * ‖u - u'‖) (hF0 : ‖F 0‖ ≤ A)
    {v : X} (hR : ‖v‖ + c * (A + L * R) ≤ R) (hcL : c * L < 1) :
    ∃! u : X, ‖u‖ ≤ R ∧ u = 𝒦 (F u) + v := by
  set f : X → X := fun u => 𝒦 (F u) + v with hf
  set s : Set X := closedBall 0 R with hs
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hF0
  have hR0 : 0 ≤ R := by nlinarith [norm_nonneg v, mul_nonneg hc hA0]
  have hmaps : MapsTo f s s := fun u hu => by
    rw [hs, mem_closedBall_zero_iff] at hu ⊢
    exact norm_le_of_norm_le 𝒦 hc hL h𝒦 hF hF0 hR hu
  have hK : (0 : ℝ) ≤ c * L := mul_nonneg hc hL
  have hcontr : ContractingWith ⟨c * L, hK⟩ (hmaps.restrict f s s) := by
    refine ⟨by exact_mod_cast hcL, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha : ‖(a : X)‖ ≤ R := mem_closedBall_zero_iff.1 a.2
    have hb : ‖(b : X)‖ ≤ R := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact norm_sub_le_of_lipschitz_ball 𝒦 hc h𝒦 hF v ha hb
  have h0s : (0 : X) ∈ s := mem_closedBall_self hR0
  obtain ⟨u, hus, hufix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps h0s
    (edist_ne_top _ _)
  refine ⟨u, ⟨mem_closedBall_zero_iff.1 hus, hufix.symm⟩, fun u' hu' => ?_⟩
  exact eq_of_isFixedPt_of_norm_le 𝒦 hc h𝒦 hF hcL hu'.1 (mem_closedBall_zero_iff.1 hus) hu'.2
    hufix.symm

/-- **The abstract fixed-point theorem with an explicit existence time** ([Hai14, Theorem 7.8],
functional-analytic form). Let `‖𝒦 y‖ ≤ C T^θ ‖y‖`, let `F` satisfy
`‖F u − F u'‖ ≤ L₀ (1 + R)^p ‖u − u'‖` for `‖u‖, ‖u'‖ ≤ R` (every `R`) and `‖F 0‖ ≤ A`, and let
`‖v‖ ≤ V`. For every `0 < T ≤ T₀ = fixedPointTime C θ L₀ A V p`, which depends only on these
bounds, the equation `u = 𝒦 (F u) + v` has exactly one solution with `‖u‖ ≤ V + 1`. -/
theorem exists_unique_fixedPoint_of_le_fixedPointTime [CompleteSpace X] (𝒦 : 𝓚)
    {C θ L₀ A V T : ℝ} {p : ℕ} (hC : 0 ≤ C) (hθ : 0 < θ) (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A)
    (hV : 0 ≤ V) (hT : 0 < T) (hTT₀ : T ≤ fixedPointTime C θ L₀ A V p)
    (h𝒦 : ∀ y, ‖𝒦 y‖ ≤ C * T ^ θ * ‖y‖) {F : X → Y}
    (hF : ∀ R u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L₀ * (1 + R) ^ p * ‖u - u'‖)
    (hF0 : ‖F 0‖ ≤ A) {v : X} (hv : ‖v‖ ≤ V) :
    ∃! u : X, ‖u‖ ≤ V + 1 ∧ u = 𝒦 (F u) + v := by
  have hsmall := mul_rpow_mul_le_one_of_le_fixedPointTime hC hθ hL₀ hA hV hT.le hTT₀
  have hc : 0 ≤ C * T ^ θ := mul_nonneg hC (Real.rpow_nonneg hT.le _)
  have hL : 0 ≤ L₀ * (2 + V) ^ p := by positivity
  have hR : ‖v‖ + C * T ^ θ * (A + L₀ * (2 + V) ^ p * (V + 1)) ≤ V + 1 := by
    have : C * T ^ θ * (A + L₀ * (2 + V) ^ p * (V + 1)) ≤
        C * T ^ θ * (A + L₀ * (2 + V) ^ p * (3 + V)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc
    linarith
  have hcL : C * T ^ θ * (L₀ * (2 + V) ^ p) < 1 := by
    have : C * T ^ θ * (L₀ * (2 + V) ^ p) * 2 ≤ C * T ^ θ * (A + L₀ * (2 + V) ^ p * (3 + V)) := by
      have := mul_nonneg hc hL
      nlinarith
    nlinarith [mul_nonneg hc hL]
  have hF' : ∀ u u', ‖u‖ ≤ V + 1 → ‖u'‖ ≤ V + 1 →
      ‖F u - F u'‖ ≤ L₀ * (2 + V) ^ p * ‖u - u'‖ := fun u u' hu hu' => by
    have h := hF (V + 1) u u' hu hu'
    rwa [show (1 + (V + 1)) = 2 + V by ring] at h
  exact exists_unique_fixedPoint_of_ball 𝒦 hc hL h𝒦 hF' hF0 hR hcL

end Banach

end RegularityStructures

end

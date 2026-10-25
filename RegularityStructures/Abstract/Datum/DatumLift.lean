/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.SingularLift
public import RegularityStructures.Abstract.Datum.LiftMeasurable
public import RegularityStructures.Abstract.Datum.HeatLikeExt
public import RegularityStructures.Abstract.Datum.HeatExtCont
public import RegularityStructures.Abstract.Model

/-!
# The lift of the free heat evolution of an initial datum `a ∈ 𝒞^η`

[Hai14, Lemma 7.5 and Proposition A.1]. For `a ∈ 𝒞^η` (`η < 0`) the function
`(t, y) ↦ P_t a (y)` is smooth on `{t > 0}` with `|D^k P_t a| ≤ C_k t^{(η - |k|_𝔰)/2} ‖a‖_η` for
`0 < t ≤ 1` (`abs_D_datumField_le`). Its Taylor lift into the polynomial sector,
`datumLift P γ₀ a x = ∑_{|k|_𝔰 < γ₀} D^k (P_· a)(x) / k! · e_{P.emb k}` (and `0` for `t ≤ 0`),
is a singular modelled distribution on the time slab `(0, T]` for every polynomial-compatible
model `M` (`singularBoundOn_datumLift`), with constant `C ‖a‖_η`, `C` depending only on `η`, `N`;
it is additive in `a` (`datumLift_sub`), so
`SingularDiffBoundOn M M ρ γ₀ η (C ‖a - b‖_η) (timeSlab T) (datumLift a) (datumLift b)`
(`singularDiffBoundOn_datumLift`).
-/

public section

open Set Filter Topology MeasureTheory

namespace RegularityStructures.Datum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

open RegularityStructures.PDE

theorem datumField_of_nonpos (η : NegExponent) (a : HolderBesov η) {z : ParabolicSpace}
    (hz : z.1 ≤ 0) : datumField η a z = 0 := by
  simp [datumField, not_lt.2 hz]

theorem datumField_sub (η : NegExponent) (a b : HolderBesov η) :
    datumField η (a - b) = datumField η a - datumField η b := by
  funext z
  by_cases hz : 0 < z.1
  · simp [datumField_of_pos η _ hz, heatExt_sub]
  · simp [datumField_of_nonpos η _ (not_lt.1 hz)]

/-- **Derivative bounds** `|D^k P_t a| ≤ C_k t^{(η - |k|_𝔰)/2} ‖a‖_η` for `0 < t ≤ 1`: the
constants are uniform in `a`. -/
theorem exists_derivBound (η : NegExponent) :
    ∃ Kc : (Fin 4 → ℕ) → ℝ, (∀ k, 0 ≤ Kc k) ∧
      ∀ a : HolderBesov η, DerivBound (η : ℝ) ‖a‖ Kc (datumField η a) := by
  choose K hK using heatLike_bound_D (heatLike_datumField η)
  refine ⟨fun k => max (K k) 0, fun k => le_max_right _ _, fun a => ⟨smoothPos_datumField η a,
    fun k z hz hz1 => ?_⟩⟩
  refine (hK k a z hz hz1).trans ?_
  have : 0 ≤ ‖a‖ * z.1 ^ (((η : ℝ) - (wt k : ℝ)) / 2) :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _)
  have h := mul_le_mul_of_nonneg_right (le_max_left (K k) 0) this
  calc K k * ‖a‖ * z.1 ^ (((η : ℝ) - ((2 * k 0 + k 1 + k 2 + k 3 : ℕ) : ℝ)) / 2)
      = K k * (‖a‖ * z.1 ^ (((η : ℝ) - (wt k : ℝ)) / 2)) := by
        unfold wt
        ring
    _ ≤ max (K k) 0 * (‖a‖ * z.1 ^ (((η : ℝ) - (wt k : ℝ)) / 2)) := h
    _ = _ := by ring

theorem liftOf_sub (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) {F G : ParabolicSpace → ℝ}
    (hF : SmoothPos F) (hG : SmoothPos G) (x : ParabolicSpace) :
    liftOf P γ₀ (F - G) x = liftOf P γ₀ F x - liftOf P γ₀ G x := by
  have e : F - G = F + (-1 : ℝ) • G := by
    funext z
    simp [sub_eq_add_neg]
  rw [e, liftOf_add P γ₀ hF (hG.smul _), liftOf_smul P γ₀ hG]
  simp [sub_eq_add_neg]

theorem singularDiffBoundOn_of_sub {𝒯' : RegularityStructure ι} {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {K : RegularisingSemigroup E μ} {M : Model 𝒯' K} {ρ : E → ℝ}
    {γ η C : ℝ} {S : Set E} {f g : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η C S (fun x => f x - g x)) :
    M.SingularDiffBoundOn M ρ γ η C S f g := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · simpa using h.1 x hx hρ i hi
  · have := h.2 x hx y hy hρx hρy hd j hj
    simpa [map_sub, sub_sub_sub_comm] using this

theorem singularBoundOn_congr {𝒯' : RegularityStructure ι} {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {K : RegularisingSemigroup E μ} {M : Model 𝒯' K} {ρ : E → ℝ}
    {γ η C : ℝ} {S : Set E} {f g : E → ι → ℝ} (hfg : ∀ x ∈ S, f x = g x)
    (h : M.SingularBoundOn ρ γ η C S f) : M.SingularBoundOn ρ γ η C S g := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · rw [← hfg x hx]
    exact h.1 x hx hρ i hi
  · rw [← hfg x hx, ← hfg y hy]
    exact h.2 x hx y hy hρx hρy hd j hj

end RegularityStructures.Datum

end


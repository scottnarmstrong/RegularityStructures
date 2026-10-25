/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointBanach
public import RegularityStructures.Abstract.FixedPointShortTime
public import RegularityStructures.Abstract.Model

/-!
# The abstract fixed-point theorem on a time slab

[Hai14, Theorem 7.8] for a fixed model: the equation `U = 𝒦(1_{t>0} F(U)) + v` on the slab
`(0, T]` has a unique solution in `D^{γ,η}_P` for `T` small, depending only on the bounds.

**Setting.** The slab is a set `S ⊆ E`; `Model.SlabSpace M ρ V γ η S` is `D^{γ,η}_P(V)` on the
slab, a Banach space (`RegularityStructures.Abstract.FixedPointSlabSpace`,
`RegularityStructures.Abstract.FixedPointSlabComplete`). Its elements vanish off `S⁺ = S ∩ {ρ > 0}`,
i.e. they live on the slab, so `1_{t>0}` acts as the identity on them and the equation is
`U = 𝒦 (F U) + v` with

* `𝒦 : D^{γ̄,η̄}_P(V̄) → D^{γ,η}_P(V)` on the slab, linear, `‖𝒦 g‖ ≤ C T^θ ‖g‖`: this is the bound
  `|||𝒦_γ R⁺ f|||_{γ,η;T} ≤ C T^θ |||f|||_{γ̄,η̄;T}` of [Hai14, Theorem 7.1, Lemma 7.3] for the
  slab operator `g ↦ 1_{S⁺} 𝒦(1_{t>0} g)`; its non-anticipativity is built into the slab
  formulation (the right-hand side only sees `g` on the slab);
* `F : D^{γ,η}_P(V) → D^{γ̄,η̄}_P(V̄)` on the slab, locally Lipschitz with constants polynomial in
  the radius: `‖F u − F u'‖ ≤ L₀ (1 + R)^p ‖u − u'‖` for `‖u‖, ‖u'‖ ≤ R`, and `‖F 0‖ ≤ A`;
* the datum `v ∈ D^{γ,η}_P(V)` on the slab, `‖v‖ ≤ R₀` (e.g. the restriction of a global element
  of `D^{γ,η}_P`, `Model.slabRestrict`).

In the code Hairer's `γ̄, η̄, V̄` are written `γ', η', V'`.

Main statements:

* `Model.exists_unique_slab_fixedPoint` (**Theorem 7.8, fixed model**): for every
  `0 < T ≤ T₀ = fixedPointTime C θ L₀ A R₀ p` there is a unique `U` with `‖U‖ ≤ R₀ + 1` and
  `U = 𝒦 (F U) + v`;
* `Model.exists_unique_slab_fixedPoint_of_vanishing` (**Theorems 7.1 + 7.8**): the same when `𝒦`
  maps into the class vanishing at `P` to order `η + κ` with a constant `C` uniform in `T` and
  the slab satisfies `ρ ≤ T^{1/𝔰₀}`; then `θ = κ/𝔰₀`;
* `Model.slab_fixedPoint_eq_of_norm_le`: uniqueness among all solutions of norm `≤ R` once
  `C T^θ L₀ (1 + R)^p < 1`;
* `Model.norm_sub_slab_fixedPoint_le`: Lipschitz dependence on the datum,
  `|||U − U'|||_{γ,η;T} ≤ 2 |||v − v'|||_{γ,η;T}`;
* `Model.norm_sub_slab_fixedPoint_le_of_perturbation`: Lipschitz dependence on the operators,
  `|||U − U'||| ≤ 2 (|||v − v'||| + C T^θ ε_F + ε_𝒦 B)` when `‖F − F'‖ ≤ ε_F` and
  `‖F'‖ ≤ B` on the ball and `‖𝒦 − 𝒦'‖ ≤ ε_𝒦`.

Continuity in the model (two different slab spaces) is
`RegularityStructures.Abstract.FixedPointTwoModels`.

**On uniqueness.** Uniqueness is proved in the ball `‖U‖ ≤ R₀ + 1`, and among solutions of norm
`≤ R` for `T ≤ T₀(R)`. Uniqueness among *all* solutions in `D^{γ,η}_P` on `(0, T)`, as stated in
[Hai14, Theorem 7.8], is not a consequence of these hypotheses (see
`RegularityStructures.Abstract.FixedPointBanach`: `u = c u³` has the solutions `± c^{-1/2}`);
Hairer's continuity argument restarts the equation at intermediate times, which needs the structure
of Proposition 7.11.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.8, Theorem 7.1, Lemma 7.3.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)
  {ρ : E → ℝ} {V V' : Submodule ℝ (ι → ℝ)} {γ η γ' η' : ℝ} {S : Set E}

/-- **The abstract fixed-point theorem on a time slab** ([Hai14, Theorem 7.8], fixed model).
Let `𝒦 : D^{γ',η'}_P(V') → D^{γ,η}_P(V)` on the slab be linear with
`|||𝒦 g|||_{γ,η;T} ≤ C T^θ |||g|||_{γ',η';T}`, let `F : D^{γ,η}_P(V) → D^{γ',η'}_P(V')` satisfy
`|||F u − F u'|||_{γ',η';T} ≤ L₀ (1 + R)^p |||u − u'|||_{γ,η;T}` for `|||u|||, |||u'||| ≤ R` and
`|||F 0||| ≤ A`, and let `|||v|||_{γ,η;T} ≤ R₀`. For every `0 < T ≤ fixedPointTime C θ L₀ A R₀ p`
(a time depending only on these bounds) there is exactly one `U` with `|||U|||_{γ,η;T} ≤ R₀ + 1`
and `U = 𝒦 (F U) + v`. -/
theorem exists_unique_slab_fixedPoint {C θ L₀ A R₀ T : ℝ} {p : ℕ} (hC : 0 ≤ C) (hθ : 0 < θ)
    (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A) (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime C θ L₀ A R₀ p)
    (𝒦 : M.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M.SlabSpace ρ V γ η S)
    (h𝒦 : ∀ g, ‖𝒦 g‖ ≤ C * T ^ θ * ‖g‖) (F : M.SlabSpace ρ V γ η S → M.SlabSpace ρ V' γ' η' S)
    (hF : ∀ R u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L₀ * (1 + R) ^ p * ‖u - u'‖)
    (hF0 : ‖F 0‖ ≤ A) (v : M.SlabSpace ρ V γ η S) (hv : ‖v‖ ≤ R₀) :
    ∃! U : M.SlabSpace ρ V γ η S, ‖U‖ ≤ R₀ + 1 ∧ U = 𝒦 (F U) + v :=
  exists_unique_fixedPoint_of_le_fixedPointTime 𝒦 hC hθ hL₀ hA hR₀ hT hTT₀ h𝒦 hF hF0 hv

/-- **Theorems 7.1 and 7.8 combined.** If `𝒦` maps into the class vanishing at `P` to order
`η + κ`: `|(𝒦 g)(x)_i| ≤ C |||g||| ‖x‖_P^{η + κ − deg i}` and `|||𝒦 g|||_{γ,η+κ;T} ≤ C |||g|||`,
with `C` independent of `T`, and the slab satisfies `ρ ≤ T^{1/𝔰₀}`, then the conclusion of
`exists_unique_slab_fixedPoint` holds with `θ = κ/𝔰₀` for
`0 < T ≤ fixedPointTime C (κ/𝔰₀) L₀ A R₀ p`. -/
theorem exists_unique_slab_fixedPoint_of_vanishing {C κ s L₀ A R₀ T : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hκ : 0 < κ) (hs : 0 < s) (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A) (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime C (κ / s) L₀ A R₀ p) (hS : ∀ x ∈ S, 0 < ρ x → ρ x ≤ T ^ s⁻¹)
    (𝒦 : M.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M.SlabSpace ρ V γ η S)
    (h𝒦sup : ∀ g, ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |(𝒦 g).val x i| ≤ C * ‖g‖ * singularWeight ρ x ^ (η + κ - 𝒯.deg i))
    (h𝒦 : ∀ g, M.SingularBoundOn ρ γ (η + κ) (C * ‖g‖) S (𝒦 g).val)
    (F : M.SlabSpace ρ V γ η S → M.SlabSpace ρ V' γ' η' S)
    (hF : ∀ R u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L₀ * (1 + R) ^ p * ‖u - u'‖)
    (hF0 : ‖F 0‖ ≤ A) (v : M.SlabSpace ρ V γ η S) (hv : ‖v‖ ≤ R₀) :
    ∃! U : M.SlabSpace ρ V γ η S, ‖U‖ ≤ R₀ + 1 ∧ U = 𝒦 (F U) + v := by
  refine M.exists_unique_slab_fixedPoint hC (div_pos hκ hs) hL₀ hA hR₀ hT hTT₀ 𝒦 (fun g => ?_)
    F hF hF0 v hv
  have h := (𝒦 g).norm_le_of_vanishing hκ.le (mul_nonneg hC (norm_nonneg g)) hT.le hS
    (h𝒦sup g) (h𝒦 g)
  calc ‖𝒦 g‖ ≤ T ^ (κ / s) * (C * ‖g‖) := h
    _ = C * T ^ (κ / s) * ‖g‖ := by ring

end Model

end RegularityStructures

end

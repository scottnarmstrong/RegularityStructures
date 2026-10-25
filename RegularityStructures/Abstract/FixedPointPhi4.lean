/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTwoModels
public import RegularityStructures.Abstract.Model

/-!
# The Φ⁴₃ nonlinearity in the abstract fixed-point theorem

[Hai14, Lemma 9.7 and Proposition 9.8]: the map `U ↦ U³ = Q_{<γ̄}(U ⋆ U ⋆ U)` is locally
Lipschitz (in the strong sense) from `D^{γ₀,η₀}_P(V)` to `D^{γ₀+2α, η''}_P`, so Theorem 7.8
applies to the Φ⁴₃ fixed-point problem `U = −𝒦(1_{t>0} U³) + v` [Hai14, (9.18)], for any
integration operator `𝒦` with the short-time gain. Here `𝒦` is a hypothesis: the concrete
`𝒦_γ̄ + R_γ R` comes from the multilevel Schauder estimate (another part of the project).

On the slab spaces of `RegularityStructures.Abstract.FixedPointSlabSpace`:

* `Model.SlabSpace.cube P γ' η' u`: the truncated cube of `u`, as an element of `D^{γ',η'}_P` on
  the slab (with junk value `0` if it does not belong to it; under the hypotheses of
  [Hai14, Lemma 9.7] it always does, `Model.SlabSpace.val_cube`);
* `Model.SlabSpace.norm_cube_le`: `|||U³||| ≤ c² |||U|||³ (1 + C_Γ)⁴`;
* `Model.SlabSpace.norm_cube_sub_cube_le`: `|||U³ − U'³||| ≤ 3 c² (1 + C_Γ)⁴ (1 + R)² |||U − U'|||`
  for `|||U|||, |||U'||| ≤ R`: the local Lipschitz bound with constants polynomial in `R`;
* `Model.exists_unique_phi4_slab_fixedPoint` (**[Hai14, Proposition 9.8], local part, fixed
  model**): for `0 < T ≤ fixedPointTime C θ (3 c² (1 + C_Γ)⁴) 0 R₀ 2` the equation
  `U = −𝒦 (U³) + v` has a unique solution with `|||U|||_{γ₀,η₀;T} ≤ R₀ + 1`;
* `Model.singularDiffBoundOn_phi4_slab_fixedPoint`: Lipschitz dependence on the model and the
  datum, `|||U; Ū||| ≤ 2 (δ_v + C T^θ ε_F + ε_𝒦)` with `ε_F = 4 c² (R₀+1)³ (1 + C_Γ)⁴ δ_Γ`.

(`Model.SingularDiffBoundOn.neg`: `|||−f; −g||| = |||f; g|||`.)

Here `c = P.truncMulConst`, `C_Γ` bounds `Γ` on the slab, `δ_Γ` bounds `Γ − Γ̄`, and the exponent
conditions are those of `Model.singularBoundOn_truncCube`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 9.7, Proposition 9.8, (9.18).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct) {E : Type*}

/-- The product of measurable functions is measurable. -/
theorem measurable_mul_apply [MeasurableSpace E] {f g : E → ι → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => P.mul (f x) (g x) := by
  refine Measurable.of_eval fun k => ?_
  simp only [mul_apply_eq_sum]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply j).comp hg)).mul_const _

/-- The truncated cube of a measurable function is measurable. -/
theorem measurable_truncCube [MeasurableSpace E] (γ : ℝ) {U : E → ι → ℝ} (hU : Measurable U) :
    Measurable (P.truncCube γ U) := by
  have h := P.measurable_mul_apply hU (P.measurable_mul_apply hU hU)
  refine Measurable.of_eval fun k => ?_
  simp only [truncCube, truncTripleMul, lowerProj_apply]
  split_ifs
  · exact (measurable_pi_apply k).comp h
  · exact measurable_const

theorem truncCube_apply_eq_zero (γ : ℝ) {U : E → ι → ℝ} {x : E} (h : U x = 0) :
    P.truncCube γ U x = 0 := by
  simp [truncCube, truncTripleMul, h]

end RegularityStructure.GradedProduct

end RegularityStructures

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

open scoped Classical in
/-- The Φ⁴₃ nonlinearity on the slab: `u ↦ u³ = Q_{<γ'}(u ⋆ u ⋆ u)` as an element of
`D^{γ',η'}_P` on the slab, and `0` if the cube does not belong to that space (which does not
happen under the hypotheses of [Hai14, Lemma 9.7], see `Model.SlabSpace.val_cube`). -/
def SlabSpace.cube (P : 𝒯.GradedProduct) (γ' η' : ℝ) (u : M.SlabSpace ρ V γ η S) :
    M.SlabSpace ρ ⊤ γ' η' S :=
  if h : P.truncCube γ' u.val ∈ M.slabModelledDistributions ρ ⊤ γ' η' S then
    SlabSpace.mk _ h
  else 0

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {S : Set E} (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)}
  {α γ₀ η₀ η' η'' CΓ : ℝ} (hV : 𝒯.IsSector V) (hW : 𝒯.IsSector W)
  (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
  (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
  (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
  (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
  (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
  (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α)

include hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ

omit hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ in
theorem SingularDiffBoundOn.neg {M₁ M₂ : Model 𝒯 K} {γ η C : ℝ} {f g : E → ι → ℝ}
    (h : M₁.SingularDiffBoundOn M₂ ρ γ η C S f g) :
    M₁.SingularDiffBoundOn M₂ ρ γ η C S (-f) (-g) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have e : (-f) x i - (-g) x i = -(f x i - g x i) := by simp only [Pi.neg_apply]; ring
    rw [e, abs_neg]
    exact h.1 x hx hρ i hi
  · have e : ((-f) y - M₁.gammaMap y x ((-f) x)) j - ((-g) y - M₂.gammaMap y x ((-g) x)) j =
        -((f y - M₁.gammaMap y x (f x)) j - (g y - M₂.gammaMap y x (g x)) j) := by
      simp only [Pi.neg_apply, map_neg, Pi.sub_apply]
      ring
    rw [e, abs_neg]
    exact h.2 x hx y hy hρx hρy hd j hj

end Model

end RegularityStructures

end

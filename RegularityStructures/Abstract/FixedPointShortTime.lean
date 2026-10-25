/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointSlabComplete
public import RegularityStructures.Abstract.Model

/-!
# The short-time gain `T^θ` on a time slab

[Hai14, proof of Theorem 7.1 and Lemma 7.3]: on the slab `O_T` one has `‖z‖_P ≤ T^{1/𝔰₀}`
(`𝔰₀` the time scaling, `𝔰₀ = 2` for parabolic problems), so a modelled distribution that
*vanishes at `P` to order `η + κ`* has `D^{γ,η}`-norm on the slab smaller by the factor
`T^{κ/𝔰₀}`. In Theorem 7.1 the vanishing comes from Lemma 6.5 (non-anticipative kernels and
`R⁺`): `‖𝒦_γ R⁺ f(z)‖_ℓ ≲ ‖z‖_P^{(η ∧ α) + β − ℓ}` with no `∧ 0` in the exponent.

Here `S ⊆ E` is the slab, and the slab condition is `‖x‖_P ≤ r` for `x ∈ S⁺` (with
`r = T^{1/𝔰₀}`, `singularWeight_le_rpow_inv`).

Main statements (`κ ≥ 0`):

* `Model.singularBoundOn_of_vanishing` (**the gain**): if `|f(x)_i| ≤ C ‖x‖_P^{η + κ − deg i}`
  (the vanishing bound, no `∧ 0`) and the increments satisfy the bound of `D^{γ,η+κ}` with
  constant `C`, then `|||f|||_{γ,η;S} ≤ r^κ C`;
* `Model.singularBoundOn_shortTime`: the same with `r = T^{1/𝔰₀}`, i.e. the constant `T^{κ/𝔰₀} C`;
* `Model.SingularBoundOn.vanishing_of_apply_eq_zero`: an element of `D^{γ,η'}` vanishing in
  degrees `< ζ` (e.g. with values in a sector of regularity `ζ`) satisfies the vanishing bound
  with exponent `η' ∧ ζ`; hence (`Model.singularBoundOn_shortTime_of_apply_eq_zero`)
  `|||f|||_{γ,η;S} ≤ T^{κ/𝔰₀} |||f|||_{γ,η';S}` whenever `η + κ ≤ η' ∧ ζ`;
* `Model.SingularBoundOn.mono_exponent`: `D^{γ,η'} ⊂ D^{γ,η}` for `η ≤ η'`, with the same
  constant;
* slab-space forms: `Model.SlabSpace.norm_le_of_vanishing`, `Model.SlabSpace.ofLE`.

Without the vanishing bound there is no gain in general: the components of degree `< η − κ` of
an element of `D^{γ,η}` are only bounded, not small.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.1 (proof), Lemma 7.3, Lemma 6.5.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- `w^{a + κ} ≤ r^κ w^{a ∧ 0}` for `0 < w ≤ r`, `w ≤ 1`, `κ ≥ 0`. -/
theorem rpow_add_le_rpow_mul_rpow_min {w r a κ : ℝ} (hw0 : 0 < w) (hwr : w ≤ r) (hw1 : w ≤ 1)
    (hκ : 0 ≤ κ) : w ^ (a + κ) ≤ r ^ κ * w ^ min a 0 := by
  rw [Real.rpow_add hw0, mul_comm]
  exact mul_le_mul (Real.rpow_le_rpow hw0.le hwr hκ)
    (Real.rpow_le_rpow_of_exponent_ge hw0 hw1 (min_le_left a 0)) (Real.rpow_nonneg hw0.le _)
    (Real.rpow_nonneg (hw0.le.trans hwr) _)

/-- `w^{a + κ} ≤ r^κ w^a` for `0 < w ≤ r`, `κ ≥ 0`. -/
theorem rpow_add_le_rpow_mul_rpow {w r a κ : ℝ} (hw0 : 0 < w) (hwr : w ≤ r) (hκ : 0 ≤ κ) :
    w ^ (a + κ) ≤ r ^ κ * w ^ a := by
  rw [Real.rpow_add hw0, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hw0.le hwr hκ) (Real.rpow_nonneg hw0.le _)

/-- On the slab `{ρ ≤ T^{1/𝔰₀}}`: `‖x‖_P ≤ T^{1/𝔰₀}`. -/
theorem singularWeight_le_rpow_inv {E : Type*} {ρ : E → ℝ} {x : E} {T s : ℝ}
    (h : ρ x ≤ T ^ s⁻¹) : singularWeight ρ x ≤ T ^ s⁻¹ :=
  (min_le_right _ _).trans h

/-- `(T^{1/𝔰₀})^κ = T^{κ/𝔰₀}`. -/
theorem rpow_inv_rpow_eq {T s κ : ℝ} (hT : 0 ≤ T) : (T ^ s⁻¹) ^ κ = T ^ (κ / s) := by
  rw [← Real.rpow_mul hT, inv_mul_eq_div]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- **The short-time gain** ([Hai14, proof of Theorem 7.1]). On a slab `S` where `‖x‖_P ≤ r`,
a function with the vanishing bound `|f(x)_i| ≤ C ‖x‖_P^{η + κ − deg i}` and the increment
bound of `D^{γ,η+κ}` with constant `C` satisfies `|||f|||_{γ,η;S} ≤ r^κ C`. -/
theorem singularBoundOn_of_vanishing {ρ : E → ℝ} {γ η κ C r : ℝ} {S : Set E}
    {f : E → ι → ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hS : ∀ x ∈ S, 0 < ρ x → singularWeight ρ x ≤ r)
    (hsup : ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |f x i| ≤ C * singularWeight ρ x ^ (η + κ - 𝒯.deg i))
    (hf : M.SingularBoundOn ρ γ (η + κ) C S f) : M.SingularBoundOn ρ γ η (r ^ κ * C) S f := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have hw0 := singularWeight_pos hρ
    have hexp : η + κ - 𝒯.deg i = (η - 𝒯.deg i) + κ := by ring
    refine (hsup x hx hρ i hi).trans ?_
    rw [hexp, mul_comm (r ^ κ) C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_add_le_rpow_mul_rpow_min hw0 (hS x hx hρ)
      (singularWeight_le_one ρ x) hκ) hC
  · have hw0 : 0 < min (singularWeight ρ x) (singularWeight ρ y) :=
      lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
    have hwr : min (singularWeight ρ x) (singularWeight ρ y) ≤ r :=
      (min_le_left _ _).trans (hS x hx hρx)
    have hexp : η + κ - γ = (η - γ) + κ := by ring
    have hd0 : 0 ≤ K.scaleDist y x ^ (γ - 𝒯.deg j) :=
      Real.rpow_nonneg (K.scaleDist_nonneg _ _) _
    refine (hf.2 x hx y hy hρx hρy hd j hj).trans ?_
    calc C * K.scaleDist y x ^ (γ - 𝒯.deg j) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ (η + κ - γ)
        = C * (K.scaleDist y x ^ (γ - 𝒯.deg j) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ ((η - γ) + κ)) := by
          rw [hexp, mul_assoc]
      _ ≤ C * (K.scaleDist y x ^ (γ - 𝒯.deg j) *
          (r ^ κ * min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (rpow_add_le_rpow_mul_rpow hw0 hwr hκ) hd0) hC
      _ = r ^ κ * C * K.scaleDist y x ^ (γ - 𝒯.deg j) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ) := by ring

/-- **The short-time gain on the time slab** ([Hai14, Theorem 7.1, Lemma 7.3]): if
`ρ ≤ T^{1/𝔰₀}` on `S⁺`, the vanishing bound of order `η + κ` gives
`|||f|||_{γ,η;S} ≤ T^{κ/𝔰₀} C`. -/
theorem singularBoundOn_shortTime {ρ : E → ℝ} {γ η κ C T s : ℝ} {S : Set E} {f : E → ι → ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hT : 0 ≤ T) (hS : ∀ x ∈ S, 0 < ρ x → ρ x ≤ T ^ s⁻¹)
    (hsup : ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |f x i| ≤ C * singularWeight ρ x ^ (η + κ - 𝒯.deg i))
    (hf : M.SingularBoundOn ρ γ (η + κ) C S f) :
    M.SingularBoundOn ρ γ η (T ^ (κ / s) * C) S f := by
  have h := M.singularBoundOn_of_vanishing hκ hC
    (fun x hx hρ => singularWeight_le_rpow_inv (hS x hx hρ)) hsup hf
  rwa [rpow_inv_rpow_eq hT] at h

/-- **Lowering the weight exponent**: `D^{γ,η'} ⊂ D^{γ,η}` for `η ≤ η'`, with the same constant
(all weights are `≤ 1`). -/
theorem SingularBoundOn.mono_exponent {ρ : E → ℝ} {γ η η' C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (hf : M.SingularBoundOn ρ γ η' C S f) (hη : η ≤ η') (hC : 0 ≤ C) :
    M.SingularBoundOn ρ γ η C S f := by
  refine ⟨fun x hx hρ i hi => (hf.1 x hx hρ i hi).trans ?_,
    fun x hx y hy hρx hρy hd j hj => (hf.2 x hx y hy hρx hρy hd j hj).trans ?_⟩
  · refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (singularWeight_pos hρ)
      (singularWeight_le_one ρ x) ?_) hC
    exact min_le_min (by linarith) le_rfl
  · have hw0 : 0 < min (singularWeight ρ x) (singularWeight ρ y) :=
      lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
    have hw1 : min (singularWeight ρ x) (singularWeight ρ y) ≤ 1 :=
      (min_le_left _ _).trans (singularWeight_le_one ρ x)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hw0 hw1 (by linarith))
      (mul_nonneg hC (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))

variable {M} {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ : ℝ} {S : Set E}

/-- Slab-space form of the gain: `‖u‖_{γ,η;S} ≤ T^{κ/𝔰₀} C` when `u` vanishes at `P` to order
`η + κ` with constant `C` and satisfies the increment bound of `D^{γ,η+κ}`. -/
theorem SlabSpace.norm_le_of_vanishing {η κ C T s : ℝ} (u : M.SlabSpace ρ V γ η S)
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hT : 0 ≤ T) (hS : ∀ x ∈ S, 0 < ρ x → ρ x ≤ T ^ s⁻¹)
    (hsup : ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |u.val x i| ≤ C * singularWeight ρ x ^ (η + κ - 𝒯.deg i))
    (hf : M.SingularBoundOn ρ γ (η + κ) C S u.val) : ‖u‖ ≤ T ^ (κ / s) * C :=
  u.norm_le (mul_nonneg (Real.rpow_nonneg hT _) hC) (M.singularBoundOn_shortTime hκ hC hT hS hsup hf)

end Model

end RegularityStructures

end


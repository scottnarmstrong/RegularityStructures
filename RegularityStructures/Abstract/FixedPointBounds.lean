/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularCubeTwoModels
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Order.Filter.AtTopBot.Basic
public import RegularityStructures.Abstract.Model

/-!
# Algebraic and closedness properties of the bounds of `D^{γ,η}_P`

Elementary facts about the predicates `Model.SingularBoundOn` (the bound `|||f|||_{γ,η;S} ≤ C` of
[Hai14, Definition 6.2]) and `Model.SingularDiffBoundOn` (the two-model bound
`|||f; g|||_{γ,η;S} ≤ C`), used to make `D^{γ,η}_P` on a time slab a Banach space
(`RegularityStructures.Abstract.FixedPointSlabSpace`) and in the fixed-point argument of [Hai14,
Theorem 7.8]:

* linearity: `singularBoundOn_zero`, `SingularBoundOn.smul`, `SingularBoundOn.neg`,
  `SingularBoundOn.sub`, `SingularDiffBoundOn.add`, `singularDiffBoundOn_of_singularBoundOn`;
* restriction to subsets: `SingularBoundOn.mono_set`, `SingularDiffBoundOn.mono_set`;
* closedness in the constant: `SingularBoundOn.of_forall_lt`, `SingularDiffBoundOn.of_forall_lt`
  (if the bound holds with every `C' > C` it holds with `C`);
* closedness under pointwise limits: `SingularBoundOn.of_tendsto`.

Source: [Hai14] = arXiv:1303.5113v4, Definition 6.2.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

/-- If `a ≤ C' b` for every `C' > C` and `b ≥ 0`, then `a ≤ C b`. -/
theorem le_mul_of_forall_lt_mul {a b C : ℝ} (hb : 0 ≤ b) (h : ∀ C', C < C' → a ≤ C' * b) :
    a ≤ C * b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hb1 : 0 < b + 1 := by linarith
  have hpos : 0 < ε / (b + 1) := div_pos hε hb1
  have h1 := h (C + ε / (b + 1)) (by linarith)
  have h2 : ε / (b + 1) * b ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb1]
    nlinarith
  have h3 : (C + ε / (b + 1)) * b = C * b + ε / (b + 1) * b := by ring
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem singularBoundOn_zero (ρ : E → ℝ) (γ η : ℝ) (S : Set E) :
    M.SingularBoundOn ρ γ η 0 S 0 :=
  ⟨fun _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ _ => by simp⟩

theorem SingularBoundOn.smul {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η C S f) (c : ℝ) : M.SingularBoundOn ρ γ η (|c| * C) S (c • f) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.1 x hx hρ i hi) (abs_nonneg c)
  · have e : (c • f) y - M.gammaMap y x ((c • f) x) = c • (f y - M.gammaMap y x (f x)) := by
      simp only [Pi.smul_apply, map_smul, smul_sub]
    rw [e, Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    rw [← mul_assoc]
    exact h.2 x hx y hy hρx hρy hd j hj

theorem SingularBoundOn.neg {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η C S f) : M.SingularBoundOn ρ γ η C S (-f) := by
  have h' := h.smul M (-1)
  rw [abs_neg, abs_one, one_mul, neg_one_smul] at h'
  exact h'

/-- The bound `|||f|||_{γ,η;S} ≤ C` is closed in `C`. -/
theorem SingularBoundOn.of_forall_lt {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : ∀ C', C < C' → M.SingularBoundOn ρ γ η C' S f) : M.SingularBoundOn ρ γ η C S f := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · exact le_mul_of_forall_lt_mul (Real.rpow_nonneg (singularWeight_pos hρ).le _)
      fun C' hC' => (h C' hC').1 x hx hρ i hi
  · have hw : 0 ≤ min (singularWeight ρ x) (singularWeight ρ y) :=
      (lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)).le
    rw [mul_assoc]
    refine le_mul_of_forall_lt_mul (mul_nonneg (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
      (Real.rpow_nonneg hw _)) fun C' hC' => ?_
    rw [← mul_assoc]
    exact (h C' hC').2 x hx y hy hρx hρy hd j hj

/-- The bound `|||f|||_{γ,η;S} ≤ C` passes to pointwise limits. -/
theorem SingularBoundOn.of_tendsto {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {F : ℕ → E → ι → ℝ}
    {f : E → ι → ℝ} (hF : ∀ᶠ n in atTop, M.SingularBoundOn ρ γ η C S (F n))
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : M.SingularBoundOn ρ γ η C S f := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have ht : Tendsto (fun n => |F n x i|) atTop (𝓝 |f x i|) :=
      ((continuous_apply i).continuousAt.tendsto.comp (hlim x)).abs
    exact le_of_tendsto ht (hF.mono fun n hn => hn.1 x hx hρ i hi)
  · have hΓ : Continuous (M.gammaMap y x) := LinearMap.continuous_of_finiteDimensional _
    have ht : Tendsto (fun n => |(F n y - M.gammaMap y x (F n x)) j|) atTop
        (𝓝 |(f y - M.gammaMap y x (f x)) j|) :=
      ((continuous_apply j).continuousAt.tendsto.comp
        ((hlim y).sub (hΓ.continuousAt.tendsto.comp (hlim x)))).abs
    exact le_of_tendsto ht (hF.mono fun n hn => hn.2 x hx y hy hρx hρy hd j hj)

/-- A bound with constant `0` forces `f = 0` on `S ∩ {ρ > 0}` in degrees `< γ`. -/
theorem SingularBoundOn.apply_eq_zero {ρ : E → ℝ} {γ η : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η 0 S f) {x : E} (hx : x ∈ S) (hρ : 0 < ρ x) {i : ι}
    (hi : 𝒯.deg i < γ) : f x i = 0 := by
  have := h.1 x hx hρ i hi
  rw [zero_mul] at this
  exact abs_nonpos_iff.1 this

/-- The bound `|||f; g|||_{γ,η;S} ≤ C` is closed in `C`. -/
theorem SingularDiffBoundOn.of_forall_lt {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ} {γ η C : ℝ}
    {S : Set E} {f g : E → ι → ℝ}
    (h : ∀ C', C < C' → M₁.SingularDiffBoundOn M₂ ρ γ η C' S f g) :
    M₁.SingularDiffBoundOn M₂ ρ γ η C S f g := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · exact le_mul_of_forall_lt_mul (Real.rpow_nonneg (singularWeight_pos hρ).le _)
      fun C' hC' => (h C' hC').1 x hx hρ i hi
  · have hw : 0 ≤ min (singularWeight ρ x) (singularWeight ρ y) :=
      (lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)).le
    rw [mul_assoc]
    refine le_mul_of_forall_lt_mul (mul_nonneg (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
      (Real.rpow_nonneg hw _)) fun C' hC' => ?_
    rw [← mul_assoc]
    exact (h C' hC').2 x hx y hy hρx hρy hd j hj

/-- `|||f₁ + f₂; g₁ + g₂||| ≤ |||f₁; g₁||| + |||f₂; g₂|||`. -/
theorem SingularDiffBoundOn.add {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ} {γ η A B : ℝ} {S : Set E}
    {f₁ g₁ f₂ g₂ : E → ι → ℝ} (h₁ : M₁.SingularDiffBoundOn M₂ ρ γ η A S f₁ g₁)
    (h₂ : M₁.SingularDiffBoundOn M₂ ρ γ η B S f₂ g₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ η (A + B) S (f₁ + f₂) (g₁ + g₂) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have e : (f₁ + f₂) x i - (g₁ + g₂) x i = (f₁ x i - g₁ x i) + (f₂ x i - g₂ x i) := by
      simp only [Pi.add_apply]
      ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (h₁.1 x hx hρ i hi) (h₂.1 x hx hρ i hi))
  · have e : ((f₁ + f₂) y - M₁.gammaMap y x ((f₁ + f₂) x)) j -
        ((g₁ + g₂) y - M₂.gammaMap y x ((g₁ + g₂) x)) j =
        ((f₁ y - M₁.gammaMap y x (f₁ x)) j - (g₁ y - M₂.gammaMap y x (g₁ x)) j) +
          ((f₂ y - M₁.gammaMap y x (f₂ x)) j - (g₂ y - M₂.gammaMap y x (g₂ x)) j) := by
      simp only [Pi.add_apply, map_add, Pi.sub_apply]
      ring
    rw [e, add_mul, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (h₁.2 x hx y hy hρx hρy hd j hj)
      (h₂.2 x hx y hy hρx hρy hd j hj))

/-- Two single-model bounds give a two-model bound: `|||f; g||| ≤ |||f||| + |||g|||`. -/
theorem singularDiffBoundOn_of_singularBoundOn {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ} {γ η A B : ℝ}
    {S : Set E} {f g : E → ι → ℝ} (hf : M₁.SingularBoundOn ρ γ η A S f)
    (hg : M₂.SingularBoundOn ρ γ η B S g) : M₁.SingularDiffBoundOn M₂ ρ γ η (A + B) S f g := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · rw [add_mul]
    exact (abs_sub _ _).trans (add_le_add (hf.1 x hx hρ i hi) (hg.1 x hx hρ i hi))
  · rw [add_mul, add_mul]
    exact (abs_sub _ _).trans (add_le_add (hf.2 x hx y hy hρx hρy hd j hj)
      (hg.2 x hx y hy hρx hρy hd j hj))

end Model

end RegularityStructures

end

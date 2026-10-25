/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.RegularityStructureDegrees

/-!
# Modelled distributions

For a model `M = (Π, Γ)` and `γ ∈ ℝ`, a modelled distribution of order `γ` is a measurable
`f : E → T_{<γ}` with

* `|f(x)_i| ≤ C`, and
* `|(f(y) − Γ_{yx} f(x))_j| ≤ C d(y, x)^{γ − deg j}` for `deg j < γ`

([Hai14, Definition 3.1], [Hos25, Definition 3.5] with `p = ∞`, `v = 1`). `ModelledBoundOn`
records these bounds on a set `S`; `modelledDistributions M γ` is the submodule `D^γ` (global
bounds); `modelledNormOn` is the best constant, characterised by `modelledNormOn_le_iff`.
`ModelledDiffBoundOn` is the bound `|||f¹; f²|||` comparing modelled distributions for two
models [Hai14, (3.2)].

Source: [Hai14, Section 3.1], [Hos25, Section 3.3].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The bounds of `D^γ` on `S` with constant `C`: `|f(x)_i| ≤ C` for `deg i < γ` and
`|(f(y) − Γ_{yx} f(x))_j| ≤ C d(y, x)^{γ − deg j}` for `deg j < γ`. -/
def ModelledBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) (f : E → ι → ℝ) : Prop :=
  (∀ x ∈ S, ∀ i, 𝒯.deg i < γ → |f x i| ≤ C) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ j, 𝒯.deg j < γ →
      |(f y - M.gammaMap y x (f x)) j| ≤ C * K.scaleDist y x ^ (γ - 𝒯.deg j)

/-- The space `D^γ` of modelled distributions of order `γ` (global bounds). -/
def modelledDistributions (M : Model 𝒯 K) (γ : ℝ) : Submodule ℝ (E → ι → ℝ) where
  carrier := {f | Measurable f ∧ (∀ x, f x ∈ lowerSubspace 𝒯.deg γ) ∧
    ∃ C, M.ModelledBoundOn γ C univ f}
  add_mem' := by
    rintro f g ⟨hf, hfT, Cf, hf1, hf2⟩ ⟨hg, hgT, Cg, hg1, hg2⟩
    refine ⟨hf.add hg, fun x => Submodule.add_mem _ (hfT x) (hgT x), Cf + Cg, ?_, ?_⟩
    · intro x hx i hi
      simp only [Pi.add_apply]
      exact (abs_add_le _ _).trans (add_le_add (hf1 x hx i hi) (hg1 x hx i hi))
    · intro x hx y hy j hj
      have h : (f + g) y - M.gammaMap y x ((f + g) x) =
          (f y - M.gammaMap y x (f x)) + (g y - M.gammaMap y x (g x)) := by
        simp only [Pi.add_apply, map_add]
        abel
      rw [h, Pi.add_apply, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hf2 x hx y hy j hj) (hg2 x hx y hy j hj))
  zero_mem' := ⟨measurable_const, fun _ => Submodule.zero_mem _, 0,
    fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hfT, Cf, hf1, hf2⟩
    refine ⟨hf.const_smul c, fun x => Submodule.smul_mem _ c (hfT x), |c| * Cf, ?_, ?_⟩
    · intro x hx i hi
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hf1 x hx i hi) (abs_nonneg c)
    · intro x hx y hy j hj
      have h : (c • f) y - M.gammaMap y x ((c • f) x) = c • (f y - M.gammaMap y x (f x)) := by
        simp only [Pi.smul_apply, map_smul, smul_sub]
      rw [h, Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hf2 x hx y hy j hj) (abs_nonneg c)

/-- The norm `|||f|||_{γ;S}` of a modelled distribution: the best constant in
`ModelledBoundOn`. -/
def modelledNormOn (M : Model 𝒯 K) (γ : ℝ) (S : Set E) (f : E → ι → ℝ) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : M.ModelledBoundOn γ C S f), (C : ℝ≥0∞)

/-- The bound `|||f¹; f²|||_{γ;S} ≤ C` comparing `f¹ ∈ D^γ(M₁)` and `f² ∈ D^γ(M₂)`:
`|f¹(x)_i − f²(x)_i| ≤ C` and
`|(f¹(y) − Γ¹_{yx} f¹(x) − f²(y) + Γ²_{yx} f²(x))_j| ≤ C d(y, x)^{γ − deg j}`
[Hai14, (3.2)]. -/
def ModelledDiffBoundOn (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (S : Set E) (f₁ f₂ : E → ι → ℝ) :
    Prop :=
  (∀ x ∈ S, ∀ i, 𝒯.deg i < γ → |f₁ x i - f₂ x i| ≤ C) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ j, 𝒯.deg j < γ →
      |(f₁ y - M₁.gammaMap y x (f₁ x)) j - (f₂ y - M₂.gammaMap y x (f₂ x)) j| ≤
        C * K.scaleDist y x ^ (γ - 𝒯.deg j)

end Model

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem mem_modelledDistributions {γ : ℝ} {f : E → ι → ℝ} :
    f ∈ M.modelledDistributions γ ↔ Measurable f ∧ (∀ x, f x ∈ lowerSubspace 𝒯.deg γ) ∧
      ∃ C, M.ModelledBoundOn γ C univ f :=
  Iff.rfl

theorem ModelledBoundOn.mono {γ C C' : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.ModelledBoundOn γ C S f) (hC : C ≤ C') : M.ModelledBoundOn γ C' S f :=
  ⟨fun x hx i hi => (h.1 x hx i hi).trans hC, fun x hx y hy j hj => (h.2 x hx y hy j hj).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))⟩

theorem ModelledBoundOn.nonneg {γ C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.ModelledBoundOn γ C S f) {x : E} (hx : x ∈ S) {i : ι} (hi : 𝒯.deg i < γ) :
    0 ≤ C :=
  (abs_nonneg _).trans (h.1 x hx i hi)

theorem modelledNormOn_le_iff {γ : ℝ} {S : Set E} {f : E → ι → ℝ} (C : ℝ≥0) :
    M.modelledNormOn γ S f ≤ C ↔ M.ModelledBoundOn γ C S f := by
  refine iInf_nnreal_le_iff (P := fun C : ℝ≥0 => M.ModelledBoundOn γ C S f)
    (fun _ _ hab h => h.mono M (by exact_mod_cast hab)) (fun c hc => ⟨?_, ?_⟩) C
  · intro x hx i hi
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    exact (hc ⟨δ, hδ.le⟩ hδ).1 x hx i hi
  · intro x hx y hy j hj
    exact le_mul_of_forall_pos_le_add_mul (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
      fun ε hε => (hc ε hε).2 x hx y hy j hj

/-- Components of a modelled distribution of degree `≥ γ` vanish. -/
theorem apply_eq_zero_of_mem {γ : ℝ} {f : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ)
    (x : E) {i : ι} (hi : γ ≤ 𝒯.deg i) : f x i = 0 :=
  hf.2.1 x i hi

end Model

end RegularityStructures

end

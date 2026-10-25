/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointSlabSpace
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Abstract.Model

/-!
# A constant vector on the time slab as a singular modelled distribution

[Hai14, Definition 6.2, Section 7.3]. For a vector `c ∈ T` fixed by every `Γ_{yx}` of the model,
the function `slabConst T c = c · 1_{(0, T] × ℝ³}` is a singular modelled distribution on the time
slab `(0, T] × ℝ³` for **every** weight exponent `η` and every model: its increments vanish, and
the weight `‖x‖_P ≤ 1` is raised to a nonpositive power `min (η - deg i) 0`, so the sup bound holds
with the constant `sup_i |c i|`.  Consequently `slabConstElem` is an element of the slab space with
norm at most `sup_i |c i|`, and the comparison of `slabConst T c + f` with `slabConst T c + g` for
two models fixing `c` reduces to the comparison of `f` and `g`.

The `Φ⁴₃` application (`c = e_Ψ`) is in `Phi43.Inhomogeneity.Psi`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant vector `c` on the time slab `(0, T] × ℝ³`, and `0` elsewhere. -/
def slabConst (T : ℝ) (c : ι → ℝ) : ParabolicSpace → ι → ℝ :=
  (timeSlab T).indicator fun _ => c
end RegularityStructures.Inhomogeneity

end

public section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem slabConst_of_mem {T : ℝ} (c : ι → ℝ) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    slabConst T c x = c :=
  indicator_of_mem hx _

omit [Fintype ι] [DecidableEq ι] in
theorem slabConst_of_notMem {T : ℝ} (c : ι → ℝ) {x : ParabolicSpace} (hx : x ∉ timeSlab T) :
    slabConst T c x = 0 :=
  indicator_of_notMem hx _

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_slabConst (T : ℝ) (c : ι → ℝ) : Measurable (slabConst T c) :=
  measurable_const.indicator (measurableSet_timeSlab T)

theorem timeZeroDist_pos_of_mem_timeSlab {T : ℝ} {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    0 < timeZeroDist x :=
  Real.sqrt_pos.2 (abs_pos.2 hx.1.ne')

/-- **A `Γ`-fixed constant is a singular modelled distribution** with constant `C ≥ sup |c i|`,
for every exponent `η`. -/
theorem singularBoundOn_slabConst {𝒯 : RegularityStructure ι}
    (M : Model 𝒯 parabolicSemigroup) {γ η C : ℝ} (T : ℝ) {c : ι → ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, |c i| ≤ C) (hΓ : ∀ x y : ParabolicSpace, M.gammaMap y x c = c) :
    M.SingularBoundOn timeZeroDist γ η C (timeSlab T) (slabConst T c) := by
  refine ⟨fun x hx hρ i _ => ?_, fun x hx y hy hρx hρy _ j _ => ?_⟩
  · rw [slabConst_of_mem c hx]
    have h1 : 1 ≤ singularWeight timeZeroDist x ^ min (η - 𝒯.deg i) 0 :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (singularWeight_pos hρ)
        (singularWeight_le_one _ _) (min_le_right _ _)
    calc |c i| ≤ C := hc i
      _ = C * 1 := (mul_one C).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hC
  · rw [slabConst_of_mem c hx, slabConst_of_mem c hy, hΓ x y, sub_self, Pi.zero_apply, abs_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _))
      (Real.rpow_nonneg (le_min (singularWeight_pos hρx).le (singularWeight_pos hρy).le) _)
end RegularityStructures.Inhomogeneity

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The singular modelled distribution `c · 1_{(0,T]×ℝ³}` as an element of the slab space. -/
def slabConstElem {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup) (T : ℝ)
    {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} (c : ι → ℝ) (hc : c ∈ V ⊓ lowerSubspace 𝒯.deg γ)
    (hΓ : ∀ x y : ParabolicSpace, M.gammaMap y x c = c) :
    M.SlabSpace timeZeroDist V γ η (timeSlab T) :=
  Model.SlabSpace.mk (slabConst T c)
    ⟨measurable_slabConst T c, fun x hx _ => by rwa [slabConst_of_mem c hx],
      fun x hx => slabConst_of_notMem c fun h => hx ⟨h, timeZeroDist_pos_of_mem_timeSlab h⟩,
      ∑ i, |c i|, singularBoundOn_slabConst M T (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (fun i => Finset.single_le_sum (f := fun i => |c i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)) hΓ⟩
end RegularityStructures.Inhomogeneity

end

public section

open MeasureTheory Set

namespace RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The norm of the constant element is at most any `C ≥ sup |c i|`. -/
theorem norm_slabConstElem_le {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup)
    (T : ℝ) {V : Submodule ℝ (ι → ℝ)} {γ η C : ℝ} (c : ι → ℝ)
    (hc : c ∈ V ⊓ lowerSubspace 𝒯.deg γ) (hΓ : ∀ x y : ParabolicSpace, M.gammaMap y x c = c)
    (hC : 0 ≤ C) (hcC : ∀ i, |c i| ≤ C) :
    ‖slabConstElem (η := η) M T c hc hΓ‖ ≤ C :=
  M.slabNorm_le (singularBoundOn_slabConst M T hC hcC hΓ) hC

/-- **Two-model comparison**: adding the same `Γ`-fixed constant to both arguments does not change
the comparison norm. -/
theorem singularDiffBoundOn_slabConst_add {𝒯 : RegularityStructure ι}
    {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ η C T : ℝ} {c : ι → ℝ}
    (h₁ : ∀ x y : ParabolicSpace, M₁.gammaMap y x c = c)
    (h₂ : ∀ x y : ParabolicSpace, M₂.gammaMap y x c = c) {f g : ParabolicSpace → ι → ℝ}
    (h : M₁.SingularDiffBoundOn M₂ timeZeroDist γ η C (timeSlab T) f g) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist γ η C (timeSlab T)
      (slabConst T c + f) (slabConst T c + g) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · simpa using h.1 x hx hρ i hi
  · have key : ((slabConst T c + f) y - M₁.gammaMap y x ((slabConst T c + f) x)) -
        ((slabConst T c + g) y - M₂.gammaMap y x ((slabConst T c + g) x)) =
        (f y - M₁.gammaMap y x (f x)) - (g y - M₂.gammaMap y x (g x)) := by
      simp only [Pi.add_apply, slabConst_of_mem c hx, slabConst_of_mem c hy, map_add, h₁ x y,
        h₂ x y]
      abel
    rw [← Pi.sub_apply, key, Pi.sub_apply]
    exact h.2 x hx y hy hρx hρy hd j hj
/-- **Two-model comparison of the constant with itself** vanishes. -/
theorem singularDiffBoundOn_slabConst_self {𝒯 : RegularityStructure ι}
    {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ η T : ℝ} {c : ι → ℝ}
    (h₁ : ∀ x y : ParabolicSpace, M₁.gammaMap y x c = c)
    (h₂ : ∀ x y : ParabolicSpace, M₂.gammaMap y x c = c) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist γ η 0 (timeSlab T) (slabConst T c) (slabConst T c) := by
  have h0 : M₁.SingularDiffBoundOn M₂ timeZeroDist γ η 0 (timeSlab T) (0 : ParabolicSpace → ι → ℝ)
      0 := by
    refine ⟨fun x hx hρ i _ => ?_, fun x hx y hy hρx hρy _ j _ => ?_⟩
    · simp
    · simp
  have := singularDiffBoundOn_slabConst_add (c := c) h₁ h₂ h0
  simpa using this

end RegularityStructures.Inhomogeneity

end

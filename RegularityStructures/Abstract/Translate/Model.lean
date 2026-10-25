/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Translating a model

For `a : ParabolicSpace`, the translate `M.translate a` of a model `M` for the parabolic
semigroup has `Π^a_x = Π_{x+a}(· + a)` and `Γ^a_{xy} = Γ_{x+a,y+a}`. This uses that the kernel
of `parabolicSemigroup` depends only on `x - y`, so that the semigroup commutes with translations
(`parabolicSemigroup_apply_translate`) and translations preserve `Q`-distributions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

namespace RegularisingSemigroup

instance instIsAddRightInvariantVolumeParabolicSpace :
    (volume : Measure ParabolicSpace).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The translation `Λ ↦ Λ(· + a)` of a `Q`-distribution for the parabolic semigroup. -/
def translateDistr (a : ParabolicSpace) :
    parabolicSemigroup.distributions →ₗ[ℝ] parabolicSemigroup.distributions where
  toFun Λ := ⟨fun t z => (Λ : ℝ → ParabolicSpace → ℝ) t (z + a), by
    obtain ⟨h0, h⟩ := Λ.2
    refine ⟨fun t ht => by funext z; simp [h0 ht], fun s t hs ht x => ?_⟩
    obtain ⟨hi, he⟩ := h hs ht (x + a)
    have hk : ∀ y : ParabolicSpace, parabolicSemigroup.kernel s (x + a) (y + a) =
        parabolicSemigroup.kernel s x y := fun y => by
      simp [parabolicSemigroup]
    refine ⟨?_, ?_⟩
    · have := hi.comp_add_right a
      simpa only [hk] using this
    · simp only [RegularisingSemigroup.apply, parabolicSemigroup] at he ⊢
      rw [← he, ← integral_add_right_eq_self
        (fun y => parabolicKernel s (x + a - y) * (Λ : ℝ → ParabolicSpace → ℝ) t y) a]
      simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RegularisingSemigroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- The translate of a model: `Π^a_x = Π_{x+a}(· + a)`, `Γ^a_{xy} = Γ_{x+a,y+a}`. -/
def translate (M : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace) :
    Model 𝒯 parabolicSemigroup where
  pi x := RegularisingSemigroup.translateDistr a ∘ₗ M.pi (x + a)
  gamma x y := M.gamma (x + a) (y + a)
  pi_gamma x y τ := by
    have := M.pi_gamma (x + a) (y + a) τ
    simpa using congrArg (RegularisingSemigroup.translateDistr a) this
  gamma_self x := M.gamma_self _
  gamma_mul x y z := M.gamma_mul _ _ _
  measurable_diag i t ht :=
    (M.measurable_diag i ht).comp (measurable_id.add_const a)
  measurable_pi x i t ht := (M.measurable_pi (x + a) i ht).comp (measurable_id.add_const a)

variable (M : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace)

@[simp]
theorem regPi_translate (x : ParabolicSpace) (τ : ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    (M.translate a).regPi x τ t z = M.regPi (x + a) τ t (z + a) := rfl

@[simp]
theorem gammaMap_translate (x y : ParabolicSpace) :
    (M.translate a).gammaMap x y = M.gammaMap (x + a) (y + a) := rfl

theorem parabolicSemigroup_scaleDist_translate (x y : ParabolicSpace) :
    parabolicSemigroup.scaleDist (y + a) (x + a) = parabolicSemigroup.scaleDist y x := by
  simp [parabolicSemigroup]

/-- Translation covariance of the `Π`-bound, on translated sets. -/
theorem piBoundOn_translate_iff {γ C : ℝ} {S : Set ParabolicSpace} :
    (M.translate a).PiBoundOn γ C S ↔ M.PiBoundOn γ C ((· + a) '' S) := by
  constructor
  · intro h i hi t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h i hi t ht y hy
  · intro h i hi t ht x hx
    exact h i hi t ht (x + a) ⟨x, hx, rfl⟩

variable (M₂ : Model 𝒯 parabolicSemigroup)

theorem piDiffBoundOn_translate_iff {γ C : ℝ} {S : Set ParabolicSpace} :
    (M.translate a).PiDiffBoundOn (M₂.translate a) γ C S ↔
      M.PiDiffBoundOn M₂ γ C ((· + a) '' S) := by
  constructor
  · intro h i hi t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h i hi t ht y hy
  · intro h i hi t ht x hx
    exact h i hi t ht (x + a) ⟨x, hx, rfl⟩

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Translate.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Translation covariance of pairings, `J`, the germ and realisation

For the translate `M.translate a` (`RegularityStructures.Abstract.Translate.Model`):

* `parabolicSemigroup_apply_translate`, `pairing_translate`: `Q_t` and the pairing commute with
  translation of both arguments;
* `jCoeffP_translate`, `jVecP_translate`, `jMapP_translate`, `realGermP_translate`, and the
  non-profile versions;
* `isPolyCompatible_translate`, `realisesKernelP_translate`, `isRealisingP_translate`;
* `isJointMeasurable_translate`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem parabolicSemigroup_apply_translate (a : ParabolicSpace) (t : ℝ) (g : ParabolicSpace → ℝ)
    (z : ParabolicSpace) :
    parabolicSemigroup.apply t (fun y => g (y + a)) z = parabolicSemigroup.apply t g (z + a) := by
  simp only [RegularisingSemigroup.apply, parabolicSemigroup]
  rw [← integral_add_right_eq_self
    (fun y => parabolicKernel t (z + a - y) * g y) a]
  simp

/-- The pairing is invariant under translating both the distribution and the test function. -/
theorem pairing_translate (a : ParabolicSpace) (Λ : ℝ → ParabolicSpace → ℝ)
    (φ : ParabolicSpace → ℝ) :
    parabolicSemigroup.pairing (fun t z => Λ t (z + a)) (fun z => φ (z + a)) =
      parabolicSemigroup.pairing Λ φ := by
  unfold RegularisingSemigroup.pairing
  congr 1
  funext s
  exact integral_add_right_eq_self (fun y => Λ s y * φ y) a

theorem polyEval_translate (a x : ParabolicSpace) {N : ℕ} (τ : PolyIndex N → ℝ)
    (y : ParabolicSpace) : polyEval (x + a) τ (y + a) = polyEval x τ y := by
  simp [polyEval]

theorem polyReg_translate (a x : ParabolicSpace) {N : ℕ} (τ : PolyIndex N → ℝ) (t : ℝ)
    (z : ParabolicSpace) : polyReg (x + a) τ t (z + a) = polyReg x τ t z := by
  unfold polyReg
  split_ifs with ht
  · rw [← parabolicSemigroup_apply_translate]
    simp only [polyEval_translate]
  · rfl

theorem taylorKernel_translate (a : ParabolicSpace) (h : ParabolicSpace → ℝ) (n : ℕ) (σ : ℝ)
    (x y w : ParabolicSpace) :
    taylorKernel h n σ (x + a) (y + a) (w + a) = taylorKernel h n σ x y w := by
  simp [taylorKernel]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (M : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace)

theorem realGermP_translate (h : ParabolicSpace → ℝ) (x : ParabolicSpace) (i : ι)
    (y : ParabolicSpace) :
    realGermP (M.translate a) h x i y = realGermP M h (x + a) i (y + a) := by
  unfold realGermP
  congr 1
  funext n
  rw [← pairing_translate a (fun t z => M.regPi (x + a) (Pi.single i 1) t z)
    (taylorKernel h n (𝒯.deg i + 2) (x + a) (y + a))]
  simp [taylorKernel_translate]

theorem realRegP_translate (h : ParabolicSpace → ℝ) (x : ParabolicSpace) (i : ι) (t : ℝ)
    (z : ParabolicSpace) :
    realRegP (M.translate a) h x i t z = realRegP M h (x + a) i t (z + a) := by
  unfold realRegP
  split_ifs with ht
  · have : realGermP (M.translate a) h x i = fun y => realGermP M h (x + a) i (y + a) :=
      funext (realGermP_translate M a h x i)
    rw [this, parabolicSemigroup_apply_translate]
  · rfl

theorem isPolyCompatible_translate {N' : ℕ} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) : (M.translate a).IsPolyCompatible P := by
  intro x k t z
  rw [regPi_translate, hM, polyReg_translate]

theorem realisesKernelP_translate {h : ParabolicSpace → ℝ} {γ : ℝ}
    {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)} (hM : M.RealisesKernelP h γ I V) :
    (M.translate a).RealisesKernelP h γ I V := by
  intro x i hi hV t ht z
  rw [regPi_translate, hM (x + a) i hi hV t ht, realRegP_translate]

theorem isRealisingP_translate {h : ParabolicSpace → ℝ} {γ : ℝ} {N' : ℕ}
    {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hM : M.IsRealisingP h γ P I V) : (M.translate a).IsRealisingP h γ P I V :=
  ⟨realisesKernelP_translate M a hM.realises, isPolyCompatible_translate M a hM.poly⟩

theorem isJointMeasurable_translate (hM : M.IsJointMeasurable) :
    (M.translate a).IsJointMeasurable := fun i t ht =>
  (hM i t ht).comp ((measurable_fst.add_const a).prodMk (measurable_snd.add_const a))

end Model

end RegularityStructures

end

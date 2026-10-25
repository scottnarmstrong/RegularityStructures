/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.PairingLinear
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Integration.Sector.Commute
public import RegularityStructures.Analysis.Heat.Schauder.TaylorTy
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The `J`-coefficients and germs of the difference model

For the profile `h` (`ShellProfile h N`) and `Π⊕ = λ⁻¹ (Π¹ - Π²) ⊕ Π²`:

* `jCoeffP_modelSum_inl`: `jCoeffP M⊕ h x (inl j) k = λ⁻¹ (jCoeffP M₁ h x j k - jCoeffP M₂ h x j k)`
  for `|k|_𝔰 < deg j + 2`, `deg j < γ`;
* `jCoeffP_modelSum_inr`: `jCoeffP M⊕ h x (inr j) k = jCoeffP M₂ h x j k`;
* `realGermP_modelSum_inl`, `realGermP_modelSum_inr`: the same for the germs `realGermP`, which
  determine `Π⊕_x I⊕ e` (`RegularityStructures.Abstract.Singular.TwoModel.Realising`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem continuous_taylorKernel_right {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (n : ℕ)
    (σ : ℝ) (x y : ParabolicSpace) : Continuous (taylorKernel h n σ x y) :=
  (continuous_taylorKernel_uncurry h0 n σ x).comp (continuous_const.prodMk continuous_id)

theorem hasCompactSupport_taylorKernel {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (n : ℕ) (σ : ℝ) (x y : ParabolicSpace) :
    HasCompactSupport (taylorKernel h n σ x y) := by
  have hg := contDiff_scaledShell h0 n
  have hhs : HasCompactSupport (scaledShell h n) := hasCompactSupport_scaledShell hs n
  have h1 : HasCompactSupport fun w => scaledShell h n (y - w) := hasCompactSupport_reflect hhs y
  have h2 : HasCompactSupport fun w => ∑ k ∈ taylorIdx σ,
      (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
        lineIter (multiDirs k) (scaledShell h n) (x - w) :=
    hasCompactSupport_finset_sum' _ fun k _ =>
      (hasCompactSupport_reflect (hasCompactSupport_lineIter hhs _) x).mul_left
  exact h1.sub h2

namespace TwoModel

variable {N' : ℕ} {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {h : ParabolicSpace → ℝ} {N : ℕ}

theorem jCoeffP_modelSum_inr (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (j : ι)
    (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) :
    jCoeffP (modelSum (lam := lam) h₁ h₂) h x (Sum.inr j) k = jCoeffP M₂ h x j k := by
  unfold jCoeffP
  exact tsum_congr fun n => pairing_modelSum_inr h₁ h₂ j x _

theorem realGermP_modelSum_inr (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (j : ι)
    (x y : ParabolicSpace) :
    realGermP (modelSum (lam := lam) h₁ h₂) h x (Sum.inr j) y = realGermP M₂ h x j y := by
  unfold realGermP
  exact tsum_congr fun n => pairing_modelSum_inr h₁ h₂ j x _

end TwoModel

end RegularityStructures

end

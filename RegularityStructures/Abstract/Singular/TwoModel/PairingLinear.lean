/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Sector
public import RegularityStructures.Abstract.Integration.Lipschitz.Coeff
public import RegularityStructures.Abstract.Profile.RealGerm
public import RegularityStructures.Abstract.Model

/-!
# Pairings of the difference model are differences of pairings

For `Λ⊕ = λ⁻¹ (Λ¹ - Λ²)` (the `Q`-family `Π⊕_x e_{inl j}`) and a test function `φ` continuous with
compact support for which the regularised integrals of `Λ¹`, `Λ²` converge,
`⟨Λ⊕, φ⟩ = λ⁻¹ (⟨Λ¹, φ⟩ - ⟨Λ², φ⟩)` (`pairing_modelSum_inl`); `⟨Π⊕_x e_{inr j}, φ⟩ = ⟨Π²_x e_j, φ⟩`.
Consequences:

* `jCoeffP_modelSum_inl`, `jCoeffP_modelSum_inr`: the coefficients of `J⊕`;
* `realGermP_modelSum_inl`, `realGermP_modelSum_inr`: the germs of `Π⊕ I⊕ e`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

namespace TwoModel

theorem pairing_mul_sub_of_tendsto {Λ Λ' : ℝ → ParabolicSpace → ℝ} {φ : ParabolicSpace → ℝ}
    (c : ℝ) (hi : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable (fun y => Λ s y * φ y))
    (hi' : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable (fun y => Λ' s y * φ y))
    (h : Tendsto (fun s => ∫ y, Λ s y * φ y) (𝓝[>] 0) (𝓝 (parabolicSemigroup.pairing Λ φ)))
    (h' : Tendsto (fun s => ∫ y, Λ' s y * φ y) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing Λ' φ))) :
    parabolicSemigroup.pairing (fun t z => c * (Λ t z - Λ' t z)) φ =
      c * (parabolicSemigroup.pairing Λ φ - parabolicSemigroup.pairing Λ' φ) := by
  refine parabolicSemigroup.pairing_eq_of_tendsto (((h.sub h').const_mul c).congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs
  have hs' : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
  have e : (fun y => c * (Λ s y - Λ' s y) * φ y) =
      fun y => c * (Λ s y * φ y - Λ' s y * φ y) := by
    funext y; ring
  rw [e, integral_const_mul, integral_sub (hi s hs') (hi' s hs')]

end TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace TwoModel

variable {N' : ℕ} {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

/-- The pairing of `Π⊕_x e_{inl j}` with a test function is the difference of the pairings. -/
theorem pairing_modelSum_inl (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (j : NonPoly P) (x : ParabolicSpace) {φ : ParabolicSpace → ℝ}
    (hi₁ : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun y => M₁.regPi x (Pi.single j.1 1) s y * φ y)
    (hi₂ : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun y => M₂.regPi x (Pi.single j.1 1) s y * φ y)
    (t₁ : Tendsto (fun s => ∫ y, M₁.regPi x (Pi.single j.1 1) s y * φ y) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing (fun t y => M₁.regPi x (Pi.single j.1 1) t y) φ)))
    (t₂ : Tendsto (fun s => ∫ y, M₂.regPi x (Pi.single j.1 1) s y * φ y) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing (fun t y => M₂.regPi x (Pi.single j.1 1) t y) φ))) :
    parabolicSemigroup.pairing
        (fun t y => (modelSum (lam := lam) h₁ h₂).regPi x (Pi.single (Sum.inl j) 1) t y) φ =
      lam⁻¹ * (parabolicSemigroup.pairing (fun t y => M₁.regPi x (Pi.single j.1 1) t y) φ -
        parabolicSemigroup.pairing (fun t y => M₂.regPi x (Pi.single j.1 1) t y) φ) := by
  have e : (fun t y => (modelSum (lam := lam) h₁ h₂).regPi x (Pi.single (Sum.inl j) 1) t y) =
      fun t y => lam⁻¹ * (M₁.regPi x (Pi.single j.1 1) t y - M₂.regPi x (Pi.single j.1 1) t y) :=
    funext fun t => funext fun y => by
      rw [regPi_modelSum]
      exact coe_piSum_single_inl x j t y
  rw [e]
  exact pairing_mul_sub_of_tendsto _ hi₁ hi₂ t₁ t₂

/-- The pairing of `Π⊕_x e_{inr j}` is that of `Π²_x e_j`. -/
theorem pairing_modelSum_inr (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (j : ι) (x : ParabolicSpace) (φ : ParabolicSpace → ℝ) :
    parabolicSemigroup.pairing
        (fun t y => (modelSum (lam := lam) h₁ h₂).regPi x (Pi.single (Sum.inr j) 1) t y) φ =
      parabolicSemigroup.pairing (fun t y => M₂.regPi x (Pi.single j 1) t y) φ := by
  congr 1
  funext t y
  rw [regPi_modelSum]
  exact coe_piSum_single_inr x j t y

end TwoModel

end RegularityStructures

end

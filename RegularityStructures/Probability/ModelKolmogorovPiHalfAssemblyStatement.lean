/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyTranslate

/-!
# The `Π` half statement and the translation of its hypotheses

`PiHalfPrem` collects the eight deterministic and moment premises of the `Π` half of
`kolmogorov_modelNorm_of_halves`, and `PiHalfStmt` is that half itself (with the premises curried,
exactly as in `kolmogorov_modelNorm_of_halves`). `PiHalfPrem.translate` transports the premises to
translated random models, which is the only place where translation invariance of the hypotheses
(all are `∀ x` / `∀ x y` statements) is used.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The eight deterministic / moment premises of the `Π` half. -/
structure PiHalfPrem (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (qPi : ℕ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ) : Prop where
  detPi : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
    ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
      ∀ x : ParabolicSpace,
      |(Z ω).regPi x (Pi.single i 1) t x| ≤
        C * t ^ (𝒯.deg i / parabolicSemigroup.order)
  detPiDiff : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
    ∀ x : ParabolicSpace,
    |(Z₁ ω).regPi x (Pi.single i 1) t x -
        (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
      C * ε ^ θ * t ^ (𝒯.deg i / parabolicSemigroup.order)
  detGamma : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
    ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
      ∀ x y : ParabolicSpace,
      |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)
  detGammaDiff : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
    ∀ x y : ParabolicSpace,
    |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
        (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
      C * ε ^ θ * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)
  momPi : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
    ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
      ∀ x : ParabolicSpace,
      ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
        ENNReal.ofReal (C * t ^ ((𝒯.deg i + κbar) / parabolicSemigroup.order)) ^ qPi
  momPiDiff : ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
    ∀ x : ParabolicSpace,
    ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x -
        (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
      ENNReal.ofReal (C * ε ^ θ *
        t ^ ((𝒯.deg i + κbar) / parabolicSemigroup.order)) ^ qPi
  momGamma : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
    ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ x y : ParabolicSpace,
      ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi
  momGammaDiff : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
    ∀ x y : ParabolicSpace,
    ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
        (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
      ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi

/-- The `Π` half of `kolmogorov_modelNorm_of_halves` for the compact set `S`, with the
constants `qPi`, `KPi` as parameters (premises curried exactly as there). -/
@[expose] def PiHalfStmt (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (S : Set ParabolicSpace) (p qPi : ℕ) (KPi : ℝ → ℝ) : Prop :=
  ∀ (Cbar : ℝ),
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ),
        0 ≤ C → C ≤ Cbar → 0 ≤ ε →
        IsContinuousRandomModelWithFieldsOn Z₁ S →
        IsContinuousRandomModelWithFieldsOn Z₂ S →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
            ∀ x : ParabolicSpace,
            |(Z ω).regPi x (Pi.single i 1) t x| ≤
              C * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          |(Z₁ ω).regPi x (Pi.single i 1) t x -
              (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
            C * ε ^ θ * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
            ∀ x y : ParabolicSpace,
            |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
              C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j)) →
        (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : ParabolicSpace,
          |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
            C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j)) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal
              (C * t ^ ((𝒯.deg i + κbar) /
                parabolicSemigroup.order)) ^ qPi) →
        (∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x -
              (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal (C * ε ^ θ *
              t ^ ((𝒯.deg i + κbar) / parabolicSemigroup.order)) ^ qPi) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
            ∀ x y : ParabolicSpace,
            ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi) →
        (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          AEMeasurable (fun ω => (Z ω).piNormOn γ S) P ∧
            ∫⁻ ω, (Z ω).piNormOn γ S ^ p ∂P ≤
            ENNReal.ofReal (KPi Cbar * C ^ p)) ∧
        AEMeasurable (fun ω => (Z₁ ω).piDiffNormOn (Z₂ ω) γ S) P ∧
        ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤
          ENNReal.ofReal (KPi Cbar * (C * ε ^ θ) ^ p)

variable {𝒯 : RegularityStructure ι} {γ κbar θ : ℝ} {Dπ : Set ι} {DΓ : Set (ι × ι)} {qPi : ℕ}
  {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup} {C ε : ℝ}

omit [MeasurableSpace Ω] in
private theorem exists_translate_of_mem {a : ParabolicSpace}
    {Z : Ω → Model 𝒯 parabolicSemigroup}
    (hZ : Z ∈ ({fun ω => (Z₁ ω).translate a, fun ω => (Z₂ ω).translate a} :
      Set (Ω → Model 𝒯 parabolicSemigroup))) :
    ∃ Z₀ ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      Z = fun ω => (Z₀ ω).translate a := by
  rcases hZ with rfl | hZ
  · exact ⟨Z₁, by simp, rfl⟩
  · rw [mem_singleton_iff] at hZ
    exact ⟨Z₂, by simp, hZ⟩

/-- All premises of the `Π` half transport to translated models. -/
theorem PiHalfPrem.translate (h : PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε)
    (a : ParabolicSpace) :
    PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P (fun ω => (Z₁ ω).translate a)
      (fun ω => (Z₂ ω).translate a) C ε where
  detPi Z hZ i hi hγ ω t ht x := by
    obtain ⟨Z₀, h₀, rfl⟩ := exists_translate_of_mem hZ
    exact h.detPi Z₀ h₀ i hi hγ ω t ht (x + a)
  detPiDiff i hi hγ ω t ht x := h.detPiDiff i hi hγ ω t ht (x + a)
  detGamma Z hZ i j hij hγ hj ω x y := by
    obtain ⟨Z₀, h₀, rfl⟩ := exists_translate_of_mem hZ
    have := h.detGamma Z₀ h₀ i j hij hγ hj ω (x + a) (y + a)
    rw [Model.parabolicSemigroup_scaleDist_translate a x y] at this
    exact this
  detGammaDiff i j hij hγ hj ω x y := by
    have := h.detGammaDiff i j hij hγ hj ω (x + a) (y + a)
    rw [Model.parabolicSemigroup_scaleDist_translate a x y] at this
    exact this
  momPi Z hZ i hi hγ t ht x := by
    obtain ⟨Z₀, h₀, rfl⟩ := exists_translate_of_mem hZ
    exact h.momPi Z₀ h₀ i hi hγ t ht (x + a)
  momPiDiff i hi hγ t ht x := h.momPiDiff i hi hγ t ht (x + a)
  momGamma Z hZ i j hij hγ hj x y := by
    obtain ⟨Z₀, h₀, rfl⟩ := exists_translate_of_mem hZ
    have := h.momGamma Z₀ h₀ i j hij hγ hj (x + a) (y + a)
    rw [Model.parabolicSemigroup_scaleDist_translate a x y] at this
    exact this
  momGammaDiff i j hij hγ hj x y := by
    have := h.momGammaDiff i j hij hγ hj (x + a) (y + a)
    rw [Model.parabolicSemigroup_scaleDist_translate a x y] at this
    exact this

end RegularityStructures

end

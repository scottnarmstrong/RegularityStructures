/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyStatement
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyMoments
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyDiffDyadic
public import RegularityStructures.Probability.ModelKolmogorovPiHalfFactorBound
public import RegularityStructures.Probability.ModelKolmogorovFieldNormMeasurable

/-!
# Support lemmas for the concrete `Π` half assembly

The envelope index, conversion of `PiHalfPrem` to the hypothesis bundles of the cell-weight
moment bounds, the lowering of `Γ`-moments, real constants from `Γ`-norms, and moments of `1 + G`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An envelope index large enough for all cell-weight moment bounds. -/
theorem exists_piHalfEnvIndex (𝒯 : RegularityStructure ι) {κ : ℝ} (hκ : 0 < κ) (q : ℕ)
    (hq : 1 ≤ q) :
    ∃ N : ℕ, 1 < N ∧ (∀ k j, 𝒯.deg j ≤ 𝒯.deg k → (𝒯.deg k - 𝒯.deg j + κ) * q + 1 < N) ∧
      (∀ k j, 𝒯.deg j ≤ 𝒯.deg k → 𝒯.deg k - 𝒯.deg j + 1 < N) := by
  set B : ℝ := ∑ x : ι × ι, |(𝒯.deg x.1 - 𝒯.deg x.2 + κ) * q| + 2 with hB
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ x : ι × ι, |(𝒯.deg x.1 - 𝒯.deg x.2 + κ) * q| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hB]; linarith
  have hceil : 0 < ⌈B⌉₊ := Nat.ceil_pos.2 hBpos
  refine ⟨⌈B⌉₊ + 1, by omega, fun k j hjk => ?_, fun k j hjk => ?_⟩
  · have h1 : |(𝒯.deg k - 𝒯.deg j + κ) * q| ≤ ∑ x : ι × ι, |(𝒯.deg x.1 - 𝒯.deg x.2 + κ) * q| :=
      Finset.single_le_sum (f := fun x : ι × ι => |(𝒯.deg x.1 - 𝒯.deg x.2 + κ) * q|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (k, j))
    have h2 := Nat.le_ceil B
    have h3 := le_abs_self ((𝒯.deg k - 𝒯.deg j + κ) * q)
    have : (((⌈B⌉₊ + 1 : ℕ)) : ℝ) = ⌈B⌉₊ + 1 := by push_cast; ring
    rw [this]; linarith
  · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h0 : 0 ≤ 𝒯.deg k - 𝒯.deg j := by linarith
    have h1 : |(𝒯.deg k - 𝒯.deg j + κ) * q| ≤ ∑ x : ι × ι, |(𝒯.deg x.1 - 𝒯.deg x.2 + κ) * q| :=
      Finset.single_le_sum (f := fun x : ι × ι => |(𝒯.deg x.1 - 𝒯.deg x.2 + κ) * q|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (k, j))
    have h2 := Nat.le_ceil B
    have h3 := le_abs_self ((𝒯.deg k - 𝒯.deg j + κ) * q)
    have h4 : 𝒯.deg k - 𝒯.deg j ≤ (𝒯.deg k - 𝒯.deg j + κ) * q := by nlinarith
    have : (((⌈B⌉₊ + 1 : ℕ)) : ℝ) = ⌈B⌉₊ + 1 := by push_cast; ring
    rw [this]; linarith

variable {𝒯 : RegularityStructure ι} {γ κbar θ : ℝ} {Dπ : Set ι} {DΓ : Set (ι × ι)} {qPi : ℕ}
  {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup} {C ε : ℝ}

theorem PiHalfPrem.toSingle (h : PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε)
    {Z : Ω → Model 𝒯 parabolicSemigroup}
    (hZ : Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup))) :
    PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z C where
  piDet := h.detPi Z hZ
  gammaDet := h.detGamma Z hZ
  piAnn := h.momPi Z hZ
  gammaAnn := h.momGamma Z hZ

theorem PiHalfPrem.toDiff (h : PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε) :
    PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε where
  piDet := h.detPiDiff
  gammaDet := h.detGammaDiff
  piAnn := h.momPiDiff
  gammaAnn := h.momGammaDiff

/-- Moment of `1 + Y`. -/
theorem lintegral_one_add_pow_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ≥0∞} (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, Y ω ^ m ∂P' ≤ ENNReal.ofReal B) :
    ∫⁻ ω, (1 + Y ω) ^ m ∂P' ≤ ENNReal.ofReal (2 ^ m * (1 + B)) := by
  have h2 : (2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  calc ∫⁻ ω, (1 + Y ω) ^ m ∂P' ≤ ∫⁻ ω, 2 ^ m * (1 ^ m + Y ω ^ m) ∂P' :=
        lintegral_mono fun ω => ennreal_add_pow_le _ _ _
    _ = 2 ^ m * (1 + ∫⁻ ω, Y ω ^ m ∂P') := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          one_pow, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 2 ^ m * (1 + ENNReal.ofReal B) := by gcongr
    _ = ENNReal.ofReal (2 ^ m * (1 + B)) := by
        have h1 : (1 : ℝ≥0∞) + ENNReal.ofReal B = ENNReal.ofReal (1 + B) := by
          rw [ENNReal.ofReal_add (by norm_num) hB]; simp
        rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]

end RegularityStructures

end

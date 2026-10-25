/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedBphzCauchyMono
public import Phi43.BPHZ.KolmogorovModelNormStatement
import Mathlib.Tactic
public import Phi43.BPHZ.BphzCauchyCanonical
public import Phi43.BPHZ.BphzCauchyGrowth
public import Phi43.BPHZ.PathwiseKolmogorovInputs
public import Phi43.BPHZ.RegularisedFieldContinuity

/-!
# Cauchy bounds for the BPHZ models with constants `C_K(ρ, ε) + c(ε)`

`bphzModels_cauchy_shifted` is the conclusion of the Cauchy property of the BPHZ models
(`bphzModels_cauchy`) for models whose renormalisation constants are `shiftConst N ρ ε (c ε)` with
`‖c ε‖ ≤ B` on `(0, 1]`; the difference bound carries the factor
`(max ε ε' ^ θ + ‖c ε - c' ε'‖) ^ p`.

Proof: the models are replaced by canonical ones on a set of full measure
(`exists_canonical_replacement`), and the Kolmogorov bound for the model norms is applied to the
canonical models, with the constants as a parameter. In the Kolmogorov bound the moment exponent
`q` is chosen first and then `Cbar := Cm(q)`; it is applied with its exponent equal to `1` and its
difference parameter equal to `E := max ε ε' ^ θ + ‖c ε - c' ε'‖`, where here `θ = κ / 4`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

set_option linter.unusedVariables false in
theorem bphzModels_cauchy_shifted (hG1 : Phi43.RenormalisedCanonicalModelStatement)
    (hG5 : Phi43.KolmogorovModelNormStatement.{u, 0}) (hG7 : Phi43.NoiseCauchyStatement.{u})
    (hin : ∀ (N : ℕ) (κ : Kappa), ShiftedBphzInputs.{u} N κ) :
    ∀ (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
      (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
      (S : Set ParabolicSpace) (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) (B : ℝ) (hB : 0 ≤ B),
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsWhiteNoise P W →
      ∀ (ξ ξ' : ℝ → Ω → SpaceTime → ℝ),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ' ε (ξ' ε)) →
      ∀ (c c' : ℝ → RenormalisationConstants),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ‖c ε‖ ≤ B) → (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ‖c' ε‖ ≤ B) →
      ∀ (Z Z' : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          Statements.IsModeratePhi43ModelOf N κ (ξ ε ω) (shiftConst N ρ ε (c ε)) (Z ε ω)) →
        (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          Statements.IsModeratePhi43ModelOf N κ (ξ' ε ω) (shiftConst N ρ' ε (c' ε)) (Z' ε ω)) →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).normOn (gamma κ) S) P ∧
        AEMeasurable (fun ω => (Z ε ω).diffNormOn (Z' ε' ω) (gamma κ) S) P ∧
        ∫⁻ ω, (Z ε ω).normOn (gamma κ) S ^ p ∂P ≤ ENNReal.ofReal C ∧
        ∫⁻ ω, (Z ε ω).diffNormOn (Z' ε' ω) (gamma κ) S ^ p ∂P ≤
          ENNReal.ofReal (C * (max ε ε' ^ θ + ‖c ε - c' ε'‖) ^ p) := by
  intro κ hκE N hN ρ ρ' hρ hρ' S hS p hp B hB
  have hk0 : 0 < κ.1 := κ.2.1
  obtain ⟨κbar, hκbar⟩ : ∃ κbar : ℝ, κbar = κ.1 / 4 := ⟨_, rfl⟩
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = κ.1 / 4 := ⟨_, rfl⟩
  have hκbar0 : 0 < κbar := by rw [hκbar]; positivity
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hκθ : κbar + θ ≤ κ.1 / 2 := by rw [hκbar, hθdef]; linarith
  have hκb2 : κbar ≤ κ.1 / 2 := by rw [hκbar]; linarith
  have hθκ : θ < κ.1 - κbar := by rw [hκbar, hθdef]; linarith
  obtain ⟨q, hpq, hG5q⟩ := hG5 (phi43RegularityStructure κ) (gamma κ) κbar 1 hκbar0
    zero_le_one piDeterministic gammaFullDeterministic S hS p hp
  have hq : 1 ≤ q := hp.trans hpq
  obtain ⟨cA, hcA, hP₁⟩ := (hin N κ).pi hρ hκbar0.le hκb2 hq hB
  obtain ⟨cB, hcB, hP₂⟩ := (hin N κ).pi hρ' hκbar0.le hκb2 hq hB
  obtain ⟨cC, hcC, hP₃⟩ := (hin N κ).pi_sub hρ hρ' hκbar0.le hθ0 hκθ hq hB
  obtain ⟨cD, hcD, hΓ⟩ := (hin N κ).gamma hρ hρ' hκbar0.le hκb2 hθ0 hθκ hq hB
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ,
      Cm = max (max (max cA cB) (max cC cD)) (max 1 (polyPiConst 2)) := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by
    rw [hCm]
    exact (zero_le_one.trans (le_max_left _ _)).trans (le_max_right _ _)
  have hcAm : cA ≤ Cm := by
    rw [hCm]; exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hcBm : cB ≤ Cm := by
    rw [hCm]; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hcCm : cC ≤ Cm := by
    rw [hCm]; exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hcDm : cD ≤ Cm := by
    rw [hCm]; exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hpoly : polyPiConst 2 ≤ Cm := by rw [hCm]; exact le_max_of_le_right (le_max_right _ _)
  have hC1 : 1 ≤ Cm := by rw [hCm]; exact le_max_of_le_right (le_max_left _ _)
  obtain ⟨K, hK, hG5'⟩ := hG5q Cm
  refine ⟨θ, K * Cm ^ p, hθ0, mul_nonneg hK (pow_nonneg hCm0 _), ?_⟩
  intro Ω _ P _ W hW ξ ξ' hξ hξ' c c' hc hc' Z Z' hZ hZ' ε hε ε' hε'
  have hgr₁ := ae_hasPhi43NoiseGrowth_of_noiseCauchy hG7 hρ hW hξ hε
  have hgr₂ := ae_hasPhi43NoiseGrowth_of_noiseCauchy hG7 hρ' hW hξ' hε'
  obtain ⟨ξ₁, hreg₁, hg₁, hd₁⟩ :=
    exists_canonical_replacement hG1 (canonicalLiftGrowth_holds N κ) (hξ ε hε) hgr₁ (hZ ε hε) S
  obtain ⟨ξ₂, hreg₂, hg₂, hd₂⟩ :=
    exists_canonical_replacement hG1 (canonicalLiftGrowth_holds N κ) (hξ' ε' hε') hgr₂
      (hZ' ε' hε') S
  let Z₁ : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup := fun ω =>
    canonicalModelOfLift N κ (shiftConst N ρ ε (c ε)) (ξ₁ ω)
  let Z₂ : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup := fun ω =>
    canonicalModelOfLift N κ (shiftConst N ρ' ε' (c' ε')) (ξ₂ ω)
  have hpoly₁ : ∀ ω, (Z₁ ω).IsPolyCompatible (phi43PolynomialSector κ) := fun ω =>
    canonicalModelOfLift_polyCompatible (hreg₁.1 ω) (hg₁ ω)
  have hpoly₂ : ∀ ω, (Z₂ ω).IsPolyCompatible (phi43PolynomialSector κ) := fun ω =>
    canonicalModelOfLift_polyCompatible (hreg₂.1 ω) (hg₂ ω)
  have hM : 0 ≤ max ε ε' ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = max ε ε' ^ θ + ‖c ε - c' ε'‖ := ⟨_, rfl⟩
  have hE : 0 ≤ E := by rw [hEdef]; exact add_nonneg hM (norm_nonneg _)
  have hE1 : E ^ (1 : ℝ) = max ε ε' ^ θ + ‖c ε - c' ε'‖ := by rw [Real.rpow_one, hEdef]
  obtain ⟨hΓ1, hΓ2, hΓ3⟩ := (hΓ.mono hcDm) (c ε) (c' ε') (hc ε hε) (hc' ε' hε') hW hε hε'
    hreg₁ hreg₂ hg₁ hg₂
  obtain ⟨hΓd1, hΓd2⟩ := gammaDeterministic_hypotheses (N := N) (κ := κ)
    (C₁' := shiftConst N ρ ε (c ε)) (C₂' := shiftConst N ρ' ε' (c' ε'))
    (fun ω => (hreg₁.1 ω)) (fun ω => (hreg₂.1 ω)) hg₁ hg₂ hC1 hE
  have key := hG5' P Z₁ Z₂ Cm E hCm0 le_rfl hE
    (isContinuousRandomModelWithFieldsOn_canonicalModelOfLift (fun z => (hreg₁.2 z).1) hreg₁.1 hg₁ S)
    (isContinuousRandomModelWithFieldsOn_canonicalModelOfLift (fun z => (hreg₂.2 z).1) hreg₂.1 hg₂ S)
    (by
      rintro Z (rfl | rfl)
      · exact fun i hi _ => piDeterministic_bound hpoly₁ hpoly i hi
      · exact fun i hi _ => piDeterministic_bound hpoly₂ hpoly i hi)
    (fun i hi _ => piDeterministic_sub_bound hpoly₁ hpoly₂ hCm0 hE i hi)
    hΓd1
    (fun i j hp hi hj ω x y => by
      rw [Real.rpow_one]
      exact hΓd2 i j hp hi hj ω x y)
    (by
      rintro Z (rfl | rfl) i hi hlt t ht x
      · exact (PiShiftSingleBound.mono (hP₁ i hi hlt) hcAm) (c ε) (hc ε hε) hW hε hreg₁ hg₁ t ht x
      · exact (PiShiftSingleBound.mono (hP₂ i hi hlt) hcBm) (c' ε') (hc' ε' hε') hW hε' hreg₂ hg₂
          t ht x)
    (fun i hi hlt t ht x => by
      rw [hE1]
      exact (PiShiftSubBound.mono (hP₃ i hi hlt) hcCm) (c ε) (c' ε') (hc ε hε) (hc' ε' hε') hW hε
        hε' hreg₁ hreg₂ hg₁ hg₂ t ht x)
    (by
      rintro Z (rfl | rfl) i j hp hi hj x y
      · exact hΓ1 i j hp hi hj x y
      · exact hΓ2 i j hp hi hj x y)
    (fun i j hp hi hj x y => by
      rw [hE1]
      exact hΓ3 i j hp hi hj x y)
  obtain ⟨hm₁, hi₁⟩ := key.1 Z₁ (by simp)
  obtain ⟨hmd, hid⟩ := key.2
  -- transfer to the given models
  have hn : ∀ᵐ ω ∂P, (Z ε ω).normOn (gamma κ) S = (Z₁ ω).normOn (gamma κ) S := by
    filter_upwards [hd₁] with ω hω
    exact Model.normOn_eq_of_diffNormOn_eq_zero hω
  have hdd : ∀ᵐ ω ∂P, (Z ε ω).diffNormOn (Z' ε' ω) (gamma κ) S =
      (Z₁ ω).diffNormOn (Z₂ ω) (gamma κ) S := by
    filter_upwards [hd₁, hd₂] with ω h1 h2
    exact Model.diffNormOn_eq_of_diffNormOn_eq_zero h1 h2
  refine ⟨hm₁.congr (hn.mono fun ω h => h.symm), hmd.congr (hdd.mono fun ω h => h.symm), ?_, ?_⟩
  · calc ∫⁻ ω, (Z ε ω).normOn (gamma κ) S ^ p ∂P = ∫⁻ ω, (Z₁ ω).normOn (gamma κ) S ^ p ∂P :=
          lintegral_congr_ae (hn.mono fun ω h => by simp only [h])
      _ ≤ _ := hi₁
  · calc ∫⁻ ω, (Z ε ω).diffNormOn (Z' ε' ω) (gamma κ) S ^ p ∂P
        = ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) (gamma κ) S ^ p ∂P :=
          lintegral_congr_ae (hdd.mono fun ω h => by simp only [h])
      _ ≤ _ := hid
      _ = _ := by
        congr 1
        rw [hE1, mul_pow]
        ring

end RegularityStructures.Phi43

end

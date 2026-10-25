/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyRand
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblySupport

/-!
# The constants of the concrete `Π` half

`PiHalfConsts` bundles the envelope index and the probability-space-independent constants coming
from the deterministic parts, the pathwise block bounds and the random moment bounds. 
`exists_piHalfConsts` produces them.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pathwise block bound property (single model). -/
def PiHalfPathwiseProp (𝒯 : RegularityStructure ι) (γ : ℝ) (Dπ : Set ι) (DΓ : Set (ι × ι))
    (nEnv : ℕ) (Kdet : ι → ℝ) (c₀ : ℝ) : Prop :=
  ∀ (M : Model 𝒯 parabolicSemigroup) (T : Set ParabolicSpace),
      T ⊆ piHalfUnitBox → ∀ (G C : ℝ), 0 ≤ G → 0 ≤ C → M.GammaBoundOn γ G T →
      (∀ x ∈ T, ∀ (k : ι) (j : ℕ), Measurable (fun w => M.regPi x (Pi.single k 1) (piHalfScale j) w)) →
      ∀ i, 𝒯.deg i < γ → ∀ j : ℕ, ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j),
        ∀ (x : ParabolicSpace) (hx : x ∈ T),
          ‖M.regPi x (Pi.single i 1) u x‖ₑ ≤ ENNReal.ofReal (1 + G) *
            (ENNReal.ofReal (piHalfCellDet 𝒯 Kdet c₀ C j i) +
              piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ M j i (piHalfCellOf T j ⟨x, hx⟩))

/-- The pathwise block bound property (difference). -/
def PiHalfPathwiseDiffProp (𝒯 : RegularityStructure ι) (γ θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv : ℕ) (Kdet KdetD : ι → ℝ) (c₀ : ℝ) : Prop :=
  ∀ (M M' : Model 𝒯 parabolicSemigroup) (T : Set ParabolicSpace),
      T ⊆ piHalfUnitBox → ∀ (G Gd C ε : ℝ), 0 ≤ G → 0 ≤ Gd → 0 ≤ C → 0 ≤ ε →
      M.GammaBoundOn γ G T → Model.GammaDiffBoundOn M M' γ Gd T →
      (∀ x ∈ T, ∀ (k : ι) (j : ℕ), Measurable (fun w => M.regPi x (Pi.single k 1) (piHalfScale j) w)) →
      (∀ x ∈ T, ∀ (k : ι) (j : ℕ), Measurable (fun w => M'.regPi x (Pi.single k 1) (piHalfScale j) w)) →
      ∀ i, 𝒯.deg i < γ → ∀ j : ℕ, ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j),
        ∀ (x : ParabolicSpace) (hx : x ∈ T),
          ‖M.regPi x (Pi.single i 1) u x - M'.regPi x (Pi.single i 1) u x‖ₑ ≤
            ENNReal.ofReal (1 + G) *
              (ENNReal.ofReal (piHalfCellDetG 𝒯 KdetD c₀ (max 1 C) (C * ε ^ θ) j i) +
                piHalfCellDiffRand 𝒯 Dπ DΓ nEnv T C ε θ c₀ M M' j i (piHalfCellOf T j ⟨x, hx⟩)) +
            ENNReal.ofReal Gd *
              (ENNReal.ofReal (piHalfCellDet 𝒯 Kdet c₀ C j i) +
                piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ M' j i (piHalfCellOf T j ⟨x, hx⟩))

/-- Uniform moment bound of the random part of the cell weight (A2). -/
def PiHalfRandMomentProp (𝒯 : RegularityStructure ι) (γ κbar : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv q qPi : ℕ) (KR : ι → ℝ) : Prop :=
  ∀ k, 𝒯.deg k < γ → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → Model 𝒯 parabolicSemigroup) (C : ℝ), 0 ≤ C →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z C →
      ∀ {s : ℝ}, s ∈ Ioc (0 : ℝ) 1 → ∀ (x₀ : ParabolicSpace),
      Measurable (fun z : Ω × ParabolicSpace => (Z z.1).regPi x₀ (Pi.single k 1) s z.2) →
      (∀ j w, Measurable fun ω => (Z ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z ω).gammaMap w x₀ (Pi.single k 1) j) →
      ∫⁻ ω, piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C s x₀ k (Z ω) ^ q ∂P ≤
        ENNReal.ofReal (KR k * max 1 C * C * s ^ ((𝒯.deg k + κbar) / 4)) ^ q

/-- Uniform moment bound of the random part of the difference weight (A3). -/
def PiHalfRandMomentDiffProp (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv q qPi : ℕ) (KR : ι → ℝ) : Prop :=
  ∀ k, 𝒯.deg k < γ → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ), 0 ≤ C → 0 ≤ ε →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z₁ C →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z₂ C →
      PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε →
      ∀ {s : ℝ}, s ∈ Ioc (0 : ℝ) 1 → ∀ (x₀ : ParabolicSpace),
      Measurable (fun z : Ω × ParabolicSpace => (Z₁ z.1).regPi x₀ (Pi.single k 1) s z.2 -
        (Z₂ z.1).regPi x₀ (Pi.single k 1) s z.2) →
      (∀ j w, Measurable fun ω => (Z₁ ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z₂ ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j) →
      (∀ j w, Measurable fun ω => (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j) →
      ∫⁻ ω, piHalfCellDiffRandPartA 𝒯 Dπ DΓ nEnv C ε θ s x₀ k (Z₁ ω) (Z₂ ω) ^ q ∂P ≤
        ENNReal.ofReal (KR k * max 1 C * (C * ε ^ θ) * s ^ ((𝒯.deg k + κbar) / 4)) ^ q

/-- The constants of the concrete `Π` half. -/
structure PiHalfConsts (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (q qPi : ℕ) where
  nEnv : ℕ
  Kdet : ι → ℝ
  KdetD : ι → ℝ
  KR : ι → ℝ
  KRd : ι → ℝ
  c₀ : ℝ
  c₀d : ℝ
  hKdet : ∀ k, 0 ≤ Kdet k
  hKdetD : ∀ k, 0 ≤ KdetD k
  hKR : ∀ k, 0 ≤ KR k
  hKRd : ∀ k, 0 ≤ KRd k
  hc₀ : 0 ≤ c₀
  hc₀d : 0 ≤ c₀d
  hpw : PiHalfPathwiseProp 𝒯 γ Dπ DΓ nEnv Kdet c₀
  hpwd : PiHalfPathwiseDiffProp 𝒯 γ θ Dπ DΓ nEnv Kdet KdetD c₀d
  hRk : PiHalfRandMomentProp.{u} 𝒯 γ κbar Dπ DΓ nEnv q qPi KR
  hRkd : PiHalfRandMomentDiffProp.{u} 𝒯 γ κbar θ Dπ DΓ nEnv q qPi KRd

/-- Existence of the constants, for `q ≥ 1` and `2 q ≤ qPi`. -/
theorem exists_piHalfConsts (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (hκ : 0 < κbar)
    (Dπ : Set ι) (DΓ : Set (ι × ι)) (q qPi : ℕ) (hq : 1 ≤ q) (hqPi : 2 * q ≤ qPi) :
    Nonempty (PiHalfConsts.{u} 𝒯 γ κbar θ Dπ DΓ q qPi) := by
  obtain ⟨N, hN1, hN, hN'⟩ := exists_piHalfEnvIndex 𝒯 hκ q hq
  -- deterministic parts
  have hA1 : ∀ k : ι, ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ), 0 ≤ C → ∀ {s : ℝ}, 0 < s →
      ∀ (x₀ : ParabolicSpace), piHalfCellDetPartA 𝒯 Dπ DΓ N C s x₀ k ≤
        ENNReal.ofReal (K * max 1 C * C * s ^ (𝒯.deg k / 4)) := fun k =>
    exists_piHalfCellDetPartA_le 𝒯 Dπ DΓ k (hN' k)
  choose Kdet hKdet hdetA using hA1
  have hA1d : ∀ k : ι, ∃ K : ℝ, 0 ≤ K ∧ ∀ (C ε : ℝ), 0 ≤ C → 0 ≤ ε → ∀ {s : ℝ}, 0 < s →
      ∀ (x₀ : ParabolicSpace), piHalfCellDiffDetPartA 𝒯 Dπ DΓ N C ε θ s x₀ k ≤
        ENNReal.ofReal (K * max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg k / 4)) := fun k => by
    obtain ⟨K, hK, h⟩ := exists_piHalfCellDiffDetPartA_le 𝒯 Dπ DΓ k (hN' k)
    exact ⟨K, hK, fun C ε hC hε s hs x₀ => h C ε θ hC hε hs x₀⟩
  choose KdetD hKdetD hdetD using hA1d
  obtain ⟨c₀, hc₀, hpw⟩ := exists_piHalfCell_pathwise 𝒯 γ Dπ DΓ N Kdet hKdet
    (fun k C hC s hs x₀ => hdetA k C hC hs x₀)
  obtain ⟨c₀d, hc₀d, hpwd⟩ := exists_piHalfCell_pathwise_diff 𝒯 γ θ Dπ DΓ N Kdet KdetD hKdet
    hKdetD (fun k C hC s hs x₀ => hdetA k C hC hs x₀)
    (fun k C ε hC hε s hs x₀ => hdetD k C ε hC hε hs x₀)
  -- random parts
  have hA2 : ∀ k : ι, ∃ K : ℝ, 0 ≤ K ∧ (𝒯.deg k < γ → ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → Model 𝒯 parabolicSemigroup) (C : ℝ),
      0 ≤ C → PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z C →
      ∀ {s : ℝ}, s ∈ Ioc (0 : ℝ) 1 → ∀ (x₀ : ParabolicSpace),
      Measurable (fun z : Ω × ParabolicSpace => (Z z.1).regPi x₀ (Pi.single k 1) s z.2) →
      (∀ j w, Measurable fun ω => (Z ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z ω).gammaMap w x₀ (Pi.single k 1) j) →
      ∫⁻ ω, piHalfCellRandPartA 𝒯 Dπ DΓ N C s x₀ k (Z ω) ^ q ∂P ≤
        ENNReal.ofReal (K * max 1 C * C * s ^ ((𝒯.deg k + κbar) / 4)) ^ q) := fun k => by
    by_cases hk : 𝒯.deg k < γ
    · obtain ⟨K, hK, h⟩ := exists_piHalfCellRandPartA_moment_le_uniform.{u} 𝒯 γ κbar hκ Dπ DΓ k hk
        (n := N) (p := q) (q := qPi) hq hqPi hN1 (hN k)
      exact ⟨K, hK, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose KR hKR hRk using hA2
  have hA3 : ∀ k : ι, ∃ K : ℝ, 0 ≤ K ∧ (𝒯.deg k < γ → ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup)
      (C ε : ℝ), 0 ≤ C → 0 ≤ ε →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z₁ C →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z₂ C →
      PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε →
      ∀ {s : ℝ}, s ∈ Ioc (0 : ℝ) 1 → ∀ (x₀ : ParabolicSpace),
      Measurable (fun z : Ω × ParabolicSpace => (Z₁ z.1).regPi x₀ (Pi.single k 1) s z.2 -
        (Z₂ z.1).regPi x₀ (Pi.single k 1) s z.2) →
      (∀ j w, Measurable fun ω => (Z₁ ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z₂ ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j) →
      (∀ j w, Measurable fun ω => (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j) →
      ∫⁻ ω, piHalfCellDiffRandPartA 𝒯 Dπ DΓ N C ε θ s x₀ k (Z₁ ω) (Z₂ ω) ^ q ∂P ≤
        ENNReal.ofReal (K * max 1 C * (C * ε ^ θ) * s ^ ((𝒯.deg k + κbar) / 4)) ^ q) := fun k => by
    by_cases hk : 𝒯.deg k < γ
    · obtain ⟨K, hK, h⟩ := exists_piHalfCellDiffRandPartA_moment_le_uniform.{u} 𝒯 γ κbar θ hκ Dπ DΓ
        k hk (n := N) (p := q) (q := qPi) hq hqPi hN1 (hN k)
      exact ⟨K, hK, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose KRd hKRd hRkd using hA3
  exact ⟨⟨N, Kdet, KdetD, KR, KRd, c₀, c₀d, hKdet, hKdetD, hKR, hKRd, hc₀, hc₀d, hpw, hpwd,
    fun k hk => hRk k hk, fun k hk => hRkd k hk⟩⟩

end RegularityStructures

end

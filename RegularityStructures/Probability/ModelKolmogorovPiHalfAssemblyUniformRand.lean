/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyUniformFamily
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightAMoment

/-!
# Uniform moment of the random part of the cell weight (A2)

`exists_piHalfCellRandPartA_moment_le_uniform`: the constant `K` of A2 is chosen before the probability
space (the proof is that of `exists_piHalfCellRandPartA_moment_le`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **(A2)** The `p`-th moment of the random part of the cell weight. -/
theorem exists_piHalfCellRandPartA_moment_le_uniform (𝒯 : RegularityStructure ι) (γ κbar : ℝ)
    (hκ : 0 < κbar) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι) (hkγ : 𝒯.deg k < γ)
    {n p q : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q) (hn1 : 1 < n)
    (hn : ∀ j, 𝒯.deg j ≤ 𝒯.deg k → (𝒯.deg k - 𝒯.deg j + κbar) * p + 1 < n)
    :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Ω → Model 𝒯 parabolicSemigroup) (C : ℝ), 0 ≤ C →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z C →
      ∀ {s : ℝ}, s ∈ Ioc (0 : ℝ) 1 → ∀ (x₀ : ParabolicSpace),
      Measurable (fun z : Ω × ParabolicSpace => (Z z.1).regPi x₀ (Pi.single k 1) s z.2) →
      (∀ j w, Measurable fun ω => (Z ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z ω).gammaMap w x₀ (Pi.single k 1) j) →
      ∫⁻ ω, piHalfCellRandPartA 𝒯 Dπ DΓ n C s x₀ k (Z ω) ^ p ∂P ≤
        ENNReal.ofReal (K * max 1 C * C * s ^ ((𝒯.deg k + κbar) / 4)) ^ p := by
  classical
  set J := piHalfRandIndexA 𝒯 Dπ DΓ k with hJ
  have hJk : ∀ j ∈ J, 𝒯.deg j ≤ 𝒯.deg k ∧
      ¬ (j ∈ Dπ ∧ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ)) := fun j hj => by
    simpa [hJ, piHalfRandIndexA] using hj
  have hα : ∀ j ∈ J, 0 ≤ piHalfRandAlphaA 𝒯 κbar DΓ k j := fun j hj =>
    (piHalf_rand_alpha_bounds hκ (hJk j hj).1).1
  have hnα : ∀ j ∈ J, piHalfRandAlphaA 𝒯 κbar DΓ k j * p + 1 < n := fun j hj =>
    lt_of_le_of_lt (by
      have := (piHalf_rand_alpha_bounds (DΓ := DΓ) hκ (hJk j hj).1).2
      nlinarith [(by positivity : (0 : ℝ) ≤ p)]) (hn j (hJk j hj).1)
  obtain ⟨M, hM0, hM⟩ := exists_kernelBlockEnvelope_weightedFamily_lintegral_pow_moment_le_uniform
    J (piHalfRandAlphaA 𝒯 κbar DΓ k) hp hn1 hα hnα (J.card ^ (p - 1))
  refine ⟨M * J.card, by positivity, fun {Ω} _ P _ Z C hC hH s hs x₀ hmOff hmPi hmGam => ?_⟩
  have hs0 : 0 < s := hs.1
  have hCm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  let c : ι → ℝ := fun j => max 1 C * C * s ^ piHalfRandBetaA 𝒯 κbar Dπ j
  have hc : ∀ j, 0 ≤ c j := fun j =>
    mul_nonneg (mul_nonneg hCm hC) (Real.rpow_nonneg hs0.le _)
  let Y : Ω → ParabolicSpace → ℝ≥0∞ := fun ω w => piHalfCellRandRemA 𝒯 Dπ DΓ k C s x₀ (Z ω) w
  have hY : Measurable (Function.uncurry Y) := by
    have h1 : Measurable (fun z : Ω × ParabolicSpace =>
        ‖(Z z.1).regPi x₀ (Pi.single k 1) s z.2‖ₑ) := hmOff.enorm
    have h2 : Measurable (fun z : Ω × ParabolicSpace =>
        ENNReal.ofReal (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀ z.2)) :=
      (measurable_piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀).ennreal_ofReal.comp measurable_snd
    exact h1.sub h2
  have hpoint : ∀ w : ParabolicSpace, ∫⁻ ω, Y ω w ^ p ∂P ≤
      ((J.card ^ (p - 1) : ℕ) : ℝ≥0∞) *
        ∑ j ∈ J, ENNReal.ofReal (c j * parabolicNorm (x₀ - w) ^ piHalfRandAlphaA 𝒯 κbar DΓ k j) ^ p := by
    intro w
    have hterm : ∀ j, Measurable fun ω => piHalfCellTermA 𝒯 s x₀ k (Z ω) j w := fun j =>
      (hmGam j w).enorm.mul (hmPi j w).enorm
    have hmj : ∀ j, Measurable fun ω => piHalfCellTermA 𝒯 s x₀ k (Z ω) j w ^ p := fun j =>
      (hterm j).pow_const p
    calc ∫⁻ ω, Y ω w ^ p ∂P
        ≤ ∫⁻ ω, (J.card : ℝ≥0∞) ^ (p - 1) *
            ∑ j ∈ J, piHalfCellTermA 𝒯 s x₀ k (Z ω) j w ^ p ∂P := by
          refine lintegral_mono fun ω => ?_
          refine le_trans (pow_le_pow_left' ?_ p) (piHalf_finset_sum_pow_le J _ hp)
          exact piHalfCellRandRemA_le_sum hkγ hC (Z ω)
            (fun i hi hiγ t ht x => hH.piDet i hi hiγ ω t ht x)
            (fun i j h1 h2 h3 x y => hH.gammaDet i j h1 h2 h3 ω x y) hs x₀ w
      _ = (J.card : ℝ≥0∞) ^ (p - 1) *
            ∑ j ∈ J, ∫⁻ ω, piHalfCellTermA 𝒯 s x₀ k (Z ω) j w ^ p ∂P := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)),
            lintegral_finsetSum _ fun j _ => hmj j]
      _ ≤ _ := by
          rw [Nat.cast_pow]
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) zero_le
          exact piHalf_term_pointwise_moment hH hC hkγ hp hpq hs x₀ w
            (fun j => hmPi j w) (fun j => hmGam j w) (hJk j hj).1 (hJk j hj).2
  have hmain := hM (Ω := Ω) (P := P) hs0 Y hY x₀ c hc hpoint
  refine hmain.trans (piHalf_ofReal_pow_le ?_ p)
  have hterm : ∀ j ∈ J, c j * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k j / 4) ≤
      max 1 C * C * s ^ ((𝒯.deg k + κbar) / 4) := by
    intro j hj
    have hexp := piHalf_rand_exponent_ge (Dπ := Dπ) (DΓ := DΓ) hκ (hJk j hj).2
    have : c j * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k j / 4) =
        max 1 C * C * s ^ (piHalfRandBetaA 𝒯 κbar Dπ j +
          piHalfRandAlphaA 𝒯 κbar DΓ k j / 4) := by
      simp only [c]
      rw [Real.rpow_add hs0]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hs0 hs.2 hexp)
      (mul_nonneg hCm hC)
  have hsum : ∑ j ∈ J, c j * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k j / 4) ≤
      J.card * (max 1 C * C * s ^ ((𝒯.deg k + κbar) / 4)) := by
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    simp
  calc M * ∑ j ∈ J, c j * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k j / 4)
      ≤ M * (J.card * (max 1 C * C * s ^ ((𝒯.deg k + κbar) / 4))) :=
        mul_le_mul_of_nonneg_left hsum hM0
    _ = _ := by ring

end RegularityStructures

end

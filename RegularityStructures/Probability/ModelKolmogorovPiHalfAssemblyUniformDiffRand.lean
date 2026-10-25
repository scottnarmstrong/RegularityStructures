/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyUniformRand
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADiffMoment

/-!
# Uniform moment of the random part of the difference weight (A3)

The constant of A3 chosen before the probability space.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **(A3)** The `p`-th moment of the random part of the difference weight. -/
theorem exists_piHalfCellDiffRandPartA_moment_le_uniform (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ)
    (hκ : 0 < κbar) (Dπ : Set ι) (DΓ : Set (ι × ι)) (k : ι) (hkγ : 𝒯.deg k < γ)
    {n p q : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q) (hn1 : 1 < n)
    (hn : ∀ j, 𝒯.deg j ≤ 𝒯.deg k → (𝒯.deg k - 𝒯.deg j + κbar) * p + 1 < n)
    :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ), 0 ≤ C → 0 ≤ ε →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₁ C →
      PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₂ C →
      PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε →
      ∀ {s : ℝ}, s ∈ Ioc (0 : ℝ) 1 → ∀ (x₀ : ParabolicSpace),
      Measurable (fun z : Ω × ParabolicSpace => (Z₁ z.1).regPi x₀ (Pi.single k 1) s z.2 -
        (Z₂ z.1).regPi x₀ (Pi.single k 1) s z.2) →
      (∀ j w, Measurable fun ω => (Z₁ ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z₂ ω).regPi w (Pi.single j 1) s w) →
      (∀ j w, Measurable fun ω => (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j) →
      (∀ j w, Measurable fun ω => (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j) →
      ∫⁻ ω, piHalfCellDiffRandPartA 𝒯 Dπ DΓ n C ε θ s x₀ k (Z₁ ω) (Z₂ ω) ^ p ∂P ≤
        ENNReal.ofReal (K * max 1 C * (C * ε ^ θ) * s ^ ((𝒯.deg k + κbar) / 4)) ^ p := by
  classical
  set J := piHalfRandIndexA 𝒯 Dπ DΓ k ×ˢ (Finset.univ : Finset Bool) with hJ
  have hJk : ∀ jb ∈ J, 𝒯.deg jb.1 ≤ 𝒯.deg k ∧
      ¬ (jb.1 ∈ Dπ ∧ (𝒯.deg jb.1 = 𝒯.deg k ∨ (k, jb.1) ∈ DΓ)) := fun jb hjb => by
    have := (Finset.mem_product.1 hjb).1
    simpa [piHalfRandIndexA] using this
  have hα : ∀ jb ∈ J, 0 ≤ piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 := fun jb hjb =>
    (piHalf_rand_alpha_bounds hκ (hJk jb hjb).1).1
  have hnα : ∀ jb ∈ J, piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 * p + 1 < n := fun jb hjb =>
    lt_of_le_of_lt (by
      have := (piHalf_rand_alpha_bounds (DΓ := DΓ) hκ (hJk jb hjb).1).2
      nlinarith [(by positivity : (0 : ℝ) ≤ p)]) (hn jb.1 (hJk jb hjb).1)
  obtain ⟨M, hM0, hM⟩ := exists_kernelBlockEnvelope_weightedFamily_lintegral_pow_moment_le_uniform
    J (fun jb => piHalfRandAlphaA 𝒯 κbar DΓ k jb.1) hp hn1 hα hnα (J.card ^ (p - 1))
  refine ⟨M * J.card, by positivity,
    fun {Ω} _ P _ Z₁ Z₂ C ε hC hε hH₁ hH₂ hD s hs x₀ hmOff hmPi₁ hmPi₂ hmGam₁ hmGam₂ => ?_⟩
  have hs0 : 0 < s := hs.1
  have hCm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hCd : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
  let c : ι × Bool → ℝ := fun jb => max 1 C * (C * ε ^ θ) * s ^ piHalfRandBetaA 𝒯 κbar Dπ jb.1
  have hc : ∀ jb, 0 ≤ c jb := fun jb =>
    mul_nonneg (mul_nonneg hCm hCd) (Real.rpow_nonneg hs0.le _)
  let Y : Ω → ParabolicSpace → ℝ≥0∞ := fun ω w =>
    piHalfCellDiffRandRemA 𝒯 Dπ DΓ k C ε θ s x₀ (Z₁ ω) (Z₂ ω) w
  have hY : Measurable (Function.uncurry Y) := by
    have h1 : Measurable (fun z : Ω × ParabolicSpace =>
        ‖(Z₁ z.1).regPi x₀ (Pi.single k 1) s z.2 - (Z₂ z.1).regPi x₀ (Pi.single k 1) s z.2‖ₑ) :=
      hmOff.enorm
    have h2 : Measurable (fun z : Ω × ParabolicSpace =>
        ENNReal.ofReal (piHalfCellDiffDetFunA 𝒯 Dπ DΓ k C ε θ s x₀ z.2)) :=
      (measurable_piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k _ s x₀).ennreal_ofReal.comp measurable_snd
    exact h1.sub h2
  have hpoint : ∀ w : ParabolicSpace, ∫⁻ ω, Y ω w ^ p ∂P ≤
      ((J.card ^ (p - 1) : ℕ) : ℝ≥0∞) *
        ∑ jb ∈ J, ENNReal.ofReal (c jb * parabolicNorm (x₀ - w) ^
          piHalfRandAlphaA 𝒯 κbar DΓ k jb.1) ^ p := by
    intro w
    have hmj : ∀ jb, Measurable fun ω =>
        piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) jb w ^ p := fun jb =>
      (measurable_piHalfCellDiffTermA_omega (fun j => hmPi₁ j w) (fun j => hmPi₂ j w)
        (fun j => hmGam₁ j w) (fun j => hmGam₂ j w) jb).pow_const p
    calc ∫⁻ ω, Y ω w ^ p ∂P
        ≤ ∫⁻ ω, (J.card : ℝ≥0∞) ^ (p - 1) *
            ∑ jb ∈ J, piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) jb w ^ p ∂P := by
          refine lintegral_mono fun ω => ?_
          refine le_trans (pow_le_pow_left' ?_ p) (piHalf_finset_sum_pow_le J _ hp)
          exact piHalfCellDiffRandRemA_le_sum hH₁ hH₂ hD hkγ hC hε hs ω x₀ w
      _ = (J.card : ℝ≥0∞) ^ (p - 1) *
            ∑ jb ∈ J, ∫⁻ ω, piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) jb w ^ p ∂P := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)),
            lintegral_finsetSum _ fun jb _ => hmj jb]
      _ ≤ _ := by
          rw [Nat.cast_pow]
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun jb hjb => ?_) zero_le
          exact piHalf_diffTerm_pointwise_moment hH₁ hH₂ hD hC hε hkγ hp hpq hs x₀ w
            (fun j => hmPi₁ j w) (fun j => hmPi₂ j w) (fun j => hmGam₁ j w)
            (fun j => hmGam₂ j w) (hJk jb hjb).1 jb.2
  have hmain := hM (Ω := Ω) (P := P) hs0 Y hY x₀ c hc hpoint
  refine hmain.trans (piHalf_ofReal_pow_le ?_ p)
  have hterm : ∀ jb ∈ J, c jb * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 / 4) ≤
      max 1 C * (C * ε ^ θ) * s ^ ((𝒯.deg k + κbar) / 4) := by
    intro jb hjb
    have hexp := piHalf_rand_exponent_ge (Dπ := Dπ) (DΓ := DΓ) hκ (hJk jb hjb).2
    have : c jb * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 / 4) =
        max 1 C * (C * ε ^ θ) * s ^ (piHalfRandBetaA 𝒯 κbar Dπ jb.1 +
          piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 / 4) := by
      simp only [c]
      rw [Real.rpow_add hs0]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hs0 hs.2 hexp)
      (mul_nonneg hCm hCd)
  have hsum : ∑ jb ∈ J, c jb * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 / 4) ≤
      J.card * (max 1 C * (C * ε ^ θ) * s ^ ((𝒯.deg k + κbar) / 4)) := by
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    simp
  calc M * ∑ jb ∈ J, c jb * s ^ (piHalfRandAlphaA 𝒯 κbar DΓ k jb.1 / 4)
      ≤ M * (J.card * (max 1 C * (C * ε ^ θ) * s ^ ((𝒯.deg k + κbar) / 4))) :=
        mul_le_mul_of_nonneg_left hsum hM0
    _ = _ := by ring

end RegularityStructures

end

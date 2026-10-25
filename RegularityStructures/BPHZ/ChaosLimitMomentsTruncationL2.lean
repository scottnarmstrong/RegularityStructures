/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationAE
public import RegularityStructures.BPHZ.WhiteNoiseChaosMomentsLimit

/-!
# `L²` convergence of the truncated tested fields

Let `F` be a jointly measurable random field with `E F(y)² ≤ M` and assume the weighted
Cauchy-Schwarz bound `E (∫ h F)² ≤ (∫ |h|)² M` for measurable integrable `h` supported in a time
slab (`hCS`). Then for `Xₙ = ∫ truncₙ(g) F` and `X = ∫ g F`,
`E (Xₙ - X)² ≤ τₙ² M`, with `τₙ = ∫ |g - truncₙ(g)| → 0`. The proof applies Fatou's lemma to
`(Xₙ - X_{n+j})²` as `j → ∞`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace RegularityStructures

/-- The weighted Cauchy-Schwarz hypothesis for slab-supported weights. -/
def SlabSecondMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → SpaceTime → ℝ) (c M : ℝ) : Prop :=
  ∀ (R : ℝ) (h : SpaceTime → ℝ), Measurable h → Integrable h → (∀ y, h y ≠ 0 → |y.1 - c| ≤ R) →
    Integrable (fun ω => (∫ y, h y * F ω y) ^ 2) P ∧
      ∫ ω, (∫ y, h y * F ω y) ^ 2 ∂P ≤ (∫ y, |h y|) * ((∫ y, |h y|) * M)

end RegularityStructures

end

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Ω → SpaceTime → ℝ}
  {g : SpaceTime → ℝ}

/-- **`L²` distance between the truncated and the full tested field.** -/
theorem integrable_and_integral_sq_sub_le [IsProbabilityMeasure P] {c M : ℝ}
    (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hgm : Measurable g)
    (hgi : Integrable g)
    (hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ M)
    (hCS : SlabSecondMoment P F c M) (n : ℕ) :
    Integrable (fun ω => ((∫ y, timeTruncation c n g y * F ω y) - ∫ y, g y * F ω y) ^ 2) P ∧
      ∫ ω, ((∫ y, timeTruncation c n g y * F ω y) - ∫ y, g y * F ω y) ^ 2 ∂P ≤
        (∫ y, |g y - timeTruncation c n g y|) *
          ((∫ y, |g y - timeTruncation c n g y|) * M) := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hF2 0).2
  set τ : ℝ := ∫ y, |g y - timeTruncation c n g y| with hτ
  have hτi : Integrable (fun y => |g y - timeTruncation c n g y|) :=
    (hgi.sub (integrable_timeTruncation hgi c n)).abs
  set X : ℕ → Ω → ℝ := fun k ω => ∫ y, timeTruncation c k g y * F ω y with hX
  set Xg : Ω → ℝ := fun ω => ∫ y, g y * F ω y with hXg
  have hXm : ∀ k, Measurable (X k) := fun k =>
    measurable_integral_mul_field hFm (measurable_timeTruncation hgm c k)
  have hXgm : Measurable Xg := measurable_integral_mul_field hFm hgm
  set h : ℕ → SpaceTime → ℝ := fun j y =>
    timeTruncation c ((j + n : ℕ) : ℝ) g y - timeTruncation c n g y with hh
  have hhm : ∀ j, Measurable (h j) := fun j =>
    (measurable_timeTruncation hgm c _).sub (measurable_timeTruncation hgm c _)
  have hhi : ∀ j, Integrable (h j) := fun j =>
    (integrable_timeTruncation hgi c _).sub (integrable_timeTruncation hgi c _)
  have hhs : ∀ j y, h j y ≠ 0 → |y.1 - c| ≤ ((j + n : ℕ) : ℝ) := fun j y hy => by
    by_contra hcon
    refine hy ?_
    have hn : (n : ℝ) ≤ ((j + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left n j
    simp only [hh, timeTruncation_eq_zero_of_lt g (not_le.1 hcon),
      timeTruncation_eq_zero_of_lt g (lt_of_le_of_lt hn (not_le.1 hcon)), sub_zero]
  have hhL1 : ∀ j, ∫ y, |h j y| ≤ τ := fun j =>
    integral_mono ((hhi j).abs) hτi fun y =>
      abs_timeTruncation_sub_le (by exact_mod_cast Nat.le_add_left n j) g y
  have hae : ∀ᵐ ω ∂P, ∀ j, X (j + n) ω - X n ω = ∫ y, h j y * F ω y := by
    filter_upwards [ae_integrable_timeTruncation_mul (c := c) (R := n) hFm hgm hgi hF2]
      with ω hω j
    have h1 : Integrable (fun y => timeTruncation c ((j + n : ℕ) : ℝ) g y * F ω y) :=
      integrable_timeTruncation_mul hgm (hFm.comp (measurable_const.prodMk measurable_id)) hω.1
    simp only [hX, hh, sub_mul]
    rw [integral_sub h1 hω.2]
  have hae' : ∀ᵐ ω ∂P, ∀ j, X (j + n) ω - X n ω = ∫ y, h j y * F ω y := hae
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun j : ℕ => (X n ω - X (j + n) ω) ^ 2) atTop
      (𝓝 ((X n ω - Xg ω) ^ 2)) := by
    filter_upwards [ae_tendsto_integral_timeTruncation_mul c hFm hgm hgi hF2] with ω hω
    exact ((tendsto_const_nhds.sub (hω.comp (tendsto_add_atTop_nat n))).pow 2)
  have hG : ∀ j, Integrable (fun ω => (X n ω - X (j + n) ω) ^ 2) P ∧
      ∫ ω, (X n ω - X (j + n) ω) ^ 2 ∂P ≤ τ * (τ * M) := fun j => by
    have hcs := hCS ((j + n : ℕ) : ℝ) (h j) (hhm j) (hhi j) (hhs j)
    have e : (fun ω => (X n ω - X (j + n) ω) ^ 2) =ᵐ[P] fun ω => (∫ y, h j y * F ω y) ^ 2 := by
      filter_upwards [hae'] with ω hω
      rw [← hω j, ← neg_sub, neg_sq]
    refine ⟨hcs.1.congr e.symm, ?_⟩
    rw [integral_congr_ae e]
    refine hcs.2.trans ?_
    have h0 : 0 ≤ ∫ y, |h j y| := integral_nonneg fun y => abs_nonneg _
    exact mul_le_mul (hhL1 j) (mul_le_mul (hhL1 j) le_rfl hM0 (h0.trans (hhL1 j))) 
      (mul_nonneg h0 hM0) (h0.trans (hhL1 j))
  have key := integrable_and_integral_le_of_ae_tendsto (μ := P)
    (G := fun j ω => (X n ω - X (j + n) ω) ^ 2) (G' := fun ω => (X n ω - Xg ω) ^ 2)
    (b := fun _ => τ * (τ * M)) (B := τ * (τ * M))
    (fun j => ((hXm n).sub (hXm (j + n))).pow_const 2) (fun j ω => sq_nonneg _)
    (fun j => (hG j).1) hlim (fun j => (hG j).2) tendsto_const_nhds
  simpa only [hX, hXg] using key

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ModelNearChain

/-!
# Chaining for the difference of two models

Near-`1` bounds for `Γ¹`, `Γ²` (constant `C`) and `Γ¹ - Γ²` (constant `δ`) on a segment-closed set
give the near-`R` difference bound, `R² ≤ m`, with constant `gammaDiffChainConst |ι| C δ m`
(`GammaDiffBoundNearOn.of_one`).  The constant is defined by the recursion of
`GammaEntryDiffBound.comp`.
-/

@[expose] public section

namespace RegularityStructures

/-- `d₀ = 0`, `d_{k+1} = N (B^k D + d_k B')` with `B' = max 1 C`, `B = N B'`, `D = max 0 δ`. -/
def gammaDiffStep (N : ℕ) (C δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => N * (((N : ℝ) * max 1 C) ^ k * max 0 δ) + N * (gammaDiffStep N C δ k * max 1 C)

/-- The constant of the chained near-`R` difference bound after `m` steps. -/
def gammaDiffChainConst (N : ℕ) (C δ : ℝ) (m : ℕ) : ℝ := max δ (gammaDiffStep N C δ m)

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem gammaDiffStep_nonneg (N : ℕ) (C δ : ℝ) (k : ℕ) : 0 ≤ gammaDiffStep N C δ k := by
  have hB : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  induction k with
  | zero => simp [gammaDiffStep]
  | succ k ih =>
    unfold gammaDiffStep
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hD : 0 ≤ max 0 δ := le_max_left _ _
    positivity

namespace Model

variable {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ C δ : ℝ} {S : Set ParabolicSpace}

theorem gammaEntryDiffBound_of_near (h : M₁.GammaDiffBoundNearOn M₂ γ δ 1 S)
    {x y : ParabolicSpace} (hx : x ∈ S) (hy : y ∈ S) (hd : parabolicSemigroup.scaleDist y x ≤ 1) :
    GammaEntryDiffBound 𝒯 γ (max 0 δ) (M₁.gammaMap y x) (M₂.gammaMap y x) := by
  intro i j hi
  have hU₁ := M₁.isGradedUnipotent_gammaMap y x
  have hU₂ := M₂.isGradedUnipotent_gammaMap y x
  by_cases hji : j = i
  · subst hji
    rw [hU₁.apply_single_self, hU₂.apply_single_self, sub_self, abs_zero]
    exact le_max_left _ _
  by_cases hlt : 𝒯.deg j < 𝒯.deg i
  · have hd0 : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg _ _
    have hp0 : 0 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
      Real.rpow_nonneg hd0 _
    have hp1 : parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) ≤ 1 :=
      Real.rpow_le_one hd0 hd (by linarith)
    refine (h i j hi hlt x hx y hy hd).trans ?_
    rcases le_total 0 δ with hδ | hδ
    · calc δ * _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hp1 hδ
        _ ≤ max 0 δ := by rw [mul_one]; exact le_max_right _ _
    · calc δ * _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδ hp0
        _ ≤ max 0 δ := le_max_left _ _
  · rw [hU₁.apply_single_of_le hji (not_lt.1 hlt), hU₂.apply_single_of_le hji (not_lt.1 hlt),
      sub_self, abs_zero]
    exact le_max_left _ _

theorem gammaEntryDiffBound_chain (hS : SegmentClosed S) (h₁ : M₁.GammaBoundNearOn γ C 1 S)
    (h₂ : M₂.GammaBoundNearOn γ C 1 S) (h : M₁.GammaDiffBoundNearOn M₂ γ δ 1 S)
    {x y : ParabolicSpace} (hx : x ∈ S) (hy : y ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (hstep : parabolicNorm ((1 / (m : ℝ)) • (y - x)) ≤ 1) :
    GammaEntryDiffBound 𝒯 γ (gammaDiffStep (Fintype.card ι) C δ m) (M₁.gammaMap y x)
      (M₂.gammaMap y x) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set z : ℕ → ParabolicSpace := fun k => x + ((k : ℝ) / m) • (y - x) with hz
  have hzmem : ∀ k : ℕ, k ≤ m → z k ∈ S := fun k hk =>
    hS x hx y hy _ (by positivity) ((div_le_one hm0).2 (by exact_mod_cast hk))
  have hB0 : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have key : ∀ k : ℕ, k ≤ m →
      GammaEntryBound 𝒯 γ (((Fintype.card ι : ℝ) * max 1 C) ^ k) (M₁.gammaMap (z k) x) ∧
      GammaEntryDiffBound 𝒯 γ (gammaDiffStep (Fintype.card ι) C δ k) (M₁.gammaMap (z k) x)
        (M₂.gammaMap (z k) x) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : z 0 = x := by simp [hz]
      rw [this, M₁.gammaMap_self, M₂.gammaMap_self, pow_zero]
      exact ⟨GammaEntryBound.id, GammaEntryDiffBound.self _⟩
    | succ k ih =>
      intro hk
      obtain ⟨ihb, ihd⟩ := ih (Nat.le_of_succ_le hk)
      have hdiff : z (k + 1) - z k = (1 / (m : ℝ)) • (y - x) := by
        simp only [hz]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        push_cast
        ring
      have hdist : parabolicSemigroup.scaleDist (z (k + 1)) (z k) ≤ 1 := by
        change parabolicNorm (z (k + 1) - z k) ≤ 1
        rw [hdiff]
        exact hstep
      have hk0 := hzmem k (Nat.le_of_succ_le hk)
      have hk1 := hzmem (k + 1) hk
      have hdS := gammaEntryDiffBound_of_near h hk0 hk1 hdist
      have haS := M₂.gammaEntryBound_of_near h₂ hk0 hk1 hdist
      have haS₁ := M₁.gammaEntryBound_of_near h₁ hk0 hk1 hdist
      have hcomp₁ : M₁.gammaMap (z (k + 1)) x =
          M₁.gammaMap (z (k + 1)) (z k) ∘ₗ M₁.gammaMap (z k) x :=
        (M₁.gammaMap_comp (z (k + 1)) (z k) x).symm
      have hcomp₂ : M₂.gammaMap (z (k + 1)) x =
          M₂.gammaMap (z (k + 1)) (z k) ∘ₗ M₂.gammaMap (z k) x :=
        (M₂.gammaMap_comp (z (k + 1)) (z k) x).symm
      have hb0 : 0 ≤ ((Fintype.card ι : ℝ) * max 1 C) ^ k := pow_nonneg (mul_nonneg hN0 hB0) _
      have hD0 : 0 ≤ max 0 δ := le_max_left _ _
      refine ⟨?_, ?_⟩
      · have := GammaEntryBound.comp (M₁.isGradedUnipotent_gammaMap (z k) x) hB0 hb0 haS₁ ihb
        rw [hcomp₁]
        have e : (Fintype.card ι : ℝ) * (((Fintype.card ι : ℝ) * max 1 C) ^ k * max 1 C) =
            ((Fintype.card ι : ℝ) * max 1 C) ^ (k + 1) := by ring
        rwa [e] at this
      · have := GammaEntryDiffBound.comp (A₁ := M₁.gammaMap (z (k + 1)) (z k))
          (A₂ := M₂.gammaMap (z (k + 1)) (z k)) (M₁.isGradedUnipotent_gammaMap (z k) x)
          (M₂.isGradedUnipotent_gammaMap (z k) x) hD0 (gammaDiffStep_nonneg _ _ _ k) hB0 hb0
          haS ihb hdS ihd
        rw [hcomp₁, hcomp₂]
        exact this
  have hzm : z m = y := by
    simp only [hz]
    rw [div_self hm0.ne', one_smul, add_sub_cancel]
  have := (key m le_rfl).2
  rwa [hzm] at this

/-- **Chaining for differences**. -/
theorem GammaDiffBoundNearOn.of_one (hS : SegmentClosed S) (h₁ : M₁.GammaBoundNearOn γ C 1 S)
    (h₂ : M₂.GammaBoundNearOn γ C 1 S) (h : M₁.GammaDiffBoundNearOn M₂ γ δ 1 S)
    {R : ℝ} {m : ℕ} (hm : 1 ≤ m) (hRm : R ^ 2 ≤ m) :
    M₁.GammaDiffBoundNearOn M₂ γ (gammaDiffChainConst (Fintype.card ι) C δ m) R S := by
  intro i j hi hj x hx y hy hd
  have hd0 : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg _ _
  have hp0 : 0 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
    Real.rpow_nonneg hd0 _
  by_cases hle : parabolicSemigroup.scaleDist y x ≤ 1
  · exact (h i j hi hj x hx y hy hle).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hp0)
  · push Not at hle
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hR : R ≤ Real.sqrt m := (le_abs_self R).trans (Real.abs_le_sqrt hRm)
    have hstep : parabolicNorm ((1 / (m : ℝ)) • (y - x)) ≤ 1 := by
      have h1 : (1 / (m : ℝ)) ≤ 1 := by
        rw [div_le_one hm0]
        exact_mod_cast hm
      refine (parabolicNorm_smul_le (by positivity) h1 _).trans ?_
      have hsq : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
      have e : Real.sqrt (1 / (m : ℝ)) = (Real.sqrt m)⁻¹ := by
        rw [one_div, Real.sqrt_inv]
      rw [e]
      have : parabolicNorm (y - x) ≤ Real.sqrt m := hd.trans hR
      calc (Real.sqrt m)⁻¹ * parabolicNorm (y - x) ≤ (Real.sqrt m)⁻¹ * Real.sqrt m :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hsq.le)
        _ = 1 := inv_mul_cancel₀ hsq.ne'
    have hchain := (gammaEntryDiffBound_chain hS h₁ h₂ h hx hy hm hstep) i j hi
    have hone : 1 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
      Real.one_le_rpow hle.le (by linarith)
    calc _ ≤ gammaDiffStep (Fintype.card ι) C δ m := hchain
      _ ≤ gammaDiffStep (Fintype.card ι) C δ m *
          parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
          le_mul_of_one_le_right (gammaDiffStep_nonneg _ _ _ _) hone
      _ ≤ gammaDiffChainConst (Fintype.card ι) C δ m *
          parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hp0

theorem GammaDiffBoundNearOn.toGammaDiffNearOn (hS : SegmentClosed S)
    (h₁ : M₁.GammaBoundNearOn γ C 1 S) (h₂ : M₂.GammaBoundNearOn γ C 1 S)
    (h : M₁.GammaDiffBoundNearOn M₂ γ δ 1 S) :
    M₁.GammaDiffNearOn M₂ γ (gammaDiffChainConst (Fintype.card ι) C δ 16) S :=
  GammaDiffBoundNearOn.of_one hS h₁ h₂ h (m := 16) (by norm_num)
    (by unfold gammaNearRadius; norm_num)

end Model

end RegularityStructures

end

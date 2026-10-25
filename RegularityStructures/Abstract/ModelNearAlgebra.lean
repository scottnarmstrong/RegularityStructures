/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ModelNear

/-!
# Entry bounds for products of graded unipotent maps

`GammaEntryBound 𝒯 γ b A` says `|(A e_i)_j| ≤ b` for every `i` with `deg i < γ` and every `j`.
For graded unipotent `A, B`, the entries of `A ∘ B` are bounded by `|ι| b_A b_B`
(`GammaEntryBound.comp`), and those of `A₁ B₁ - A₂ B₂` by
`|ι| (b_{B₁} d_A + d_B b_{A₂})` (`GammaEntryDiffBound.comp`).  These are the algebraic inputs of
the chaining lemma `GammaBoundNearOn.of_near_one`.
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `|(A e_i)_j| ≤ b` for every `i` with `deg i < γ` and every `j`. -/
def GammaEntryBound (𝒯 : RegularityStructure ι) (γ b : ℝ) (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ i j, 𝒯.deg i < γ → |A (Pi.single i 1) j| ≤ b

/-- `|((A - A') e_i)_j| ≤ b` for every `i` with `deg i < γ` and every `j`. -/
def GammaEntryDiffBound (𝒯 : RegularityStructure ι) (γ b : ℝ)
    (A A' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ i j, 𝒯.deg i < γ → |A (Pi.single i 1) j - A' (Pi.single i 1) j| ≤ b

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {γ : ℝ}

theorem linearMap_apply_eq_sum_coord (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ) (j : ι) :
    A v j = ∑ k, v k * A (Pi.single k 1) j := by
  conv_lhs => rw [eq_sum_single v]
  simp [map_sum, map_smul, Finset.sum_apply]

/-- The coordinates of `B e_i` vanish in degrees above `deg i`. -/
theorem IsGradedUnipotent.deg_le_of_apply_single_ne_zero {B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hB : IsGradedUnipotent 𝒯.deg B) {i k : ι} (hk : B (Pi.single i 1) k ≠ 0) :
    𝒯.deg k ≤ 𝒯.deg i := by
  by_contra h
  push Not at h
  by_cases hki : k = i
  · subst hki
    exact lt_irrefl _ h
  · exact hk (hB.apply_single_of_le hki h.le)

/-- The coordinates of `(B₁ - B₂) e_i` vanish in degrees above `deg i`. -/
theorem IsGradedUnipotent.deg_le_of_sub_apply_single_ne_zero {B₁ B₂ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (h₁ : IsGradedUnipotent 𝒯.deg B₁) (h₂ : IsGradedUnipotent 𝒯.deg B₂) {i k : ι}
    (hk : B₁ (Pi.single i 1) k - B₂ (Pi.single i 1) k ≠ 0) : 𝒯.deg k ≤ 𝒯.deg i := by
  by_contra h
  push Not at h
  by_cases hki : k = i
  · subst hki
    exact lt_irrefl _ h
  · exact hk (by rw [h₁.apply_single_of_le hki h.le, h₂.apply_single_of_le hki h.le, sub_self])

theorem GammaEntryBound.comp {A B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {a b : ℝ}
    (hB : IsGradedUnipotent 𝒯.deg B) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hA : GammaEntryBound 𝒯 γ a A)
    (hBb : GammaEntryBound 𝒯 γ b B) : GammaEntryBound 𝒯 γ (Fintype.card ι * (b * a)) (A ∘ₗ B) := by
  intro i j hi
  rw [LinearMap.comp_apply, linearMap_apply_eq_sum_coord]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k, |B (Pi.single i 1) k * A (Pi.single k 1) j| ≤ b * a := by
    intro k
    by_cases hk : B (Pi.single i 1) k = 0
    · rw [hk, zero_mul, abs_zero]
      exact mul_nonneg hb0 ha0
    · rw [abs_mul]
      exact mul_le_mul (hBb i k hi) (hA k j ((hB.deg_le_of_apply_single_ne_zero hk).trans_lt hi))
        (abs_nonneg _) hb0
  calc ∑ k, |B (Pi.single i 1) k * A (Pi.single k 1) j| ≤ ∑ _k : ι, b * a :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = Fintype.card ι * (b * a) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem GammaEntryDiffBound.comp {A₁ A₂ B₁ B₂ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {a₂ b₁ dA dB : ℝ}
    (hB₁ : IsGradedUnipotent 𝒯.deg B₁) (hB₂ : IsGradedUnipotent 𝒯.deg B₂)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁)
    (hA₂ : GammaEntryBound 𝒯 γ a₂ A₂) (hB₁b : GammaEntryBound 𝒯 γ b₁ B₁)
    (hdAb : GammaEntryDiffBound 𝒯 γ dA A₁ A₂) (hdBb : GammaEntryDiffBound 𝒯 γ dB B₁ B₂) :
    GammaEntryDiffBound 𝒯 γ (Fintype.card ι * (b₁ * dA) + Fintype.card ι * (dB * a₂))
      (A₁ ∘ₗ B₁) (A₂ ∘ₗ B₂) := by
  intro i j hi
  have e : (A₁ ∘ₗ B₁) (Pi.single i 1) j - (A₂ ∘ₗ B₂) (Pi.single i 1) j =
      ∑ k, B₁ (Pi.single i 1) k * (A₁ (Pi.single k 1) j - A₂ (Pi.single k 1) j) +
        ∑ k, (B₁ (Pi.single i 1) k - B₂ (Pi.single i 1) k) * A₂ (Pi.single k 1) j := by
    have h1 := linearMap_apply_eq_sum_coord A₁ (B₁ (Pi.single i 1)) j
    have h2 := linearMap_apply_eq_sum_coord A₂ (B₂ (Pi.single i 1)) j
    simp only [LinearMap.comp_apply, h1, h2, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k, |B₁ (Pi.single i 1) k * (A₁ (Pi.single k 1) j - A₂ (Pi.single k 1) j)| ≤
        b₁ * dA := by
      intro k
      by_cases hk : B₁ (Pi.single i 1) k = 0
      · rw [hk, zero_mul, abs_zero]
        exact mul_nonneg hb₁ hdA
      · rw [abs_mul]
        exact mul_le_mul (hB₁b i k hi)
          (hdAb k j ((hB₁.deg_le_of_apply_single_ne_zero hk).trans_lt hi)) (abs_nonneg _) hb₁
    calc _ ≤ ∑ _k : ι, b₁ * dA := Finset.sum_le_sum fun k _ => hterm k
      _ = Fintype.card ι * (b₁ * dA) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k, |(B₁ (Pi.single i 1) k - B₂ (Pi.single i 1) k) * A₂ (Pi.single k 1) j| ≤
        dB * a₂ := by
      intro k
      by_cases hk : B₁ (Pi.single i 1) k - B₂ (Pi.single i 1) k = 0
      · rw [hk, zero_mul, abs_zero]
        exact mul_nonneg hdB ha₂
      · rw [abs_mul]
        exact mul_le_mul (hdBb i k hi)
          (hA₂ k j ((hB₁.deg_le_of_sub_apply_single_ne_zero hB₂ hk).trans_lt hi)) (abs_nonneg _) hdB
    calc _ ≤ ∑ _k : ι, dB * a₂ := Finset.sum_le_sum fun k _ => hterm k
      _ = Fintype.card ι * (dB * a₂) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem GammaEntryBound.id : GammaEntryBound 𝒯 γ 1 (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
  intro i j _
  rw [LinearMap.id_apply, Pi.single_apply]
  split_ifs <;> simp

theorem GammaEntryDiffBound.self (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    GammaEntryDiffBound 𝒯 γ 0 A A := by
  intro i j _
  simp

end RegularityStructures

end

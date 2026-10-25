/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Weighted.Defs
public import RegularityStructures.Analysis.Semigroup.Germ

/-!
# Weighted germs and weighted coherence

`IsWeightedGerm` and `IsWeightedCoherent`: germs whose diagonal grows like a moderate weight `ρ`,
and coherence `|F_y(t, z) - F_z(t, z)| ≤ C ρ(z) ∑_{a ∈ A} t^{a/ℓ} d(z, y)^{γ - a}`; the constants of
the weighted reconstruction bound, and linearity of both notions.

Source: [Hos25, Theorem 4.1].
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- Germ with diagonal of growth `ρ`: `F y ∈ distributions`, diagonal measurable,
`|F y t y| ≤ B_t ρ(y)` for `0 < t ≤ 1`. -/
structure IsWeightedGerm (F : E → ℝ → E → ℝ) (ρ : E → ℝ) : Prop where
  mem : ∀ y, F y ∈ K.distributions
  measurable_diag : ∀ ⦃t : ℝ⦄, 0 < t → Measurable (diag F t)
  bounded_diag : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) 1 → ∃ B, ∀ y, |diag F t y| ≤ B * ρ y

/-- Weighted coherence:
`|F y t z - F z t z| ≤ C ρ(z) ∑_{a ∈ A} t^{a/ℓ} d(z, y)^{γ - a}` for `0 < t ≤ 1`. -/
def IsWeightedCoherent (F : E → ℝ → E → ℝ) (ρ : E → ℝ) (γ : ℝ) (A : Finset ℝ) (C : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) 1 → ∀ y z,
    |F y t z - F z t z| ≤ C * ρ z * ∑ a ∈ A, t ^ (a / K.order) * K.scaleDist z y ^ (γ - a)

/-- `κ_w = ∑_{a ∈ A} 2^p (M_{γ-a} + M_{γ-a+p}) 2^{max(0,-a)/ℓ}`. -/
def weightedCoherenceConst (p γ : ℝ) (A : Finset ℝ) : ℝ :=
  ∑ a ∈ A, (2 : ℝ) ^ p * (K.momentConst (γ - a) + K.momentConst (γ - a + p)) *
    2 ^ (max 0 (-a) / K.order)

/-- The constant of the weighted reconstruction bound on `(0, τ]`, `τ ≥ 1`. -/
def weightedReconstructionConstAt (τ p γ : ℝ) (A : Finset ℝ) : ℝ :=
  2 * (max 1 (K.weightConst p τ) * K.weightedCoherenceConst p γ A) / (1 - 2 ^ (-(γ / K.order)))

/-- The constant of the weighted reconstruction bound
`|RF_t(x) - F_x(t, x)| ≤ weightedReconstructionConst p γ A * C * ρ(x) * t^{γ/ℓ}` for
`0 < t ≤ 1`; it depends only on `K`, `p`, `γ`, `A`. -/
def weightedReconstructionConst (p γ : ℝ) (A : Finset ℝ) : ℝ :=
  K.weightedReconstructionConstAt 1 p γ A

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

variable {K}

variable (K)

theorem weightedCoherenceConst_nonneg (p γ : ℝ) (A : Finset ℝ) :
    0 ≤ K.weightedCoherenceConst p γ A :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (K.momentConst_nonneg _) (K.momentConst_nonneg _)))
      (Real.rpow_nonneg (by norm_num) _)

theorem weightedReconstructionConstAt_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (τ p : ℝ) (A : Finset ℝ) :
    0 ≤ K.weightedReconstructionConstAt τ p γ A := by
  unfold weightedReconstructionConstAt
  have h1 : (2 : ℝ) ^ (-(γ / K.order)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have := div_nonneg hγ K.order_pos.le; linarith)
  have := K.weightedCoherenceConst_nonneg p γ A
  exact div_nonneg (mul_nonneg zero_le_two (mul_nonneg (zero_le_one.trans (le_max_left _ _))
    this)) (by linarith)

theorem weightedReconstructionConst_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (p : ℝ) (A : Finset ℝ) :
    0 ≤ K.weightedReconstructionConst p γ A :=
  K.weightedReconstructionConstAt_nonneg hγ 1 p A

variable {K}

section Linear

variable {F G : E → ℝ → E → ℝ} {ρ : E → ℝ}

theorem IsWeightedGerm.add (hF : K.IsWeightedGerm F ρ) (hG : K.IsWeightedGerm G ρ) :
    K.IsWeightedGerm (fun y => F y + G y) ρ where
  mem y := K.distributions.add_mem (hF.mem y) (hG.mem y)
  measurable_diag _ ht := (hF.measurable_diag ht).add (hG.measurable_diag ht)
  bounded_diag _ ht := by
    obtain ⟨B, hB⟩ := hF.bounded_diag ht
    obtain ⟨B', hB'⟩ := hG.bounded_diag ht
    exact ⟨B + B', fun y => by
      rw [add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hB y) (hB' y))⟩

theorem IsWeightedGerm.smul (hF : K.IsWeightedGerm F ρ) (c : ℝ) :
    K.IsWeightedGerm (fun y => c • F y) ρ where
  mem y := K.distributions.smul_mem c (hF.mem y)
  measurable_diag _ ht := (hF.measurable_diag ht).const_mul c
  bounded_diag _ ht := by
    obtain ⟨B, hB⟩ := hF.bounded_diag ht
    exact ⟨|c| * B, fun y => by
      simp only [diag, Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)⟩

theorem IsWeightedCoherent.add {γ : ℝ} {A : Finset ℝ} {C C' : ℝ}
    (hF : K.IsWeightedCoherent F ρ γ A C) (hG : K.IsWeightedCoherent G ρ γ A C') :
    K.IsWeightedCoherent (fun y => F y + G y) ρ γ A (C + C') := by
  intro t ht y z
  have h1 := hF ht y z
  have h2 := hG ht y z
  have : (F y + G y) t z - (F z + G z) t z = (F y t z - F z t z) + (G y t z - G z t z) := by
    simp only [Pi.add_apply]; ring
  rw [this, add_mul, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem IsWeightedCoherent.smul {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hF : K.IsWeightedCoherent F ρ γ A C) (c : ℝ) :
    K.IsWeightedCoherent (fun y => c • F y) ρ γ A (|c| * C) := by
  intro t ht y z
  have h1 := hF ht y z
  have : (c • F y) t z - (c • F z) t z = c * (F y t z - F z t z) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, abs_mul]
  calc |c| * |F y t z - F z t z|
      ≤ |c| * (C * ρ z * ∑ a ∈ A, t ^ (a / K.order) * K.scaleDist z y ^ (γ - a)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

end Linear

end RegularityStructures.RegularisingSemigroup

end

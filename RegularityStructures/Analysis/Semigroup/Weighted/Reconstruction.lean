/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Weighted.Limit

/-!
# The weighted reconstruction theorem

The reconstruction theorem of [Hos25, Theorem 4.1] (arXiv:2310.07396v2) with a polynomially
moderate weight `ρ` (`p = ∞` there): for a weighted coherent germ `F` of order `γ > 0`,

* `weighted_reconstruct_mem`: `RF = lim_{s ↓ 0} R^t_s F` is a `Q`-distribution;
* `abs_reconstruct_sub_diag_le_weighted`: `|RF_t(x) - F_x(t, x)| ≤ c C ρ(x) t^{γ/ℓ}`, `0 < t ≤ 1`;
* `eq_reconstruct_weighted`: it is the unique `Q`-distribution with this property;
* linearity: `reconstruct_add_weighted`, `reconstruct_smul_weighted`, `reconstruct_sub_weighted`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  [SFinite μ] {ρ : E → ℝ} {p : ℝ} {F G : E → ℝ → E → ℝ}

theorem eq_reconstruct_weighted (hρ : K.IsModerateWeight ρ p) (hF : K.IsWeightedGerm F ρ)
    {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C)
    (hcoh : K.IsWeightedCoherent F ρ γ A C) {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions)
    {C' : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |Λ t x - F x t x| ≤ C' * ρ x * t ^ (γ / K.order)) :
    Λ = K.reconstruct F := by
  refine K.eq_of_abs_sub_le_weight hρ hΛ (K.weighted_reconstruct_mem hρ hF hγ hA hC hcoh)
    (C := C' + K.weightedReconstructionConst p γ A * C) (div_pos hγ K.order_pos)
    fun t ht x => ?_
  have h1 := hb t ht x
  have h2 := K.abs_reconstruct_sub_diag_le_weighted hρ hF hγ hA hC hcoh ht x
  calc |Λ t x - K.reconstruct F t x|
      = |(Λ t x - F x t x) + (F x t x - K.reconstruct F t x)| := by ring_nf
    _ ≤ |Λ t x - F x t x| + |F x t x - K.reconstruct F t x| := abs_add_le _ _
    _ ≤ _ := by rw [abs_sub_comm (F x t x)]; linarith

/-- The uniform-constant form of the weighted reconstruction theorem: the constant `c` is chosen
before the germ and the weight. -/
theorem exists_reconstruction_weighted (p γ : ℝ) (hγ : 0 < γ) (A : Finset ℝ)
    (hA : ∀ a ∈ A, a < γ) :
    ∃ c, 0 ≤ c ∧ ∀ ⦃ρ : E → ℝ⦄, K.IsModerateWeight ρ p → ∀ ⦃F : E → ℝ → E → ℝ⦄ ⦃C : ℝ⦄,
      K.IsWeightedGerm F ρ → 0 ≤ C → K.IsWeightedCoherent F ρ γ A C →
      K.reconstruct F ∈ K.distributions ∧
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |K.reconstruct F t x - F x t x| ≤ c * C * ρ x * t ^ (γ / K.order)) ∧
      ∀ Λ ∈ K.distributions, (∃ C', ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |Λ t x - F x t x| ≤ C' * ρ x * t ^ (γ / K.order)) → Λ = K.reconstruct F :=
  ⟨K.weightedReconstructionConst p γ A, K.weightedReconstructionConst_nonneg hγ.le p A,
    fun _ hρ _ _ hF hC hcoh =>
    ⟨K.weighted_reconstruct_mem hρ hF hγ hA hC hcoh,
      fun _ ht x => K.abs_reconstruct_sub_diag_le_weighted hρ hF hγ hA hC hcoh ht x,
      fun _ hΛ ⟨_, hb⟩ => K.eq_reconstruct_weighted hρ hF hγ hA hC hcoh hΛ hb⟩⟩

/-! ### Linearity -/

theorem reconstruct_add_weighted (hρ : K.IsModerateWeight ρ p) (hF : K.IsWeightedGerm F ρ)
    (hG : K.IsWeightedGerm G ρ) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hcF : K.IsWeightedCoherent F ρ γ A C)
    (hcG : K.IsWeightedCoherent G ρ γ A C') :
    K.reconstruct (fun y => F y + G y) = K.reconstruct F + K.reconstruct G := by
  symm
  refine K.eq_reconstruct_weighted hρ (hF.add hG) hγ hA (add_nonneg hC hC') (hcF.add hcG)
    (K.distributions.add_mem (K.weighted_reconstruct_mem hρ hF hγ hA hC hcF)
      (K.weighted_reconstruct_mem hρ hG hγ hA hC' hcG))
    (C' := K.weightedReconstructionConst p γ A * C +
      K.weightedReconstructionConst p γ A * C') fun t ht x => ?_
  have h1 := K.abs_reconstruct_sub_diag_le_weighted hρ hF hγ hA hC hcF ht x
  have h2 := K.abs_reconstruct_sub_diag_le_weighted hρ hG hγ hA hC' hcG ht x
  have : (K.reconstruct F + K.reconstruct G) t x - (fun y => F y + G y) x t x =
      (K.reconstruct F t x - F x t x) + (K.reconstruct G t x - G x t x) := by
    simp only [Pi.add_apply]; ring
  rw [this, add_mul, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem reconstruct_smul_weighted (hρ : K.IsModerateWeight ρ p) (hF : K.IsWeightedGerm F ρ)
    (c : ℝ) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C)
    (hcF : K.IsWeightedCoherent F ρ γ A C) :
    K.reconstruct (fun y => c • F y) = c • K.reconstruct F := by
  symm
  refine K.eq_reconstruct_weighted hρ (hF.smul c) hγ hA (mul_nonneg (abs_nonneg c) hC)
    (hcF.smul c) (K.distributions.smul_mem c (K.weighted_reconstruct_mem hρ hF hγ hA hC hcF))
    (C' := K.weightedReconstructionConst p γ A * (|c| * C)) fun t ht x => ?_
  have h1 := K.abs_reconstruct_sub_diag_le_weighted hρ hF hγ hA hC hcF ht x
  have : (c • K.reconstruct F) t x - (fun y => c • F y) x t x =
      c * (K.reconstruct F t x - F x t x) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, abs_mul]
  calc |c| * |K.reconstruct F t x - F x t x|
      ≤ |c| * (K.weightedReconstructionConst p γ A * C * ρ x * t ^ (γ / K.order)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

theorem reconstruct_sub_weighted (hρ : K.IsModerateWeight ρ p) (hF : K.IsWeightedGerm F ρ)
    (hG : K.IsWeightedGerm G ρ) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ)
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hcF : K.IsWeightedCoherent F ρ γ A C)
    (hcG : K.IsWeightedCoherent G ρ γ A C') :
    K.reconstruct (fun y => F y - G y) = K.reconstruct F - K.reconstruct G := by
  have e : (fun y => F y - G y) = fun y => F y + (-1 : ℝ) • G y := by
    funext y; simp [sub_eq_add_neg]
  rw [e, K.reconstruct_add_weighted hρ hF (hG.smul (-1)) hγ hA hC
    (mul_nonneg (abs_nonneg _) hC') hcF (hcG.smul (-1)),
    K.reconstruct_smul_weighted hρ hG (-1) hγ hA hC' hcG]
  simp [sub_eq_add_neg]

end RegularityStructures.RegularisingSemigroup

end

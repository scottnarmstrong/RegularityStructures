/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Reconstruction.Limit

/-!
# The reconstruction theorem for germs

The reconstruction theorem of [Hos25, Theorem 4.1] (arXiv:2310.07396v2), for `p = ∞`,
`w = v = 1`, in the representation of distributions by their `Q`-families: for a coherent germ `F` of
order `γ > 0`,

* `reconstruct_mem`: `RF = lim_{s ↓ 0} R^t_s F` is a `Q`-distribution;
* `abs_reconstruct_sub_diag_le`: `|RF_t(x) - F_x(t, x)| ≤ c C t^{γ/ℓ}` for `0 < t ≤ 1`;
* `eq_reconstruct`: it is the unique `Q`-distribution with this property;
* `exists_reconstruction`: the constant `c` depends only on `K, γ, A`;
* linearity (`reconstruct_add`, `reconstruct_smul`, `reconstruct_sub`) and the bound
  `abs_reconstruct_le` in negative regularity.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  [SFinite μ] {F : E → ℝ → E → ℝ}

theorem eq_reconstruct (hF : K.IsGerm F) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C)
    {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {C' : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |Λ t x - F x t x| ≤ C' * t ^ (γ / K.order)) :
    Λ = K.reconstruct F := by
  refine K.eq_of_abs_sub_le hΛ (K.reconstruct_mem hF hγ hA hC hcoh)
    (C := C' + K.reconstructionConst γ A * C) (div_pos hγ K.order_pos) fun t ht x => ?_
  have h1 := hb t ht x
  have h2 := K.abs_reconstruct_sub_diag_le hF hγ hA hC hcoh ht x
  calc |Λ t x - K.reconstruct F t x|
      = |(Λ t x - F x t x) + (F x t x - K.reconstruct F t x)| := by ring_nf
    _ ≤ |Λ t x - F x t x| + |F x t x - K.reconstruct F t x| := abs_add_le _ _
    _ ≤ _ := by rw [abs_sub_comm (F x t x)]; linarith

/-- The uniform-constant form of the reconstruction theorem [Hos25, Theorem 4.1]: the constant
`c` is chosen before the germ. -/
theorem exists_reconstruction (γ : ℝ) (hγ : 0 < γ) (A : Finset ℝ) (hA : ∀ a ∈ A, a < γ) :
    ∃ c, 0 ≤ c ∧ ∀ ⦃F : E → ℝ → E → ℝ⦄ ⦃C : ℝ⦄, K.IsGerm F → 0 ≤ C → K.IsCoherent F γ A C →
      K.reconstruct F ∈ K.distributions ∧
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |K.reconstruct F t x - F x t x| ≤ c * C * t ^ (γ / K.order)) ∧
      ∀ Λ ∈ K.distributions, (∃ C', ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |Λ t x - F x t x| ≤ C' * t ^ (γ / K.order)) → Λ = K.reconstruct F :=
  ⟨K.reconstructionConst γ A, K.reconstructionConst_nonneg hγ.le A, fun _ _ hF hC hcoh =>
    ⟨K.reconstruct_mem hF hγ hA hC hcoh,
      fun _ ht x => K.abs_reconstruct_sub_diag_le hF hγ hA hC hcoh ht x,
      fun _ hΛ ⟨_, hb⟩ => K.eq_reconstruct hF hγ hA hC hcoh hΛ hb⟩⟩

/-! ### Linearity -/

variable {G : E → ℝ → E → ℝ}

section Linear

omit [SFinite μ]

variable {K}

theorem IsGerm.add (hF : K.IsGerm F) (hG : K.IsGerm G) : K.IsGerm (fun y => F y + G y) where
  mem y := K.distributions.add_mem (hF.mem y) (hG.mem y)
  measurable_diag _ ht := (hF.measurable_diag ht).add (hG.measurable_diag ht)
  bounded_diag _ ht := by
    obtain ⟨B, hB⟩ := hF.bounded_diag ht
    obtain ⟨B', hB'⟩ := hG.bounded_diag ht
    exact ⟨B + B', fun y => (abs_add_le _ _).trans (add_le_add (hB y) (hB' y))⟩

theorem IsGerm.smul (hF : K.IsGerm F) (c : ℝ) : K.IsGerm (fun y => c • F y) where
  mem y := K.distributions.smul_mem c (hF.mem y)
  measurable_diag _ ht := (hF.measurable_diag ht).const_mul c
  bounded_diag _ ht := by
    obtain ⟨B, hB⟩ := hF.bounded_diag ht
    exact ⟨|c| * B, fun y => by
      simp only [diag, Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)⟩

theorem IsCoherent.add {γ : ℝ} {A : Finset ℝ} {C C' : ℝ} (hF : K.IsCoherent F γ A C)
    (hG : K.IsCoherent G γ A C') :
    K.IsCoherent (fun y => F y + G y) γ A (C + C') := by
  intro t ht y z
  have h1 := hF ht y z
  have h2 := hG ht y z
  have : (F y + G y) t z - (F z + G z) t z = (F y t z - F z t z) + (G y t z - G z t z) := by
    simp only [Pi.add_apply]; ring
  rw [this, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem IsCoherent.smul {γ : ℝ} {A : Finset ℝ} {C : ℝ} (hF : K.IsCoherent F γ A C) (c : ℝ) :
    K.IsCoherent (fun y => c • F y) γ A (|c| * C) := by
  intro t ht y z
  have h1 := hF ht y z
  have : (c • F y) t z - (c • F z) t z = c * (F y t z - F z t z) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

end Linear

theorem reconstruct_add (hF : K.IsGerm F) (hG : K.IsGerm G) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hcF : K.IsCoherent F γ A C) (hcG : K.IsCoherent G γ A C') :
    K.reconstruct (fun y => F y + G y) = K.reconstruct F + K.reconstruct G := by
  symm
  refine K.eq_reconstruct (hF.add hG) hγ hA (add_nonneg hC hC') (hcF.add hcG)
    (K.distributions.add_mem (K.reconstruct_mem hF hγ hA hC hcF)
      (K.reconstruct_mem hG hγ hA hC' hcG))
    (C' := K.reconstructionConst γ A * C + K.reconstructionConst γ A * C') fun t ht x => ?_
  have h1 := K.abs_reconstruct_sub_diag_le hF hγ hA hC hcF ht x
  have h2 := K.abs_reconstruct_sub_diag_le hG hγ hA hC' hcG ht x
  have : (K.reconstruct F + K.reconstruct G) t x - (fun y => F y + G y) x t x =
      (K.reconstruct F t x - F x t x) + (K.reconstruct G t x - G x t x) := by
    simp only [Pi.add_apply]; ring
  rw [this, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem reconstruct_smul (hF : K.IsGerm F) (c : ℝ) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcF : K.IsCoherent F γ A C) :
    K.reconstruct (fun y => c • F y) = c • K.reconstruct F := by
  symm
  refine K.eq_reconstruct (hF.smul c) hγ hA (mul_nonneg (abs_nonneg c) hC) (hcF.smul c)
    (K.distributions.smul_mem c (K.reconstruct_mem hF hγ hA hC hcF))
    (C' := K.reconstructionConst γ A * (|c| * C)) fun t ht x => ?_
  have h1 := K.abs_reconstruct_sub_diag_le hF hγ hA hC hcF ht x
  have : (c • K.reconstruct F) t x - (fun y => c • F y) x t x =
      c * (K.reconstruct F t x - F x t x) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, abs_mul]
  calc |c| * |K.reconstruct F t x - F x t x|
      ≤ |c| * (K.reconstructionConst γ A * C * t ^ (γ / K.order)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

theorem reconstruct_sub (hF : K.IsGerm F) (hG : K.IsGerm G) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hcF : K.IsCoherent F γ A C) (hcG : K.IsCoherent G γ A C') :
    K.reconstruct (fun y => F y - G y) = K.reconstruct F - K.reconstruct G := by
  have e : (fun y => F y - G y) = fun y => F y + (-1 : ℝ) • G y := by
    funext y; simp [sub_eq_add_neg]
  rw [e, K.reconstruct_add hF (hG.smul (-1)) hγ hA hC (mul_nonneg (abs_nonneg _) hC') hcF
    (hcG.smul (-1)), K.reconstruct_smul hG (-1) hγ hA hC' hcG]
  simp [sub_eq_add_neg]

/-- The bound for the reconstruction in nonpositive regularity: if
`|F_y(t, y)| ≤ B t^{α/ℓ}` with `α ≤ 0 < γ` then `|RF_t(x)| ≤ (B + c C) t^{α/ℓ}`. -/
theorem abs_reconstruct_le (hF : K.IsGerm F) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C) {α B : ℝ}
    (hα : α ≤ 0)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, |F y t y| ≤ B * t ^ (α / K.order)) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |K.reconstruct F t x| ≤ (B + K.reconstructionConst γ A * C) * t ^ (α / K.order) := by
  have h1 := K.abs_reconstruct_sub_diag_le hF hγ hA hC hcoh ht x
  have h2 := hB t ht x
  have h3 : t ^ (γ / K.order) ≤ t ^ (α / K.order) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
      (div_le_div_of_nonneg_right (hα.trans hγ.le) K.order_pos.le)
  have h4 : 0 ≤ K.reconstructionConst γ A * C :=
    mul_nonneg (K.reconstructionConst_nonneg hγ.le A) hC
  calc |K.reconstruct F t x|
      = |(K.reconstruct F t x - F x t x) + F x t x| := by ring_nf
    _ ≤ |K.reconstruct F t x - F x t x| + |F x t x| := abs_add_le _ _
    _ ≤ K.reconstructionConst γ A * C * t ^ (γ / K.order) + B * t ^ (α / K.order) :=
        add_le_add h1 h2
    _ ≤ K.reconstructionConst γ A * C * t ^ (α / K.order) + B * t ^ (α / K.order) := by
        gcongr
    _ = _ := by ring

end RegularityStructures.RegularisingSemigroup

end

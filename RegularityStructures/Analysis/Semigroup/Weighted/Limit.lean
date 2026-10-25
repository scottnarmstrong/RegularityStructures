/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.DyadicLimit
public import RegularityStructures.Analysis.Semigroup.Weighted.Increment

/-!
# The limit `s ↓ 0` of the approximations `R^t_s F`, weighted

Steps (c)-(d) of the proof of [Hos25, Theorem 4.1] (arXiv:2310.07396v2) for a weighted coherent
germ. The reconstruction is the same `K.reconstruct F`; only the hypotheses and bounds change.

* `tendsto_approx_weighted`: `R^t_s F(x) → RF_t(x)` with the rate
  `|R^t_s F(x) - RF_t(x)| ≤ c_{max t 1} C ρ(x) s^{γ/ℓ}` for `s ≤ min t 1`;
* `measurable_reconstruct_weighted`, `exists_weight_bound_reconstruct`;
* `apply_reconstruct_weighted`: `Q_r RF_t = RF_{t+r}`;
* `weighted_reconstruct_mem`: `RF` is a `Q`-distribution;
* `abs_reconstruct_sub_diag_le_weighted`: `|RF_t(x) - F_x(t, x)| ≤ c C ρ(x) t^{γ/ℓ}` for
  `0 < t ≤ 1`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  [SFinite μ] {ρ : E → ℝ} {p : ℝ} (hρ : K.IsModerateWeight ρ p)
  {F : E → ℝ → E → ℝ} (hF : K.IsWeightedGerm F ρ) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
  (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsWeightedCoherent F ρ γ A C)

include hρ hF hγ hA hC hcoh

theorem tendsto_approx_weighted {t : ℝ} (ht : 0 < t) (x : E) :
    Tendsto (fun s => K.approx F t s x) (𝓝[>] 0) (𝓝 (K.reconstruct F t x)) ∧
      ∀ s, 0 < s → s ≤ t → s ≤ 1 →
        |K.approx F t s x - K.reconstruct F t x| ≤
          K.weightedReconstructionConstAt (max t 1) p γ A * C * ρ x * s ^ (γ / K.order) := by
  have hβ : 0 < γ / K.order := div_pos hγ K.order_pos
  have hL : 0 ≤ max 1 (K.weightConst p (max t 1)) *
      (C * K.weightedCoherenceConst p γ A * ρ x) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (mul_nonneg (mul_nonneg hC (K.weightedCoherenceConst_nonneg p γ A)) (hρ.pos x).le)
  obtain ⟨φ₀, hφ, hb⟩ := exists_tendsto_of_dyadic_bound
    (φ := fun s => K.approx F t s x) (S := min t 1) (L := max 1 (K.weightConst p (max t 1)) *
      (C * K.weightedCoherenceConst p γ A * ρ x)) (β := γ / K.order) (lt_min ht one_pos) hβ hL
    (fun s u hs hsS hsu hus => by
      have h := K.abs_approx_sub_approx_le_weight hρ hF hA hC hcoh (τ := max t 1) (by linarith)
        hus hsu (hsS.trans (min_le_left _ _)) (le_max_left _ _)
        (hsS.trans (min_le_right _ _)) x
      calc _ ≤ _ := h
        _ = _ := by ring)
  have hrec : K.reconstruct F t x = φ₀ := by
    simp only [reconstruct, ht, ↓reduceIte]
    exact hφ.limUnder_eq
  rw [hrec]
  refine ⟨hφ, fun s hs hst hs1 => ?_⟩
  refine (hb s hs (le_min hst hs1)).trans (le_of_eq ?_)
  unfold weightedReconstructionConstAt
  ring

theorem abs_approx_sub_reconstruct_le_weighted {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (hs1 : s ≤ 1) (x : E) :
    |K.approx F t s x - K.reconstruct F t x| ≤
      K.weightedReconstructionConstAt (max t 1) p γ A * C * ρ x * s ^ (γ / K.order) :=
  (K.tendsto_approx_weighted hρ hF hγ hA hC hcoh ht x).2 s hs hst hs1

theorem exists_weight_bound_reconstruct {t : ℝ} (ht : 0 < t) :
    ∃ B, ∀ x, |K.reconstruct F t x| ≤ B * ρ x := by
  have hs : min t 1 ∈ Ioc (0 : ℝ) 1 := ⟨lt_min ht one_pos, min_le_right _ _⟩
  obtain ⟨B, hB⟩ := K.bounded_approx_weight hρ (t := t) hF hs
  refine ⟨B + K.weightedReconstructionConstAt (max t 1) p γ A * C * min t 1 ^ (γ / K.order),
    fun x => ?_⟩
  have h := K.abs_approx_sub_reconstruct_le_weighted hρ hF hγ hA hC hcoh ht hs.1
    (min_le_left _ _) hs.2 x
  have := hB x
  calc |K.reconstruct F t x|
      = |K.approx F t (min t 1) x - (K.approx F t (min t 1) x - K.reconstruct F t x)| := by
        ring_nf
    _ ≤ |K.approx F t (min t 1) x| + |K.approx F t (min t 1) x - K.reconstruct F t x| :=
        abs_sub _ _
    _ ≤ _ := by linarith

omit hρ hγ hA hC hcoh in
theorem measurable_approx_weighted {t s : ℝ} (hs : 0 < s) : Measurable (K.approx F t s) := by
  rcases lt_or_ge s t with h | h
  · rw [K.approx_of_lt F h]
    exact K.measurable_apply _ (hF.measurable_diag hs)
  · have : K.approx F t s = diag F s := by funext x; simp [approx, not_lt.2 h]
    rw [this]
    exact hF.measurable_diag hs

theorem measurable_reconstruct_weighted {t : ℝ} (ht : 0 < t) : Measurable (K.reconstruct F t) := by
  set S := min t 1 with hS
  have hSpos : 0 < S := lt_min ht one_pos
  have hT : Tendsto (fun n : ℕ => S / 2 ^ (n + 1)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => by
      simp only [mem_Ioi]; positivity⟩
    have h0 : Tendsto (fun n : ℕ => S / 2 ^ n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, ← inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
          (by norm_num)).const_mul S
    exact h0.comp (tendsto_add_atTop_nat 1)
  refine measurable_of_tendsto_metrizable (f := fun n => K.approx F t (S / 2 ^ (n + 1)))
    (fun n => K.measurable_approx_weighted hF (by positivity)) (tendsto_pi_nhds.2 fun x => ?_)
  exact ((K.tendsto_approx_weighted hρ hF hγ hA hC hcoh ht x).1).comp hT

omit hγ hA hC hcoh in
theorem apply_approx_weighted {t s r : ℝ} (hs : 0 < s) (hst : s < t) (hs1 : s ≤ 1) (hr : 0 < r)
    (x : E) : K.apply r (K.approx F t s) x = K.approx F (t + r) s x := by
  obtain ⟨B, hB⟩ := hF.bounded_diag ⟨hs, hs1⟩
  rw [K.approx_of_lt F hst, K.approx_of_lt F (show s < t + r by linarith),
    K.apply_apply_of_weight_bound hρ hr (sub_pos.2 hst) (hF.measurable_diag hs) hB]
  congr 1
  ring

theorem tendsto_apply_approx_weighted {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : E) :
    Tendsto (fun s => K.apply r (K.approx F t s) x) (𝓝[>] 0)
      (𝓝 (K.apply r (K.reconstruct F t) x)) := by
  obtain ⟨BR, hBR⟩ := K.exists_weight_bound_reconstruct hρ hF hγ hA hC hcoh ht
  have hmR := K.measurable_reconstruct_weighted hρ hF hγ hA hC hcoh ht
  have hS : (0 : ℝ) < min t 1 := lt_min ht one_pos
  set c := K.weightedReconstructionConstAt (max t 1) p γ A * C with hc
  have hβ : 0 < γ / K.order := div_pos hγ K.order_pos
  have h0 : Tendsto (fun s : ℝ => (c * ρ x * K.weightConst p r) * s ^ (γ / K.order))
      (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_rpow_const hβ.le).const_mul
      (c * ρ x * K.weightConst p r)).tendsto 0
    rw [Real.zero_rpow hβ.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
    dist_nonneg) ?_ h0)
  filter_upwards [Ioc_mem_nhdsGT hS] with s hs
  have hs1 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
  have hst : s ≤ t := hs.2.trans (min_le_left _ _)
  obtain ⟨B, hB⟩ := K.bounded_approx_weight hρ (t := t) hF hs1
  have i1 := K.integrable_kernel_mul_of_weight_bound hρ hr x
    (K.measurable_approx_weighted hF hs.1) hB
  have i2 := K.integrable_kernel_mul_of_weight_bound hρ hr x hmR hBR
  rw [Real.dist_eq, ← K.apply_sub x i1 i2]
  have h := K.abs_apply_le_of_weight_bound hρ hr (B := c * s ^ (γ / K.order))
    (g := fun y => K.approx F t s y - K.reconstruct F t y) (fun y => by
      have := K.abs_approx_sub_reconstruct_le_weighted hρ hF hγ hA hC hcoh ht hs.1 hst hs1.2 y
      rw [hc]
      linarith) x
  refine h.trans (le_of_eq ?_)
  ring

theorem apply_reconstruct_weighted {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : E) :
    K.apply r (K.reconstruct F t) x = K.reconstruct F (t + r) x := by
  have h1 := K.tendsto_apply_approx_weighted hρ hF hγ hA hC hcoh ht hr x
  have h2 := (K.tendsto_approx_weighted hρ hF hγ hA hC hcoh (show 0 < t + r by linarith) x).1
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (lt_min ht one_pos)] with s hs
  exact (K.apply_approx_weighted hρ hF hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _))
    (hs.2.le.trans (min_le_right _ _)) hr x).symm

/-- The reconstruction of a weighted coherent germ is a `Q`-distribution
([Hos25, proof of Theorem 4.1], with weights). -/
theorem weighted_reconstruct_mem : K.reconstruct F ∈ K.distributions := by
  refine ⟨fun t ht => funext fun x => by simp [reconstruct, not_lt.2 ht], fun s t hs ht x => ?_⟩
  obtain ⟨B, hB⟩ := K.exists_weight_bound_reconstruct hρ hF hγ hA hC hcoh ht
  refine ⟨K.integrable_kernel_mul_of_weight_bound hρ hs x
    (K.measurable_reconstruct_weighted hρ hF hγ hA hC hcoh ht) hB, ?_⟩
  rw [K.apply_reconstruct_weighted hρ hF hγ hA hC hcoh ht hs x, add_comm]

/-- `|RF_t(x) - F_x(t, x)| ≤ c C ρ(x) t^{γ/ℓ}` for `0 < t ≤ 1`
([Hos25, Theorem 4.1], the reconstruction bound, with weights). -/
theorem abs_reconstruct_sub_diag_le_weighted {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |K.reconstruct F t x - F x t x| ≤
      K.weightedReconstructionConst p γ A * C * ρ x * t ^ (γ / K.order) := by
  have h := K.abs_approx_sub_reconstruct_le_weighted hρ hF hγ hA hC hcoh ht.1 ht.1 le_rfl ht.2 x
  rw [K.approx_self, max_eq_right ht.2] at h
  rw [abs_sub_comm]
  exact h

end RegularityStructures.RegularisingSemigroup

end

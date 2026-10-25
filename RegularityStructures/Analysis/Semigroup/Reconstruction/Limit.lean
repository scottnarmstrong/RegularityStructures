/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.DyadicLimit
public import RegularityStructures.Analysis.Semigroup.Reconstruction.Increment

/-!
# The limit `s ↓ 0` of the approximations `R^t_s F`

Steps (c)-(d) of the proof of [Hos25, Theorem 4.1] (arXiv:2310.07396v2), for a coherent germ:

* `tendsto_approx`: `R^t_s F(x)` converges as `s ↓ 0` to `reconstruct F t x`, with the rate
  `|R^t_s F(x) - RF_t(x)| ≤ c C s^{γ/ℓ}` for `s ≤ min t 1`;
* `measurable_reconstruct`, `bounded_reconstruct`;
* `apply_reconstruct`: `Q_r RF_t = RF_{t+r}`;
* `reconstruct_mem`: `RF` is a `Q`-distribution;
* `abs_reconstruct_sub_diag_le`: `|RF_t(x) - F_x(t, x)| ≤ c C t^{γ/ℓ}` for `0 < t ≤ 1`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  [SFinite μ] {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {γ : ℝ} (hγ : 0 < γ) {A : Finset ℝ}
  (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C)

include hF hγ hA hC hcoh

theorem tendsto_approx {t : ℝ} (ht : 0 < t) (x : E) :
    Tendsto (fun s => K.approx F t s x) (𝓝[>] 0) (𝓝 (K.reconstruct F t x)) ∧
      ∀ s, 0 < s → s ≤ t → s ≤ 1 →
        |K.approx F t s x - K.reconstruct F t x| ≤
          K.reconstructionConst γ A * C * s ^ (γ / K.order) := by
  have hβ : 0 < γ / K.order := div_pos hγ K.order_pos
  have hL : 0 ≤ max 1 (K.momentConst 0) * (C * K.coherenceConst γ A) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (mul_nonneg hC (K.coherenceConst_nonneg γ A))
  obtain ⟨φ₀, hφ, hb⟩ := exists_tendsto_of_dyadic_bound
    (φ := fun s => K.approx F t s x) (S := min t 1) (L := max 1 (K.momentConst 0) *
      (C * K.coherenceConst γ A)) (β := γ / K.order) (lt_min ht one_pos) hβ hL
    (fun s u hs hsS hsu hus => by
      have h := K.abs_approx_sub_approx_le hF hA hC hcoh (by linarith) hus hsu
        (hsS.trans (min_le_left _ _)) (hsS.trans (min_le_right _ _)) x
      rw [mul_assoc]
      exact h)
  have hrec : K.reconstruct F t x = φ₀ := by
    simp only [reconstruct, ht, ↓reduceIte]
    exact hφ.limUnder_eq
  rw [hrec]
  refine ⟨hφ, fun s hs hst hs1 => ?_⟩
  refine (hb s hs (le_min hst hs1)).trans (le_of_eq ?_)
  rw [reconstructionConst_eq]
  ring

theorem abs_approx_sub_reconstruct_le {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (hs1 : s ≤ 1) (x : E) :
    |K.approx F t s x - K.reconstruct F t x| ≤
      K.reconstructionConst γ A * C * s ^ (γ / K.order) :=
  (K.tendsto_approx hF hγ hA hC hcoh ht x).2 s hs hst hs1

theorem bounded_reconstruct {t : ℝ} (ht : 0 < t) : ∃ B, ∀ x, |K.reconstruct F t x| ≤ B := by
  have hs : min t 1 ∈ Ioc (0 : ℝ) 1 := ⟨lt_min ht one_pos, min_le_right _ _⟩
  obtain ⟨B, hB⟩ := K.bounded_approx (t := t) hF hs
  refine ⟨B + K.reconstructionConst γ A * C * min t 1 ^ (γ / K.order), fun x => ?_⟩
  have h := K.abs_approx_sub_reconstruct_le hF hγ hA hC hcoh ht hs.1 (min_le_left _ _)
    hs.2 x
  have := hB x
  calc |K.reconstruct F t x|
      = |K.approx F t (min t 1) x - (K.approx F t (min t 1) x - K.reconstruct F t x)| := by
        ring_nf
    _ ≤ |K.approx F t (min t 1) x| + |K.approx F t (min t 1) x - K.reconstruct F t x| :=
        abs_sub _ _
    _ ≤ _ := by linarith

theorem measurable_reconstruct {t : ℝ} (ht : 0 < t) : Measurable (K.reconstruct F t) := by
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
    (fun n => K.measurable_approx hF (by positivity)) (tendsto_pi_nhds.2 fun x => ?_)
  exact ((K.tendsto_approx hF hγ hA hC hcoh ht x).1).comp hT

omit hγ hA hC hcoh in
theorem apply_approx {t s r : ℝ} (hs : 0 < s) (hst : s < t) (hs1 : s ≤ 1) (hr : 0 < r)
    (x : E) : K.apply r (K.approx F t s) x = K.approx F (t + r) s x := by
  obtain ⟨B, hB⟩ := hF.bounded_diag ⟨hs, hs1⟩
  rw [K.approx_of_lt F hst, K.approx_of_lt F (show s < t + r by linarith),
    K.apply_apply hr (sub_pos.2 hst) (hF.measurable_diag hs) hB]
  congr 1
  ring

theorem tendsto_apply_approx {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : E) :
    Tendsto (fun s => K.apply r (K.approx F t s) x) (𝓝[>] 0)
      (𝓝 (K.apply r (K.reconstruct F t) x)) := by
  obtain ⟨BR, hBR⟩ := K.bounded_reconstruct hF hγ hA hC hcoh ht
  have hmR := K.measurable_reconstruct hF hγ hA hC hcoh ht
  have hS : (0 : ℝ) < min t 1 := lt_min ht one_pos
  have h0 : Tendsto (fun s : ℝ => K.momentConst 0 *
      (K.reconstructionConst γ A * C * s ^ (γ / K.order))) (𝓝[>] 0) (𝓝 0) := by
    have := (((Real.continuous_rpow_const (div_pos hγ K.order_pos).le).const_mul
      (K.reconstructionConst γ A * C)).const_mul (K.momentConst 0)).tendsto 0
    rw [Real.zero_rpow (div_pos hγ K.order_pos).ne', mul_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
    dist_nonneg) ?_ h0)
  filter_upwards [Ioc_mem_nhdsGT hS] with s hs
  have hs1 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
  have hst : s ≤ t := hs.2.trans (min_le_left _ _)
  obtain ⟨B, hB⟩ := K.bounded_approx (t := t) hF hs1
  have i1 := K.integrable_kernel_mul_of_bound hr x (K.measurable_approx hF hs.1) hB
  have i2 := K.integrable_kernel_mul_of_bound hr x hmR hBR
  rw [Real.dist_eq, ← K.apply_sub x i1 i2]
  exact K.abs_apply_le_of_bound hr (fun y =>
    K.abs_approx_sub_reconstruct_le hF hγ hA hC hcoh ht hs.1 hst hs1.2 y) x

theorem apply_reconstruct {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : E) :
    K.apply r (K.reconstruct F t) x = K.reconstruct F (t + r) x := by
  have h1 := K.tendsto_apply_approx hF hγ hA hC hcoh ht hr x
  have h2 := (K.tendsto_approx hF hγ hA hC hcoh (show 0 < t + r by linarith) x).1
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (lt_min ht one_pos)] with s hs
  exact (K.apply_approx hF hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _))
    (hs.2.le.trans (min_le_right _ _)) hr x).symm

/-- The reconstruction of a coherent germ is a `Q`-distribution
([Hos25, proof of Theorem 4.1]). -/
theorem reconstruct_mem : K.reconstruct F ∈ K.distributions := by
  refine ⟨fun t ht => funext fun x => by simp [reconstruct, not_lt.2 ht], fun s t hs ht x => ?_⟩
  obtain ⟨B, hB⟩ := K.bounded_reconstruct hF hγ hA hC hcoh ht
  refine ⟨K.integrable_kernel_mul_of_bound hs x (K.measurable_reconstruct hF hγ hA hC hcoh ht) hB,
    ?_⟩
  rw [K.apply_reconstruct hF hγ hA hC hcoh ht hs x, add_comm]

/-- `|RF_t(x) - F_x(t, x)| ≤ c C t^{γ/ℓ}` for `0 < t ≤ 1`
([Hos25, Theorem 4.1], the reconstruction bound). -/
theorem abs_reconstruct_sub_diag_le {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |K.reconstruct F t x - F x t x| ≤ K.reconstructionConst γ A * C * t ^ (γ / K.order) := by
  have h := K.abs_approx_sub_reconstruct_le hF hγ hA hC hcoh ht.1 ht.1 le_rfl ht.2 x
  rw [K.approx_self] at h
  rw [abs_sub_comm]
  exact h

end RegularityStructures.RegularisingSemigroup

end

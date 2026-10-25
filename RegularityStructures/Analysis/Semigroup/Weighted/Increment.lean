/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Weighted.Operator
public import RegularityStructures.Analysis.Semigroup.Weighted.OperatorBound
public import RegularityStructures.Analysis.Semigroup.Reconstruction.Increment

/-!
# Increments of the approximations `R^t_s F` for weighted germs

Steps (a)-(c) of the proof of [Hos25, Theorem 4.1] (arXiv:2310.07396v2) with a weight `ρ`:
for a weighted coherent germ `F`, `s / 2 ≤ u ≤ s ≤ min t 1`, `t ≤ τ`,
`|R^t_s F(x) - R^t_u F(x)| ≤ max 1 (weightConst p τ) · C κ_w ρ(x) s^{γ/ℓ}`.

The key estimate is `ρ(z) d(z, y)^r ≤ ρ(y) 2^p (d^r + d^{r+p})` together with `s ≤ 1`, which turns
the moments `M_{γ-a}` and `M_{γ-a+p}` into `s^{γ/ℓ}`.

* `diag_sub_apply_eq_weight`, `abs_diag_sub_apply_le_weight`: the weighted defect `g_s - Q_{s-u} g_u`;
* `abs_diag_sub_apply_le_of_half_weight`: step (a);
* `abs_approx_sub_approx_le_weight`: the increment of `approx`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  {ρ : E → ℝ} {p : ℝ}

theorem diag_sub_apply_eq_weight (hρ : K.IsModerateWeight ρ p) {F : E → ℝ → E → ℝ}
    (hF : K.IsWeightedGerm F ρ) {u s : ℝ} (hu : 0 < u) (hus : u < s) (hs1 : s ≤ 1) (y : E) :
    diag F s y - K.apply (s - u) (diag F u) y =
      ∫ z, K.kernel (s - u) y z * (F y u z - F z u z) ∂μ := by
  obtain ⟨B, hB⟩ := hF.bounded_diag ⟨hu, hus.le.trans hs1⟩
  have h1 : diag F s y = ∫ z, K.kernel (s - u) y z * F y u z ∂μ := by
    have := K.apply_eq (hF.mem y) (sub_pos.2 hus) hu y
    rw [sub_add_cancel] at this
    exact this.symm
  have i1 := K.integrable_kernel_mul (hF.mem y) (sub_pos.2 hus) hu y
  have i2 := K.integrable_kernel_mul_of_weight_bound hρ (sub_pos.2 hus) y
    (hF.measurable_diag hu) hB
  rw [h1]
  simp only [apply, diag, mul_sub]
  exact (integral_sub i1 i2).symm

theorem abs_diag_sub_apply_le_weight (hρ : K.IsModerateWeight ρ p) {F : E → ℝ → E → ℝ}
    (hF : K.IsWeightedGerm F ρ) {γ : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ}
    (hC : 0 ≤ C) (hcoh : K.IsWeightedCoherent F ρ γ A C) {u s : ℝ} (hu : 0 < u) (hus : u < s)
    (hs1 : s ≤ 1) (y : E) :
    |diag F s y - K.apply (s - u) (diag F u) y| ≤
      C * ∑ a ∈ A, u ^ (a / K.order) * (ρ y * ((2 : ℝ) ^ p *
        (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
          K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order)))) := by
  rw [K.diag_sub_apply_eq_weight hρ hF hu hus hs1 y]
  have hp := hρ.nonneg_exp
  have hsu : 0 < s - u := sub_pos.2 hus
  have hint : ∀ a ∈ A, Integrable (fun z => (u ^ (a / K.order) * (ρ y * (2 : ℝ) ^ p)) *
      (|K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a) +
        |K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a + p))) μ := fun a ha =>
    ((K.integrable_moment hsu (sub_nonneg.2 (hA a ha).le) y).add
      (K.integrable_moment hsu (by linarith [sub_nonneg.2 (hA a ha).le]) y)).const_mul _
  have hg : Integrable (fun z => C * ∑ a ∈ A, (u ^ (a / K.order) * (ρ y * (2 : ℝ) ^ p)) *
      (|K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a) +
        |K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a + p))) μ :=
    (integrable_finsetSum _ hint).const_mul C
  have hle := norm_integral_le_of_norm_le hg
    (f := fun z => K.kernel (s - u) y z * (F y u z - F z u z)) (Eventually.of_forall fun z => by
      have hc := hcoh ⟨hu, hus.le.trans hs1⟩ y z
      have hρz := hρ.le_mul y z
      have hd := K.scaleDist_nonneg z y
      have hS : 0 ≤ ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist z y ^ (γ - a) :=
        Finset.sum_nonneg fun a _ => mul_nonneg (Real.rpow_nonneg hu.le _)
          (Real.rpow_nonneg hd _)
      rw [Real.norm_eq_abs, abs_mul]
      calc |K.kernel (s - u) y z| * |F y u z - F z u z|
          ≤ |K.kernel (s - u) y z| * (C * ρ z * ∑ a ∈ A, u ^ (a / K.order) *
              K.scaleDist z y ^ (γ - a)) := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ ≤ |K.kernel (s - u) y z| * (C * (ρ y * ((2 : ℝ) ^ p * (1 + K.scaleDist z y ^ p))) *
              ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist z y ^ (γ - a)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hS) (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hρz hC
        _ = _ := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hne : γ - a + p ≠ 0 := by linarith [sub_pos.2 (hA a ha)]
          rw [Real.rpow_add' hd hne]
          ring)
  refine hle.trans ?_
  rw [integral_const_mul, integral_finsetSum _ hint]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) hC
  have hγa : 0 ≤ γ - a := sub_nonneg.2 (hA a ha).le
  rw [integral_const_mul, integral_add (K.integrable_moment hsu hγa y)
    (K.integrable_moment hsu (by linarith) y)]
  have m1 := K.moment_le hsu hγa y
  have m2 := K.moment_le hsu (show 0 ≤ γ - a + p by linarith) y
  have hn : 0 ≤ u ^ (a / K.order) * (ρ y * (2 : ℝ) ^ p) :=
    mul_nonneg (Real.rpow_nonneg hu.le _) (mul_nonneg (hρ.pos y).le
      (Real.rpow_nonneg (by norm_num) _))
  calc (u ^ (a / K.order) * (ρ y * (2 : ℝ) ^ p)) *
        ((∫ z, |K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a) ∂μ) +
          ∫ z, |K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a + p) ∂μ)
      ≤ (u ^ (a / K.order) * (ρ y * (2 : ℝ) ^ p)) *
        (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
          K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order)) :=
        mul_le_mul_of_nonneg_left (add_le_add m1 m2) hn
    _ = _ := by ring

theorem term_le_weight {γ a p u s : ℝ} (hℓ : 0 < K.order) (hu : 0 < u) (hus : u < s)
    (hsu : s / 2 ≤ u) (hs1 : s ≤ 1) (hγa : 0 ≤ γ - a) (hp : 0 ≤ p) :
    u ^ (a / K.order) * (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
        K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order)) ≤
      (K.momentConst (γ - a) + K.momentConst (γ - a + p)) * 2 ^ (max 0 (-a) / K.order) *
        s ^ (γ / K.order) := by
  have hs : 0 < s := hu.trans hus
  have hM1 := K.momentConst_nonneg (γ - a)
  have hM2 := K.momentConst_nonneg (γ - a + p)
  have h1 := K.rpow_le_two_pow_mul hℓ (a := a) hu hus.le hsu
  have h2 : (s - u) ^ ((γ - a) / K.order) ≤ s ^ ((γ - a) / K.order) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (div_nonneg hγa hℓ.le)
  have h2' : (s - u) ^ ((γ - a + p) / K.order) ≤ s ^ ((γ - a) / K.order) :=
    (Real.rpow_le_rpow (by linarith) (by linarith)
      (div_nonneg (by linarith) hℓ.le)).trans
      (Real.rpow_le_rpow_of_exponent_ge hs hs1
        (div_le_div_of_nonneg_right (by linarith) hℓ.le))
  have h3 : s ^ (a / K.order) * s ^ ((γ - a) / K.order) = s ^ (γ / K.order) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h4 : 0 ≤ (s - u) ^ ((γ - a) / K.order) := Real.rpow_nonneg (by linarith) _
  have h4' : 0 ≤ (s - u) ^ ((γ - a + p) / K.order) := Real.rpow_nonneg (by linarith) _
  have h6 : 0 ≤ (2 : ℝ) ^ (max 0 (-a) / K.order) := Real.rpow_nonneg (by norm_num) _
  have hX : K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
      K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order) ≤
      (K.momentConst (γ - a) + K.momentConst (γ - a + p)) * s ^ ((γ - a) / K.order) := by
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h2 hM1) (mul_le_mul_of_nonneg_left h2' hM2)
  have hX0 : 0 ≤ K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
      K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order) :=
    add_nonneg (mul_nonneg hM1 h4) (mul_nonneg hM2 h4')
  have hsa : 0 ≤ s ^ (a / K.order) := Real.rpow_nonneg hs.le _
  calc u ^ (a / K.order) * (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
        K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order))
      ≤ (2 ^ (max 0 (-a) / K.order) * s ^ (a / K.order)) *
        ((K.momentConst (γ - a) + K.momentConst (γ - a + p)) * s ^ ((γ - a) / K.order)) :=
        mul_le_mul h1 hX hX0 (mul_nonneg h6 hsa)
    _ = ((K.momentConst (γ - a) + K.momentConst (γ - a + p)) * 2 ^ (max 0 (-a) / K.order)) *
        (s ^ (a / K.order) * s ^ ((γ - a) / K.order)) := by ring
    _ = _ := by rw [h3]

/-- Step (a): `|g_s - Q_{s-u} g_u| ≤ C κ_w ρ(y) s^{γ/ℓ}` for `s / 2 ≤ u < s ≤ 1`. -/
theorem abs_diag_sub_apply_le_of_half_weight (hρ : K.IsModerateWeight ρ p)
    {F : E → ℝ → E → ℝ} (hF : K.IsWeightedGerm F ρ) {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsWeightedCoherent F ρ γ A C)
    {u s : ℝ} (hu : 0 < u) (hus : u < s) (hsu : s / 2 ≤ u) (hs1 : s ≤ 1) (y : E) :
    |diag F s y - K.apply (s - u) (diag F u) y| ≤
      C * K.weightedCoherenceConst p γ A * ρ y * s ^ (γ / K.order) := by
  refine (K.abs_diag_sub_apply_le_weight hρ hF hA hC hcoh hu hus hs1 y).trans ?_
  have hρy := (hρ.pos y).le
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  calc C * ∑ a ∈ A, u ^ (a / K.order) * (ρ y * ((2 : ℝ) ^ p *
        (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
          K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order))))
      ≤ C * ∑ a ∈ A, ρ y * (((2 : ℝ) ^ p * (K.momentConst (γ - a) + K.momentConst (γ - a + p)) *
          2 ^ (max 0 (-a) / K.order)) * s ^ (γ / K.order)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) hC
        have := K.term_le_weight (p := p) K.order_pos hu hus hsu hs1
          (sub_nonneg.2 (hA a ha).le) hρ.nonneg_exp
        calc u ^ (a / K.order) * (ρ y * ((2 : ℝ) ^ p *
              (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
                K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order))))
            = (ρ y * (2 : ℝ) ^ p) * (u ^ (a / K.order) *
              (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order) +
                K.momentConst (γ - a + p) * (s - u) ^ ((γ - a + p) / K.order))) := by ring
          _ ≤ (ρ y * (2 : ℝ) ^ p) * ((K.momentConst (γ - a) + K.momentConst (γ - a + p)) *
              2 ^ (max 0 (-a) / K.order) * s ^ (γ / K.order)) :=
              mul_le_mul_of_nonneg_left this (mul_nonneg hρy h2p)
          _ = _ := by ring
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, weightedCoherenceConst]
        ring

theorem bounded_approx_weight (hρ : K.IsModerateWeight ρ p) {F : E → ℝ → E → ℝ}
    (hF : K.IsWeightedGerm F ρ) {t s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    ∃ B, ∀ x, |K.approx F t s x| ≤ B * ρ x := by
  obtain ⟨B, hB⟩ := hF.bounded_diag hs
  rcases lt_or_ge s t with h | h
  · exact ⟨B * K.weightConst p (t - s), fun x => by
      rw [K.approx_of_lt F h]
      have := K.abs_apply_le_of_weight_bound hρ (sub_pos.2 h) hB x
      linarith⟩
  · exact ⟨B, fun x => by simpa [approx, not_lt.2 h] using hB x⟩

/-- Steps (b)-(c): the increments of `R^t_s F` ([Hos25, proof of Theorem 4.1]):
`|R^t_s F(x) - R^t_u F(x)| ≤ max 1 W_τ · C κ_w ρ(x) s^{γ/ℓ}` for `s / 2 ≤ u ≤ s ≤ min t 1`
and `t ≤ τ`. -/
theorem abs_approx_sub_approx_le_weight [SFinite μ] (hρ : K.IsModerateWeight ρ p)
    {F : E → ℝ → E → ℝ} (hF : K.IsWeightedGerm F ρ) {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsWeightedCoherent F ρ γ A C)
    {t s u τ : ℝ} (hu : 0 < u) (hus : u ≤ s) (hsu : s / 2 ≤ u) (hst : s ≤ t) (htτ : t ≤ τ)
    (hs1 : s ≤ 1) (x : E) :
    |K.approx F t s x - K.approx F t u x| ≤
      max 1 (K.weightConst p τ) * (C * K.weightedCoherenceConst p γ A * ρ x * s ^ (γ / K.order)) := by
  have hs : 0 < s := hu.trans_le hus
  have hX : 0 ≤ C * K.weightedCoherenceConst p γ A * ρ x * s ^ (γ / K.order) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (K.weightedCoherenceConst_nonneg p γ A))
      (hρ.pos x).le) (Real.rpow_nonneg hs.le _)
  have hm1 : 1 ≤ max 1 (K.weightConst p τ) := le_max_left _ _
  rcases hus.eq_or_lt with rfl | hlt
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hX
  have hD : ∀ y, |diag F s y - K.apply (s - u) (diag F u) y| ≤
      (C * K.weightedCoherenceConst p γ A * s ^ (γ / K.order)) * ρ y := fun y => by
    have := K.abs_diag_sub_apply_le_of_half_weight hρ hF hA hC hcoh hu hlt hsu hs1 y
    linarith
  have hut : u < t := lt_of_lt_of_le hlt hst
  have happ_u : K.approx F t u x = K.apply (t - u) (diag F u) x := by
    rw [K.approx_of_lt F hut]
  rcases hst.eq_or_lt with rfl | hst'
  · rw [K.approx_self, happ_u]
    refine (hD x).trans ?_
    calc _ = C * K.weightedCoherenceConst p γ A * ρ x * s ^ (γ / K.order) := by ring
      _ ≤ _ := le_mul_of_one_le_left hX hm1
  · obtain ⟨Bu, hBu⟩ := hF.bounded_diag ⟨hu, hlt.le.trans hs1⟩
    obtain ⟨Bs, hBs⟩ := hF.bounded_diag ⟨hs, hs1⟩
    have hts : 0 < t - s := sub_pos.2 hst'
    have i1 := K.integrable_kernel_mul_of_weight_bound hρ hts x (hF.measurable_diag hs) hBs
    have i2 := K.integrable_kernel_mul_of_weight_bound hρ hts x
      (K.measurable_apply _ (hF.measurable_diag hu))
      (B := Bu * K.weightConst p (s - u))
      (fun y => by
        have := K.abs_apply_le_of_weight_bound hρ (sub_pos.2 hlt) hBu y
        linarith)
    have e : K.approx F t s x - K.approx F t u x =
        K.apply (t - s) (fun y => diag F s y - K.apply (s - u) (diag F u) y) x := by
      rw [K.apply_sub x i1 i2, K.apply_apply_of_weight_bound hρ hts (sub_pos.2 hlt)
        (hF.measurable_diag hu) hBu,
        (by ring : t - s + (s - u) = t - u), happ_u, K.approx_of_lt F hst']
    rw [e]
    refine (K.abs_apply_le_of_weight_bound hρ hts hD x).trans ?_
    have hw : K.weightConst p (t - s) ≤ max 1 (K.weightConst p τ) :=
      (K.weightConst_mono hρ.nonneg_exp hts.le (by linarith)).trans (le_max_right _ _)
    have hn : 0 ≤ C * K.weightedCoherenceConst p γ A * s ^ (γ / K.order) * ρ x :=
      mul_nonneg (mul_nonneg (mul_nonneg hC (K.weightedCoherenceConst_nonneg p γ A))
        (Real.rpow_nonneg hs.le _)) (hρ.pos x).le
    calc C * K.weightedCoherenceConst p γ A * s ^ (γ / K.order) * ρ x * K.weightConst p (t - s)
        ≤ C * K.weightedCoherenceConst p γ A * s ^ (γ / K.order) * ρ x *
          max 1 (K.weightConst p τ) := mul_le_mul_of_nonneg_left hw hn
      _ = _ := by ring

end RegularityStructures.RegularisingSemigroup

end

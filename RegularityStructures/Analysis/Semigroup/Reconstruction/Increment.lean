/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Germ
public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Analysis.Semigroup.OperatorBound

/-!
# Increments of the approximations `R^t_s F`

Steps (a)-(c) of the proof of [Hos25, Theorem 4.1] (arXiv:2310.07396v2), specialised to
`p = ∞`, `w = v = 1`: for a coherent germ `F`,
`|R^t_s F(x) - R^t_u F(x)| ≤ L s^{γ/ℓ}` for `s / 2 ≤ u ≤ s ≤ min t 1`.

* `coherenceConst γ A = ∑_{a ∈ A} M_{γ-a} 2^{max(0,-a)/ℓ}`;
* `reconstructionConst γ A`, the constant of the reconstruction bound;
* `diag_sub_apply_eq`, `abs_diag_sub_apply_le`: the defect `g_s - Q_{s-u} g_u`;
* `abs_approx_sub_approx_le`: the increment of `approx`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- `κ = ∑_{a ∈ A} M_{γ-a} 2^{max(0,-a)/ℓ}`. -/
def coherenceConst (γ : ℝ) (A : Finset ℝ) : ℝ :=
  ∑ a ∈ A, K.momentConst (γ - a) * 2 ^ (max 0 (-a) / K.order)

/-- The constant of the reconstruction bound
`|RF_t(x) - F_x(t, x)| ≤ reconstructionConst γ A * C * t^{γ/ℓ}`. -/
def reconstructionConst (γ : ℝ) (A : Finset ℝ) : ℝ :=
  2 * (max 1 (K.momentConst 0) * ∑ a ∈ A, K.momentConst (γ - a) * 2 ^ (max 0 (-a) / K.order)) /
    (1 - 2 ^ (-(γ / K.order)))

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem coherenceConst_nonneg (γ : ℝ) (A : Finset ℝ) : 0 ≤ K.coherenceConst γ A :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (K.momentConst_nonneg _) (Real.rpow_nonneg (by norm_num) _)

theorem reconstructionConst_eq (γ : ℝ) (A : Finset ℝ) :
    K.reconstructionConst γ A =
      2 * (max 1 (K.momentConst 0) * K.coherenceConst γ A) / (1 - 2 ^ (-(γ / K.order))) := rfl

theorem reconstructionConst_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (A : Finset ℝ) :
    0 ≤ K.reconstructionConst γ A := by
  rw [reconstructionConst_eq]
  have h1 : (2 : ℝ) ^ (-(γ / K.order)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have := div_nonneg hγ K.order_pos.le; linarith)
  have := K.coherenceConst_nonneg γ A
  have := K.momentConst_nonneg 0
  exact div_nonneg (by positivity) (by linarith)

theorem apply_sub {t : ℝ} {f g : E → ℝ} (x : E)
    (hf : Integrable (fun y => K.kernel t x y * f y) μ)
    (hg : Integrable (fun y => K.kernel t x y * g y) μ) :
    K.apply t (fun y => f y - g y) x = K.apply t f x - K.apply t g x := by
  simp only [apply, mul_sub]
  exact integral_sub hf hg

/-- The defect `g_s - Q_{s-u} g_u` of the diagonal of a germ, as an integral of the increment
`F_y - F_z` ([Hos25, proof of Theorem 4.1]). -/
theorem diag_sub_apply_eq {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {u s : ℝ} (hu : 0 < u)
    (hus : u < s) (hs1 : s ≤ 1) (y : E) :
    diag F s y - K.apply (s - u) (diag F u) y =
      ∫ z, K.kernel (s - u) y z * (F y u z - F z u z) ∂μ := by
  obtain ⟨B, hB⟩ := hF.bounded_diag ⟨hu, hus.le.trans hs1⟩
  have h1 : diag F s y = ∫ z, K.kernel (s - u) y z * F y u z ∂μ := by
    have := K.apply_eq (hF.mem y) (sub_pos.2 hus) hu y
    rw [sub_add_cancel] at this
    exact this.symm
  have i1 := K.integrable_kernel_mul (hF.mem y) (sub_pos.2 hus) hu y
  have i2 := K.integrable_kernel_mul_of_bound (sub_pos.2 hus) y (hF.measurable_diag hu) hB
  rw [h1]
  simp only [apply, diag, mul_sub]
  exact (integral_sub i1 i2).symm

theorem abs_diag_sub_apply_le {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C) {u s : ℝ}
    (hu : 0 < u) (hus : u < s) (hs1 : s ≤ 1) (y : E) :
    |diag F s y - K.apply (s - u) (diag F u) y| ≤
      C * ∑ a ∈ A, u ^ (a / K.order) * (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order)) := by
  rw [K.diag_sub_apply_eq hF hu hus hs1 y]
  have hsu : 0 < s - u := sub_pos.2 hus
  have hint : ∀ a ∈ A, Integrable (fun z => |K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a)) μ :=
    fun a ha => K.integrable_moment hsu (sub_nonneg.2 (hA a ha).le) y
  have hg : Integrable (fun z => C * ∑ a ∈ A, u ^ (a / K.order) *
      (|K.kernel (s - u) y z| * K.scaleDist z y ^ (γ - a))) μ :=
    (integrable_finsetSum _ fun a ha => (hint a ha).const_mul _).const_mul C
  have hle := norm_integral_le_of_norm_le hg
    (f := fun z => K.kernel (s - u) y z * (F y u z - F z u z)) (Eventually.of_forall fun z => by
      have hc := hcoh ⟨hu, hus.le.trans hs1⟩ y z
      rw [Real.norm_eq_abs, abs_mul]
      calc |K.kernel (s - u) y z| * |F y u z - F z u z|
          ≤ |K.kernel (s - u) y z| * (C * ∑ a ∈ A, u ^ (a / K.order) *
              K.scaleDist z y ^ (γ - a)) := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = _ := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring)
  refine hle.trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun a ha =>
    ((hint a ha).const_mul _)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) hC
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (K.moment_le hsu (sub_nonneg.2 (hA a ha).le) y)
    (Real.rpow_nonneg hu.le _)

theorem rpow_le_two_pow_mul {u s : ℝ} (hℓ : 0 < K.order) {a : ℝ} (hu : 0 < u) (hus : u ≤ s)
    (hsu : s / 2 ≤ u) :
    u ^ (a / K.order) ≤ 2 ^ (max 0 (-a) / K.order) * s ^ (a / K.order) := by
  have hs : 0 < s := hu.trans_le hus
  rcases le_or_gt 0 a with ha | ha
  · rw [max_eq_left (by linarith), zero_div, Real.rpow_zero, one_mul]
    exact Real.rpow_le_rpow hu.le hus (div_nonneg ha hℓ.le)
  · rw [max_eq_right (by linarith)]
    have h1 : u ^ (a / K.order) ≤ (s / 2) ^ (a / K.order) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hsu (div_nonpos_of_nonpos_of_nonneg ha.le hℓ.le)
    refine h1.trans (le_of_eq ?_)
    rw [Real.div_rpow hs.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
      neg_div, mul_comm]

theorem term_le {γ a u s : ℝ} (hℓ : 0 < K.order) (hu : 0 < u) (hus : u < s) (hsu : s / 2 ≤ u)
    (hγa : 0 ≤ γ - a) :
    u ^ (a / K.order) * (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order)) ≤
      (K.momentConst (γ - a) * 2 ^ (max 0 (-a) / K.order)) * s ^ (γ / K.order) := by
  have hs : 0 < s := hu.trans hus
  have hM := K.momentConst_nonneg (γ - a)
  have h1 := K.rpow_le_two_pow_mul hℓ (a := a) hu hus.le hsu
  have h2 : (s - u) ^ ((γ - a) / K.order) ≤ s ^ ((γ - a) / K.order) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (div_nonneg hγa hℓ.le)
  have h3 : s ^ (a / K.order) * s ^ ((γ - a) / K.order) = s ^ (γ / K.order) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h4 : 0 ≤ (s - u) ^ ((γ - a) / K.order) := Real.rpow_nonneg (by linarith) _
  have h5 : 0 ≤ s ^ ((γ - a) / K.order) := Real.rpow_nonneg hs.le _
  have h6 : 0 ≤ (2 : ℝ) ^ (max 0 (-a) / K.order) := Real.rpow_nonneg (by norm_num) _
  calc u ^ (a / K.order) * (K.momentConst (γ - a) * (s - u) ^ ((γ - a) / K.order))
      ≤ (2 ^ (max 0 (-a) / K.order) * s ^ (a / K.order)) *
        (K.momentConst (γ - a) * s ^ ((γ - a) / K.order)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hM) (mul_nonneg hM h4)
          (mul_nonneg h6 (Real.rpow_nonneg hs.le _))
    _ = (K.momentConst (γ - a) * 2 ^ (max 0 (-a) / K.order)) *
        (s ^ (a / K.order) * s ^ ((γ - a) / K.order)) := by ring
    _ = _ := by rw [h3]

/-- Step (a): `|g_s - Q_{s-u} g_u| ≤ C κ s^{γ/ℓ}` for `s / 2 ≤ u < s ≤ 1`. -/
theorem abs_diag_sub_apply_le_of_half {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {γ : ℝ}
    {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C)
    {u s : ℝ} (hu : 0 < u) (hus : u < s) (hsu : s / 2 ≤ u) (hs1 : s ≤ 1) (y : E) :
    |diag F s y - K.apply (s - u) (diag F u) y| ≤
      C * K.coherenceConst γ A * s ^ (γ / K.order) := by
  refine (K.abs_diag_sub_apply_le hF hA hC hcoh hu hus hs1 y).trans ?_
  rw [coherenceConst, mul_assoc, Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha =>
    K.term_le K.order_pos hu hus hsu (sub_nonneg.2 (hA a ha).le)) hC

theorem approx_of_lt (F : E → ℝ → E → ℝ) {t s : ℝ} (h : s < t) :
    K.approx F t s = K.apply (t - s) (diag F s) := by
  funext x; simp [approx, h]

theorem approx_self (F : E → ℝ → E → ℝ) (t : ℝ) : K.approx F t t = diag F t := by
  funext x; simp [approx]

theorem measurable_approx [SFinite μ] {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {t s : ℝ}
    (hs : 0 < s) : Measurable (K.approx F t s) := by
  rcases lt_or_ge s t with h | h
  · rw [K.approx_of_lt F h]
    exact K.measurable_apply _ (hF.measurable_diag hs)
  · have : K.approx F t s = diag F s := by funext x; simp [approx, not_lt.2 h]
    rw [this]
    exact hF.measurable_diag hs

theorem bounded_approx {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {t s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    ∃ B, ∀ x, |K.approx F t s x| ≤ B := by
  obtain ⟨B, hB⟩ := hF.bounded_diag hs
  rcases lt_or_ge s t with h | h
  · exact ⟨K.momentConst 0 * B, fun x => by
      rw [K.approx_of_lt F h]; exact K.abs_apply_le_of_bound (sub_pos.2 h) hB x⟩
  · exact ⟨B, fun x => by simpa [approx, not_lt.2 h] using hB x⟩

/-- Steps (b)-(c): the increments of `R^t_s F` ([Hos25, proof of Theorem 4.1]):
`|R^t_s F(x) - R^t_u F(x)| ≤ max 1 M₀ · C κ · s^{γ/ℓ}` for `s / 2 ≤ u ≤ s ≤ min t 1`. -/
theorem abs_approx_sub_approx_le [SFinite μ] {F : E → ℝ → E → ℝ} (hF : K.IsGerm F) {γ : ℝ}
    {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C)
    {t s u : ℝ} (hu : 0 < u) (hus : u ≤ s) (hsu : s / 2 ≤ u) (hst : s ≤ t) (hs1 : s ≤ 1)
    (x : E) :
    |K.approx F t s x - K.approx F t u x| ≤
      max 1 (K.momentConst 0) * (C * K.coherenceConst γ A * s ^ (γ / K.order)) := by
  have hs : 0 < s := hu.trans_le hus
  have hX : 0 ≤ C * K.coherenceConst γ A * s ^ (γ / K.order) :=
    mul_nonneg (mul_nonneg hC (K.coherenceConst_nonneg γ A)) (Real.rpow_nonneg hs.le _)
  have hm1 : 1 ≤ max 1 (K.momentConst 0) := le_max_left _ _
  have hm0 : K.momentConst 0 ≤ max 1 (K.momentConst 0) := le_max_right _ _
  rcases hus.eq_or_lt with rfl | hlt
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hX
  have hD : ∀ y, |diag F s y - K.apply (s - u) (diag F u) y| ≤
      C * K.coherenceConst γ A * s ^ (γ / K.order) := fun y =>
    K.abs_diag_sub_apply_le_of_half hF hA hC hcoh hu hlt hsu hs1 y
  have hut : u < t := lt_of_lt_of_le hlt hst
  have happ_u : K.approx F t u x = K.apply (t - u) (diag F u) x := by
    rw [K.approx_of_lt F hut]
  rcases hst.eq_or_lt with rfl | hst'
  · rw [K.approx_self, happ_u]
    exact (hD x).trans (le_mul_of_one_le_left hX hm1)
  · obtain ⟨Bu, hBu⟩ := hF.bounded_diag ⟨hu, hlt.le.trans hs1⟩
    obtain ⟨Bs, hBs⟩ := hF.bounded_diag ⟨hs, hs1⟩
    have hts : 0 < t - s := sub_pos.2 hst'
    have i1 := K.integrable_kernel_mul_of_bound hts x (hF.measurable_diag hs) hBs
    have i2 := K.integrable_kernel_mul_of_bound hts x
      (K.measurable_apply _ (hF.measurable_diag hu))
      (fun y => K.abs_apply_le_of_bound (sub_pos.2 hlt) hBu y)
    have e : K.approx F t s x - K.approx F t u x =
        K.apply (t - s) (fun y => diag F s y - K.apply (s - u) (diag F u) y) x := by
      rw [K.apply_sub x i1 i2, K.apply_apply hts (sub_pos.2 hlt) (hF.measurable_diag hu) hBu,
        (by ring : t - s + (s - u) = t - u), happ_u, K.approx_of_lt F hst']
    rw [e]
    refine (K.abs_apply_le_of_bound hts hD x).trans ?_
    exact mul_le_mul_of_nonneg_right hm0 hX

end RegularityStructures.RegularisingSemigroup

end

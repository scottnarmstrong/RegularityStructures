/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffPairing
import Mathlib.Tactic

/-!
# Pairings of the Taylor kernel with arrays of kernels

* `ipsiTaylorKernel_pairing_gen2`: kernels bounded by `K (s^(-b₁) + s^(-b₂))`;
* `ipsi_pairing_isArrR`: if `(i, j) ↦ Φ_{ij}(z)` is an array in ratio form (base `C s(z)^(-1)`,
  ratio `min 1 (m^θ (1 + s(z)^(-θ)))`) for every `z`, then so is the array of pairings
  `(i, j) ↦ ∫ T(w) Φ_{ij}(w - g) dw`, with base `C' r^γ (1 + r) (1 + e^(-p))` and ratio
  `min 1 (m^θ (1 + e^(-θ)))`, `e = s(proj x - g)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem one_add_rpow_neg_add_le {e a b : ℝ} (he : 0 < e) :
    1 + e ^ (-(a + b)) ≤ (1 + e ^ (-a)) * (1 + e ^ (-b)) := by
  have h1 : e ^ (-(a + b)) = e ^ (-a) * e ^ (-b) := by
    rw [← Real.rpow_add he]; congr 1; ring
  have h2 : 0 ≤ e ^ (-a) := Real.rpow_nonneg he.le _
  have h3 : 0 ≤ e ^ (-b) := Real.rpow_nonneg he.le _
  rw [h1]; linarith

theorem integral_sd4 {f1 f2 f3 f4 : SpaceTime → ℝ} (i1 : Integrable f1) (i2 : Integrable f2)
    (i3 : Integrable f3) (i4 : Integrable f4) :
    ∫ w, (f1 w - f2 w - f3 w + f4 w) = (∫ w, f1 w) - (∫ w, f2 w) - (∫ w, f3 w) + ∫ w, f4 w := by
  have j1 : Integrable (fun w => f1 w - f2 w) := i1.sub i2
  have j2 : Integrable (fun w => f1 w - f2 w - f3 w) := j1.sub i3
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2]

theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

theorem one_add_rpow_neg_le {e a a' : ℝ} (he : 0 < e) (ha : 0 ≤ a) (h : a ≤ a') :
    1 + e ^ (-a) ≤ 2 * (1 + e ^ (-a')) := by
  have h3 : 0 ≤ e ^ (-a') := Real.rpow_nonneg he.le _
  rcases le_total e 1 with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_ge he h1 (show -a' ≤ -a by linarith)
    linarith
  · have : e ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    linarith

/-- **Pairing with a kernel bounded by `K (s^(-b₁) + s^(-b₂))`.** -/
theorem ipsiTaylorKernel_pairing_gen2 (N : ℕ) {θ γ b₁ b₂ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hb1 : 1 ≤ b₁) (hb12 : b₁ ≤ b₂) (hbγ : γ + b₂ < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Φ : SpaceTime → ℝ} {K : ℝ}, Measurable Φ → 0 ≤ K →
      (∀ z, 0 < torusParabolicSize z →
        |Φ z| ≤ K * (torusParabolicSize z ^ (-b₁) + torusParabolicSize z ^ (-b₂))) →
      ∀ (x y : ParabolicSpace) {g : SpaceTime}, 0 < torusParabolicSize (spaceTimeProj x - g) →
        Integrable (fun w => ipsiTaylorKernel N x y w * Φ (w - g)) ∧
        |∫ w, ipsiTaylorKernel N x y w * Φ (w - g)| ≤
          C * K * (parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
            (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-(θ + b₂ - 1))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := ipsiTaylorKernel_pairing_gen N hθ hθ1 hγ hγ1 (hb1.trans hb12) hbγ
  obtain ⟨C₂, hC₂, h₂⟩ := ipsiTaylorKernel_pairing_gen N hθ hθ1 hγ hγ1 hb1 (by linarith)
  refine ⟨4 * (C₁ + C₂), by positivity, ?_⟩
  intro Φ K hΦm hK0 hΦb x y g hxg
  set Φ₁ : SpaceTime → ℝ := fun z => if torusParabolicSize z ≤ 1 then Φ z else 0 with hΦ₁
  set Φ₂ : SpaceTime → ℝ := fun z => if torusParabolicSize z ≤ 1 then 0 else Φ z with hΦ₂
  have hmeasS : MeasurableSet {z : SpaceTime | torusParabolicSize z ≤ 1} :=
    measurableSet_le Phi43.measurable_torusParabolicSize measurable_const
  have m1 : Measurable Φ₁ := Measurable.ite hmeasS hΦm measurable_const
  have m2 : Measurable Φ₂ := Measurable.ite hmeasS measurable_const hΦm
  have b1 : ∀ z, 0 < torusParabolicSize z →
      |Φ₁ z| ≤ (2 * K) * torusParabolicSize z ^ (-b₂) := by
    intro z hz
    by_cases hs : torusParabolicSize z ≤ 1
    · simp only [hΦ₁, hs, ite_true]
      have := hΦb z hz
      have h3 : torusParabolicSize z ^ (-b₁) ≤ torusParabolicSize z ^ (-b₂) :=
        Real.rpow_le_rpow_of_exponent_ge hz hs (by linarith)
      nlinarith
    · simp only [hΦ₁, hs, ite_false, abs_zero]
      positivity
  have b2 : ∀ z, 0 < torusParabolicSize z →
      |Φ₂ z| ≤ (2 * K) * torusParabolicSize z ^ (-b₁) := by
    intro z hz
    by_cases hs : torusParabolicSize z ≤ 1
    · simp only [hΦ₂, hs, ite_true, abs_zero]
      positivity
    · simp only [hΦ₂, hs, ite_false]
      have := hΦb z hz
      have h3 : torusParabolicSize z ^ (-b₂) ≤ torusParabolicSize z ^ (-b₁) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt (not_le.1 hs)) (by linarith)
      nlinarith
  obtain ⟨i1, e1⟩ := h₁ m1 (by positivity) b1 x y hxg
  obtain ⟨i2, e2⟩ := h₂ m2 (by positivity) b2 x y hxg
  have hsplit : ∀ w, ipsiTaylorKernel N x y w * Φ (w - g) =
      ipsiTaylorKernel N x y w * Φ₁ (w - g) + ipsiTaylorKernel N x y w * Φ₂ (w - g) := by
    intro w; simp only [hΦ₁, hΦ₂]; split_ifs <;> ring
  have e0 : 0 < torusParabolicSize (spaceTimeProj x - g) := hxg
  have hE := one_add_rpow_neg_le e0 (show 0 ≤ θ + b₁ - 1 by linarith)
    (show θ + b₁ - 1 ≤ θ + b₂ - 1 by linarith)
  refine ⟨?_, ?_⟩
  · refine (i1.add i2).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]; rw [hsplit w]
  · have : (fun w => ipsiTaylorKernel N x y w * Φ (w - g)) = fun w =>
        ipsiTaylorKernel N x y w * Φ₁ (w - g) + ipsiTaylorKernel N x y w * Φ₂ (w - g) :=
      funext hsplit
    rw [this, integral_add i1 i2]
    refine (abs_add_le _ _).trans ?_
    set r := parabolicNorm (y - x)
    set E2 := 1 + torusParabolicSize (spaceTimeProj x - g) ^ (-(θ + b₂ - 1))
    set E1 := 1 + torusParabolicSize (spaceTimeProj x - g) ^ (-(θ + b₁ - 1))
    have hr0 : 0 ≤ r := parabolicNorm_nonneg _
    have hW : 0 ≤ r ^ γ * (1 + r) := mul_nonneg (Real.rpow_nonneg hr0 _) (by linarith)
    have hE2 : 0 ≤ E2 := by
      have := Real.rpow_nonneg (torusParabolicSize_nonneg (spaceTimeProj x - g)) (-(θ + b₂ - 1))
      simp only [E2]; linarith
    have hE1 : 0 ≤ E1 := by
      have := Real.rpow_nonneg (torusParabolicSize_nonneg (spaceTimeProj x - g)) (-(θ + b₁ - 1))
      simp only [E1]; linarith
    have hKW : 0 ≤ K * (r ^ γ * (1 + r)) := mul_nonneg hK0 hW
    have t1 : C₁ * (2 * K) * (r ^ γ * (1 + r)) * E2 ≤ 2 * C₁ * (K * (r ^ γ * (1 + r))) * E2 := by
      linarith [mul_nonneg hKW hE2]
    have t2 : C₂ * (2 * K) * (r ^ γ * (1 + r)) * E1 ≤
        4 * C₂ * (K * (r ^ γ * (1 + r))) * E2 := by
      have := mul_le_mul_of_nonneg_left hE (mul_nonneg hC₂ hKW)
      linarith [this]
    linarith [t1, t2, e1, e2, mul_nonneg hC₁ (mul_nonneg hKW hE2), mul_nonneg hC₂ (mul_nonneg hKW hE2)]

theorem ipsi_arrR_crude {S ς CΦ : ℝ} {h : Fin 2 → Fin 2 → ℝ} (hS : 0 ≤ S) (hC : 0 ≤ CΦ)
    (H : IsArrR h (CΦ * S) ς) :
    |h 1 1| ≤ CΦ * S ∧ |h 0 1| ≤ 2 * (CΦ * S) ∧ |h 1 0| ≤ 2 * (CΦ * S) ∧
    |h 0 0| ≤ 6 * (CΦ * S) ∧ |h 0 1 - h 1 1| ≤ CΦ * S ∧ |h 1 0 - h 1 1| ≤ CΦ * S ∧
    |arrSd h| ≤ CΦ * S := by
  obtain ⟨c0, c1, h11, h01, h10, hsd⟩ := H
  have hCS : 0 ≤ CΦ * S := mul_nonneg hC hS
  have b1 : CΦ * S * ς ≤ CΦ * S := by linarith [mul_nonneg hCS (sub_nonneg.2 c1)]
  have b2 : CΦ * S * ς ^ 2 ≤ CΦ * S := by
    have : ς ^ 2 ≤ 1 := by nlinarith
    linarith [mul_nonneg hCS (sub_nonneg.2 this)]
  have d1 : |h 0 1 - h 1 1| ≤ CΦ * S := h01.trans b1
  have d2 : |h 1 0 - h 1 1| ≤ CΦ * S := h10.trans b1
  have d3 : |arrSd h| ≤ CΦ * S := hsd.trans b2
  refine ⟨h11, ?_, ?_, ?_, d1, d2, d3⟩
  · have e : h 0 1 = (h 0 1 - h 1 1) + h 1 1 := by ring
    rw [e]; exact (abs_add_le _ _).trans (by linarith)
  · have e : h 1 0 = (h 1 0 - h 1 1) + h 1 1 := by ring
    rw [e]; exact (abs_add_le _ _).trans (by linarith)
  · have e : h 0 0 = arrSd h + (h 0 1 - h 1 1) + (h 1 0 - h 1 1) + h 1 1 := by
      unfold arrSd; ring
    rw [e]
    exact (abs_add_four_le _ _ _ _).trans (by linarith)

theorem ipsi_arrR_ratio {m θ z : ℝ} (hm0 : 0 ≤ m) (hz : 0 < z) {CΦ : ℝ} (hC : 0 ≤ CΦ)
    {h : Fin 2 → Fin 2 → ℝ}
    (H : IsArrR h (CΦ * z ^ (-(1 : ℝ))) (min 1 (ipsiRatio m θ z))) :
    |h 0 1 - h 1 1| ≤ CΦ * m ^ θ * (z ^ (-(1 : ℝ)) + z ^ (-(1 + θ))) ∧
    |h 1 0 - h 1 1| ≤ CΦ * m ^ θ * (z ^ (-(1 : ℝ)) + z ^ (-(1 + θ))) ∧
    |arrSd h| ≤ (2 * CΦ * m ^ (2 * θ)) * (z ^ (-(1 : ℝ)) + z ^ (-(1 + 2 * θ))) := by
  obtain ⟨c0, c1, h11, h01, h10, hsd⟩ := H
  have hS : 0 ≤ z ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have hmθ : 0 ≤ m ^ θ := Real.rpow_nonneg hm0 _
  set S := z ^ (-(1 : ℝ)) with hSdef
  set ς := min 1 (ipsiRatio m θ z) with hς
  have hσ : ipsiRatio m θ z = m ^ θ * (1 + z ^ (-θ)) := rfl
  have hςσ : ς ≤ ipsiRatio m θ z := min_le_right _ _
  have hCS : 0 ≤ CΦ * S := mul_nonneg hC hS
  have e1 : z ^ (-(1 + θ)) = S * z ^ (-θ) := by
    rw [hSdef, ← Real.rpow_add hz]; congr 1; ring
  have e2 : z ^ (-(1 + 2 * θ)) = S * (z ^ (-θ)) ^ 2 := by
    rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    congr 1; push_cast; ring
  have r1 : CΦ * S * ς ≤ CΦ * m ^ θ * (S + z ^ (-(1 + θ))) := by
    have : CΦ * S * ς ≤ CΦ * S * ipsiRatio m θ z := mul_le_mul_of_nonneg_left hςσ hCS
    rw [hσ] at this
    rw [e1]
    calc CΦ * S * ς ≤ CΦ * S * (m ^ θ * (1 + z ^ (-θ))) := this
      _ = _ := by ring
  have r2 : CΦ * S * ς ^ 2 ≤ (2 * CΦ * m ^ (2 * θ)) * (S + z ^ (-(1 + 2 * θ))) := by
    have hm2 : m ^ (2 * θ) = (m ^ θ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
    have c : ς ^ 2 ≤ ipsiRatio m θ z ^ 2 := pow_le_pow_left₀ c0 hςσ 2
    have h3 : CΦ * S * ς ^ 2 ≤ CΦ * S * ipsiRatio m θ z ^ 2 := mul_le_mul_of_nonneg_left c hCS
    rw [hσ] at h3
    rw [e2, hm2]
    have k : (1 + z ^ (-θ)) ^ 2 ≤ 2 * (1 + (z ^ (-θ)) ^ 2) := by
      linarith [sq_nonneg (1 - z ^ (-θ))]
    have k2 : (m ^ θ * (1 + z ^ (-θ))) ^ 2 ≤ (m ^ θ) ^ 2 * (2 * (1 + (z ^ (-θ)) ^ 2)) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left k (sq_nonneg _)
    calc CΦ * S * ς ^ 2 ≤ CΦ * S * (m ^ θ * (1 + z ^ (-θ))) ^ 2 := h3
      _ ≤ CΦ * S * ((m ^ θ) ^ 2 * (2 * (1 + (z ^ (-θ)) ^ 2))) :=
          mul_le_mul_of_nonneg_left k2 hCS
      _ = _ := by ring
  refine ⟨?_, ?_, hsd.trans r2⟩
  · exact h01.trans (by rw [mul_assoc] at r1 ⊢; exact r1)
  · exact h10.trans (by rw [mul_assoc] at r1 ⊢; exact r1)

/-- **Pairing of the Taylor kernel with an array of kernels in ratio form.** -/
theorem ipsi_pairing_isArrR (N : ℕ) {θ p γ : ℝ} (hθ : 0 < θ) (hp : 0 < p)
    (hp1 : p < 1) (hγ : 0 < γ) (hγ1 : γ < 1) (hγθ : γ + 2 * θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℝ}, 0 ≤ m → ∀ {Φ : Fin 2 → Fin 2 → SpaceTime → ℝ} {CΦ : ℝ},
      0 ≤ CΦ → (∀ i j, Measurable (Φ i j)) →
      (∀ z, 0 < torusParabolicSize z → IsArrR (fun i j => Φ i j z)
        (CΦ * torusParabolicSize z ^ (-(1 : ℝ)))
        (min 1 (ipsiRatio m θ (torusParabolicSize z)))) →
      ∀ (x y : ParabolicSpace) {g : SpaceTime}, 0 < torusParabolicSize (spaceTimeProj x - g) →
        (∀ i j, Integrable (fun w => ipsiTaylorKernel N x y w * Φ i j (w - g))) ∧
        IsArrR (fun i j => ∫ w, ipsiTaylorKernel N x y w * Φ i j (w - g))
          (C * CΦ * (parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
            (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-p)))
          (min 1 (ipsiRatio m θ (torusParabolicSize (spaceTimeProj x - g)))) := by
  obtain ⟨C1, hC1, g1⟩ := ipsiTaylorKernel_pairing_gen N hp hp1 hγ hγ1 (b := 1) le_rfl
    (by linarith)
  obtain ⟨C2, hC2, g2⟩ := ipsiTaylorKernel_pairing_gen2 N hp hp1 hγ hγ1 (b₁ := 1) (b₂ := 1 + θ)
    le_rfl (by linarith) (by linarith)
  obtain ⟨C3, hC3, g3⟩ := ipsiTaylorKernel_pairing_gen2 N hp hp1 hγ hγ1 (b₁ := 1) (b₂ := 1 + 2 * θ)
    le_rfl (by linarith) (by linarith)
  refine ⟨C1 + C2 + 2 * C3, by positivity, ?_⟩
  intro m hm0 Φ CΦ hCΦ hmeas hΦ x y g hg
  set r := parabolicNorm (y - x) with hr
  set W := r ^ γ * (1 + r) with hWdef
  set e := torusParabolicSize (spaceTimeProj x - g) with hedef
  set Ep := 1 + e ^ (-p) with hEpdef
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hW0 : 0 ≤ W := mul_nonneg (Real.rpow_nonneg hr0 _) (by linarith)
  have hEp0 : 0 ≤ Ep := by
    have := Real.rpow_nonneg hg.le (-p); rw [hEpdef]; linarith
  have hσe0 : 0 ≤ ipsiRatio m θ e := ipsiRatio_nonneg m θ e hm0 hg.le
  have hb0 : 0 ≤ CΦ * W * Ep := mul_nonneg (mul_nonneg hCΦ hW0) hEp0
  have hepos : 0 < e := hg
  have hsplit1 : 1 + e ^ (-(p + 1 - 1 + θ)) ≤ Ep * (1 + e ^ (-θ)) := by
    have := one_add_rpow_neg_add_le (e := e) (a := p) (b := θ) hg
    rw [show p + 1 - 1 + θ = p + θ by ring]; exact this
  have crude := fun z (hz : 0 < torusParabolicSize z) =>
    ipsi_arrR_crude (Real.rpow_nonneg hz.le (-(1 : ℝ))) hCΦ (hΦ z hz)
  have ratio := fun z (hz : 0 < torusParabolicSize z) =>
    ipsi_arrR_ratio hm0 hz hCΦ (hΦ z hz)
  have hentry : ∀ i j z, 0 < torusParabolicSize z →
      |Φ i j z| ≤ (6 * CΦ) * torusParabolicSize z ^ (-(1 : ℝ)) := by
    intro i j z hz
    obtain ⟨a1, a2, a3, a4, -⟩ := crude z hz
    have hCS : 0 ≤ CΦ * torusParabolicSize z ^ (-(1 : ℝ)) :=
      mul_nonneg hCΦ (Real.rpow_nonneg hz.le _)
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith
  have hint : ∀ i j, Integrable (fun w => ipsiTaylorKernel N x y w * Φ i j (w - g)) :=
    fun i j => (g1 (hmeas i j) (by positivity) (hentry i j) x y hg).1
  refine ⟨hint, ?_⟩
  -- the three integral bounds
  have base11 : |∫ w, ipsiTaylorKernel N x y w * Φ 1 1 (w - g)| ≤ C1 * (CΦ * W * Ep) := by
    have := (g1 (hmeas 1 1) hCΦ (fun z hz => (crude z hz).1) x y hg).2
    rw [show p + 1 - 1 = p by ring] at this
    calc _ ≤ C1 * CΦ * W * Ep := this
      _ = _ := by ring
  have firstdiff : ∀ Ψ : SpaceTime → ℝ, Measurable Ψ →
      (∀ z, 0 < torusParabolicSize z → |Ψ z| ≤ CΦ * torusParabolicSize z ^ (-(1 : ℝ))) →
      (∀ z, 0 < torusParabolicSize z → |Ψ z| ≤ (CΦ * m ^ θ) *
        (torusParabolicSize z ^ (-(1 : ℝ)) + torusParabolicSize z ^ (-(1 + θ)))) →
      |∫ w, ipsiTaylorKernel N x y w * Ψ (w - g)| ≤
        max C2 C1 * (CΦ * W * Ep) * (min 1 (ipsiRatio m θ e)) ^ 1 := by
    intro Ψ hΨm hc hr'
    have a1 := (g1 hΨm hCΦ hc x y hg).2
    rw [show p + 1 - 1 = p by ring] at a1
    have hmθ : 0 ≤ m ^ θ := Real.rpow_nonneg hm0 _
    have a2 := (g2 hΨm (mul_nonneg hCΦ hmθ) (fun z hz => hr' z hz) x y hg).2
    rw [show p + (1 + θ) - 1 = p + θ by ring] at a2
    refine cap_le 1 hb0 hσe0 ?_ (a1.trans (le_of_eq (by ring)))
    refine a2.trans ?_
    have hWm : 0 ≤ C2 * (CΦ * m ^ θ) * W := mul_nonneg (mul_nonneg hC2 (mul_nonneg hCΦ hmθ)) hW0
    have := mul_le_mul_of_nonneg_left hsplit1 hWm
    calc C2 * (CΦ * m ^ θ) * W * (1 + e ^ (-(p + θ)))
        ≤ C2 * (CΦ * m ^ θ) * W * (Ep * (1 + e ^ (-θ))) := by
          rw [show p + 1 - 1 + θ = p + θ by ring] at this; exact this
      _ = C2 * (CΦ * W * Ep) * ipsiRatio m θ e ^ 1 := by
          unfold ipsiRatio; ring
  have seconddiff : ∀ Ψ : SpaceTime → ℝ, Measurable Ψ →
      (∀ z, 0 < torusParabolicSize z → |Ψ z| ≤ CΦ * torusParabolicSize z ^ (-(1 : ℝ))) →
      (∀ z, 0 < torusParabolicSize z → |Ψ z| ≤ (2 * CΦ * m ^ (2 * θ)) *
        (torusParabolicSize z ^ (-(1 : ℝ)) + torusParabolicSize z ^ (-(1 + 2 * θ)))) →
      |∫ w, ipsiTaylorKernel N x y w * Ψ (w - g)| ≤
        max (2 * C3) C1 * (CΦ * W * Ep) * (min 1 (ipsiRatio m θ e)) ^ 2 := by
    intro Ψ hΨm hc hr'
    have a1 := (g1 hΨm hCΦ hc x y hg).2
    rw [show p + 1 - 1 = p by ring] at a1
    have hmθ : 0 ≤ m ^ (2 * θ) := Real.rpow_nonneg hm0 _
    have a2 := (g3 hΨm (mul_nonneg (mul_nonneg (by norm_num) hCΦ) hmθ) (fun z hz => hr' z hz)
      x y hg).2
    rw [show p + (1 + 2 * θ) - 1 = p + 2 * θ by ring] at a2
    refine cap_le 2 hb0 hσe0 ?_ (a1.trans (le_of_eq (by ring)))
    refine a2.trans ?_
    have hm2 : m ^ (2 * θ) = (m ^ θ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
    have hs2 : 1 + e ^ (-(p + 2 * θ)) ≤ Ep * (1 + e ^ (-θ)) ^ 2 := by
      have := one_add_rpow_neg_add_le (e := e) (a := p) (b := 2 * θ) hg
      have h2 : 1 + e ^ (-(2 * θ)) ≤ (1 + e ^ (-θ)) ^ 2 := by
        have : e ^ (-(2 * θ)) = (e ^ (-θ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le]; congr 1; push_cast; ring
        rw [this]; linarith [Real.rpow_nonneg hg.le (-θ)]
      calc _ ≤ _ := this
        _ ≤ Ep * (1 + e ^ (-θ)) ^ 2 := mul_le_mul_of_nonneg_left h2 hEp0
    have hWm : 0 ≤ C3 * (2 * CΦ * m ^ (2 * θ)) * W :=
      mul_nonneg (mul_nonneg hC3 (mul_nonneg (mul_nonneg (by norm_num) hCΦ) hmθ)) hW0
    have := mul_le_mul_of_nonneg_left hs2 hWm
    calc C3 * (2 * CΦ * m ^ (2 * θ)) * W * (1 + e ^ (-(p + 2 * θ)))
        ≤ C3 * (2 * CΦ * m ^ (2 * θ)) * W * (Ep * (1 + e ^ (-θ)) ^ 2) := this
      _ = (2 * C3) * (CΦ * W * Ep) * ipsiRatio m θ e ^ 2 := by
          unfold ipsiRatio; rw [hm2]; ring
  have cm : 0 ≤ min 1 (ipsiRatio m θ e) := le_min zero_le_one hσe0
  have cm1 : min 1 (ipsiRatio m θ e) ≤ 1 := min_le_left _ _
  have hCf : 0 ≤ C1 + C2 + 2 * C3 := by positivity
  have mx1 : max C2 C1 ≤ C1 + C2 + 2 * C3 := max_le (by linarith) (by linarith)
  have mx2 : max (2 * C3) C1 ≤ C1 + C2 + 2 * C3 := max_le (by linarith) (by linarith)
  have hbm : 0 ≤ CΦ * W * Ep * min 1 (ipsiRatio m θ e) := mul_nonneg hb0 cm
  have hbm2 : 0 ≤ CΦ * W * Ep * (min 1 (ipsiRatio m θ e)) ^ 2 := mul_nonneg hb0 (sq_nonneg _)
  -- first differences
  have fd01 : |(∫ w, ipsiTaylorKernel N x y w * Φ 0 1 (w - g)) -
      ∫ w, ipsiTaylorKernel N x y w * Φ 1 1 (w - g)| ≤
      max C2 C1 * (CΦ * W * Ep) * (min 1 (ipsiRatio m θ e)) ^ 1 := by
    have := firstdiff (fun z => Φ 0 1 z - Φ 1 1 z) ((hmeas 0 1).sub (hmeas 1 1))
      (fun z hz => (crude z hz).2.2.2.2.1) (fun z hz => (ratio z hz).1) 
    rw [← integral_sub (hint 0 1) (hint 1 1)]
    simp only [← mul_sub]
    exact this
  have fd10 : |(∫ w, ipsiTaylorKernel N x y w * Φ 1 0 (w - g)) -
      ∫ w, ipsiTaylorKernel N x y w * Φ 1 1 (w - g)| ≤
      max C2 C1 * (CΦ * W * Ep) * (min 1 (ipsiRatio m θ e)) ^ 1 := by
    have := firstdiff (fun z => Φ 1 0 z - Φ 1 1 z) ((hmeas 1 0).sub (hmeas 1 1))
      (fun z hz => (crude z hz).2.2.2.2.2.1) (fun z hz => (ratio z hz).2.1)
    rw [← integral_sub (hint 1 0) (hint 1 1)]
    simp only [← mul_sub]
    exact this
  have sd : |arrSd (fun i j => ∫ w, ipsiTaylorKernel N x y w * Φ i j (w - g))| ≤
      max (2 * C3) C1 * (CΦ * W * Ep) * (min 1 (ipsiRatio m θ e)) ^ 2 := by
    have := seconddiff (fun z => Φ 0 0 z - Φ 0 1 z - Φ 1 0 z + Φ 1 1 z)
      ((((hmeas 0 0).sub (hmeas 0 1)).sub (hmeas 1 0)).add (hmeas 1 1))
      (fun z hz => (crude z hz).2.2.2.2.2.2) (fun z hz => (ratio z hz).2.2)
    unfold arrSd
    simp only
    have e : ∫ w, ipsiTaylorKernel N x y w * (Φ 0 0 (w - g) - Φ 0 1 (w - g) - Φ 1 0 (w - g) +
        Φ 1 1 (w - g)) = (∫ w, ipsiTaylorKernel N x y w * Φ 0 0 (w - g)) -
        (∫ w, ipsiTaylorKernel N x y w * Φ 0 1 (w - g)) -
        (∫ w, ipsiTaylorKernel N x y w * Φ 1 0 (w - g)) +
        ∫ w, ipsiTaylorKernel N x y w * Φ 1 1 (w - g) := by
      rw [← integral_sd4 (hint 0 0) (hint 0 1) (hint 1 0) (hint 1 1)]
      congr 1; funext w; ring
    rw [← e]; exact this
  unfold IsArrR IsArr
  beta_reduce
  refine ⟨cm, cm1, ?_, ?_, ?_, ?_⟩
  · refine base11.trans ?_
    have := mul_le_mul_of_nonneg_right (show C1 ≤ C1 + C2 + 2 * C3 by linarith) hb0
    calc _ ≤ (C1 + C2 + 2 * C3) * (CΦ * W * Ep) := by linarith
      _ = _ := by ring
  · refine fd01.trans ?_
    rw [pow_one]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right mx1 hb0) cm
    calc _ ≤ (C1 + C2 + 2 * C3) * (CΦ * W * Ep) * min 1 (ipsiRatio m θ e) := this
      _ = _ := by ring
  · refine fd10.trans ?_
    rw [pow_one]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right mx1 hb0) cm
    calc _ ≤ (C1 + C2 + 2 * C3) * (CΦ * W * Ep) * min 1 (ipsiRatio m θ e) := this
      _ = _ := by ring
  · refine sd.trans ?_
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right mx2 hb0) (sq_nonneg (min 1 (ipsiRatio m θ e)))
    calc _ ≤ (C1 + C2 + 2 * C3) * (CΦ * W * Ep) * (min 1 (ipsiRatio m θ e)) ^ 2 := this
      _ = _ := by ring

end RegularityStructures.Phi43

end

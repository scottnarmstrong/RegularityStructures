/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceCovPair

/-!
# The second difference of the abstract covariances

For two kernels `J_a`, `J_b` with covariances `Q_ij(x) = ∫ J_i(x + w) J_j(w) dw` and constants
`c_a`, `c_b`, the second difference of the abstract covariances `i3Psi2CovPair` is the sum of the
chaos-`5` and chaos-`3` double integrals of the second differences of the kernels and of
`36 ∫ (D^a_z - D^b_z)(D^a_{z'} - D^b_{z'}) dy` (`i3Psi2CovPair_second_diff_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- A bounded measurable kernel against `δK(z, ·) δK(z', ·)` is integrable on the product. -/
theorem integrable_dK_dK_mul_bdd {K : SpaceTime → ℝ} (hKi : Integrable K)
    {χ : SpaceTime → SpaceTime → ℝ} {C : ℝ} (hχ : Measurable (Function.uncurry χ))
    (hb : ∀ w v, |χ w v| ≤ C) (z z' : SpaceTime) :
    Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ q.1 q.2) (volume.prod volume) := by
  have hprod := (integrable_i3Psi2dK hKi z).mul_prod (integrable_i3Psi2dK hKi z')
  exact hprod.mul_bdd (c := C) hχ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hb q.1 q.2)

/-- The second difference of four double integrals is the iterated integral of the second
difference of the integrands. -/
theorem double_second_diff_eq {K : SpaceTime → ℝ} {χ₁₁ χ₁₂ χ₂₁ χ₂₂ χ : SpaceTime → SpaceTime → ℝ}
    {z z' : SpaceTime}
    (h₁₁ : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ₁₁ q.1 q.2) (volume.prod volume))
    (h₁₂ : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ₁₂ q.1 q.2) (volume.prod volume))
    (h₂₁ : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ₂₁ q.1 q.2) (volume.prod volume))
    (h₂₂ : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ₂₂ q.1 q.2) (volume.prod volume))
    (hχ : ∀ w v, χ w v = χ₁₁ w v - χ₁₂ w v - χ₂₁ w v + χ₂₂ w v) :
    (∫ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₁₁ q.1 q.2
        ∂(volume.prod volume)) -
      (∫ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₁₂ q.1 q.2
        ∂(volume.prod volume)) -
      (∫ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₂₁ q.1 q.2
        ∂(volume.prod volume)) +
      (∫ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₂₂ q.1 q.2
        ∂(volume.prod volume)) =
    ∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v * χ w v := by
  have j1 : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ₁₁ q.1 q.2 - i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₁₂ q.1 q.2) (volume.prod volume) :=
    h₁₁.sub h₁₂
  have j2 : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ₁₁ q.1 q.2 - i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₁₂ q.1 q.2 -
      i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ₂₁ q.1 q.2) (volume.prod volume) := j1.sub h₂₁
  have hint : Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      χ q.1 q.2) (volume.prod volume) :=
    (j2.add h₂₂).congr (Filter.Eventually.of_forall fun q => by
      simp only [Pi.add_apply, hχ]; ring)
  have key : ∫ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ q.1 q.2
        ∂(volume.prod volume) =
      ∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v * χ w v := integral_prod _ hint
  rw [← key, ← integral_sub h₁₁ h₁₂, ← integral_sub j1 h₂₁, ← integral_add j2 h₂₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [hχ]
  ring

private theorem abs_kernel5_le {S c02 c03 c12 c13 : ℝ} (hS : 0 ≤ S) (h02 : |c02| ≤ S)
    (h03 : |c03| ≤ S) (h12 : |c12| ≤ S) (h13 : |c13| ≤ S) :
    |i3Psi2Kernel5 c02 c03 c12 c13| ≤ 120 * S ^ 5 :=
  (abs_hairerWickCubeSquareChaos_le (S := S) (c01 := 0) (c23 := 0) (by simpa using hS)
    (by simpa using hS) h02 h03 h12 h13).1

private theorem abs_kernel3_le {S c01 c23 c02 c03 c12 c13 : ℝ} (h01 : |c01| ≤ S) (h23 : |c23| ≤ S)
    (h02 : |c02| ≤ S) (h03 : |c03| ≤ S) (h12 : |c12| ≤ S) (h13 : |c13| ≤ S) :
    |i3Psi2Kernel3 c01 c23 c02 c03 c12 c13| ≤ 216 * S ^ 5 :=
  (abs_hairerWickCubeSquareChaos_le h01 h23 h02 h03 h12 h13).2.1

/-- The chaos-`5` and chaos-`3` integrands against `δK δK` are integrable. -/
theorem integrable_chaos5_pair {K Q : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQm : Measurable Q) (hQb : ∀ x, |Q x| ≤ MQ) (z z' : SpaceTime) :
    Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      i3Psi2Chaos5 Q z z' q.1 q.2) (volume.prod volume) := by
  have hS : 0 ≤ MQ := (abs_nonneg _).trans (hQb 0)
  refine integrable_dK_dK_mul_bdd hKi (χ := fun w v => i3Psi2Chaos5 Q z z' w v) (C := 120 * MQ ^ 5)
    ?_ (fun w v => abs_kernel5_le hS (hQb _) (hQb _) (hQb _) (hQb _)) z z'
  unfold i3Psi2Chaos5 i3Psi2Kernel5
  change Measurable (fun p : SpaceTime × SpaceTime => _)
  fun_prop

theorem integrable_chaos3_pair {K Qaa Qbb Qab : SpaceTime → ℝ} {MQ : ℝ} (hKi : Integrable K)
    (hQaam : Measurable Qaa) (hQbbm : Measurable Qbb) (hQabm : Measurable Qab)
    (hQaab : ∀ x, |Qaa x| ≤ MQ) (hQbbb : ∀ x, |Qbb x| ≤ MQ) (hQabb : ∀ x, |Qab x| ≤ MQ)
    (z z' : SpaceTime) :
    Integrable (fun q : SpaceTime × SpaceTime => i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 *
      i3Psi2Chaos3Gen Qaa Qbb Qab z z' q.1 q.2) (volume.prod volume) := by
  refine integrable_dK_dK_mul_bdd hKi (χ := fun w v => i3Psi2Chaos3Gen Qaa Qbb Qab z z' w v)
    (C := 216 * MQ ^ 5) ?_ (fun w v => abs_kernel3_le (hQaab _) (hQbbb _) (hQabb _) (hQabb _)
      (hQabb _) (hQabb _)) z z'
  unfold i3Psi2Chaos3Gen i3Psi2Kernel3
  change Measurable (fun p : SpaceTime × SpaceTime => _)
  fun_prop

/-- **The second difference of the abstract covariances.** -/
theorem i3Psi2CovPair_second_diff_eq {K Ja Jb Q11 Q12 Q21 Q22 : SpaceTime → ℝ}
    {Ma Mb MQ c1 c2 : ℝ} (hKi : Integrable K) (hJam : Measurable Ja) (hJbm : Measurable Jb)
    (hJab : ∀ x, |Ja x| ≤ Ma) (hJbb : ∀ x, |Jb x| ≤ Mb) (hJai : Integrable Ja)
    (hJbi : Integrable Jb) (hQ12 : ∀ x, Q12 x = ∫ w, Ja (x + w) * Jb w)
    (hQ21 : ∀ x, Q21 x = ∫ w, Jb (x + w) * Ja w) (hQ11 : ∀ x, Q11 x = ∫ w, Ja (x + w) * Ja w)
    (hQ22 : ∀ x, Q22 x = ∫ w, Jb (x + w) * Jb w) (hm11 : Measurable Q11)
    (hm12 : Measurable Q12) (hm21 : Measurable Q21) (hm22 : Measurable Q22)
    (hb11 : ∀ x, |Q11 x| ≤ MQ) (hb12 : ∀ x, |Q12 x| ≤ MQ) (hb21 : ∀ x, |Q21 x| ≤ MQ)
    (hb22 : ∀ x, |Q22 x| ≤ MQ) (z z' : SpaceTime) :
    i3Psi2CovPair K Q11 Q11 Q11 Q11 c1 c1 z z' - i3Psi2CovPair K Q11 Q12 Q21 Q22 c1 c2 z z' -
        i3Psi2CovPair K Q22 Q21 Q12 Q11 c2 c1 z z' + i3Psi2CovPair K Q22 Q22 Q22 Q22 c2 c2 z z' =
      (∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi5 Q11 Q12 Q21 Q22 (w - v) (w - z') (z - v) (z - z')) +
        (∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
          i3Psi2DiffChi3 Q11 Q12 Q21 Q22 (w - z) (v - z') (w - v) (w - z') (z - v) (z - z')) +
        36 * ∫ y, (i3Psi2D K Q11 Ja c1 z y - i3Psi2D K Q22 Jb c2 z y) *
          (i3Psi2D K Q11 Ja c1 z' y - i3Psi2D K Q22 Jb c2 z' y) := by
  unfold i3Psi2CovPair
  have t11 := i3Psi2Chaos1TotalPair_eq (Ja := Ja) (Jb := Ja) (Qaa := Q11) (Qab := Q11)
    (Qba := Q11) (Qbb := Q11) (ca := c1) (cb := c1) hJam hJam hJab hJab hJai hJai hQ11 hQ11
    hm11 hm11 hm11 hb11 hb11 hb11 hKi z z'
  have t12 := i3Psi2Chaos1TotalPair_eq (Ja := Ja) (Jb := Jb) (Qaa := Q11) (Qab := Q12)
    (Qba := Q21) (Qbb := Q22) (ca := c1) (cb := c2) hJam hJbm hJab hJbb hJai hJbi hQ12 hQ21
    hm11 hm22 hm12 hb11 hb22 hb12 hKi z z'
  have t21 := i3Psi2Chaos1TotalPair_eq (Ja := Jb) (Jb := Ja) (Qaa := Q22) (Qab := Q21)
    (Qba := Q12) (Qbb := Q11) (ca := c2) (cb := c1) hJbm hJam hJbb hJab hJbi hJai hQ21 hQ12
    hm22 hm11 hm21 hb22 hb11 hb21 hKi z z'
  have t22 := i3Psi2Chaos1TotalPair_eq (Ja := Jb) (Jb := Jb) (Qaa := Q22) (Qab := Q22)
    (Qba := Q22) (Qbb := Q22) (ca := c2) (cb := c2) hJbm hJbm hJbb hJbb hJbi hJbi hQ22 hQ22
    hm22 hm22 hm22 hb22 hb22 hb22 hKi z z'
  rw [t11, t12, t21, t22]
  -- chaos 5
  have d5 := double_second_diff_eq (K := K) (z := z) (z' := z')
    (χ₁₁ := i3Psi2Chaos5 Q11 z z') (χ₁₂ := i3Psi2Chaos5 Q12 z z')
    (χ₂₁ := i3Psi2Chaos5 Q21 z z') (χ₂₂ := i3Psi2Chaos5 Q22 z z')
    (χ := fun w v => i3Psi2DiffChi5 Q11 Q12 Q21 Q22 (w - v) (w - z') (z - v) (z - z'))
    (integrable_chaos5_pair hKi hm11 hb11 z z') (integrable_chaos5_pair hKi hm12 hb12 z z')
    (integrable_chaos5_pair hKi hm21 hb21 z z') (integrable_chaos5_pair hKi hm22 hb22 z z')
    (fun w v => rfl)
  have d3 := double_second_diff_eq (K := K) (z := z) (z' := z')
    (χ₁₁ := i3Psi2Chaos3Gen Q11 Q11 Q11 z z') (χ₁₂ := i3Psi2Chaos3Gen Q11 Q22 Q12 z z')
    (χ₂₁ := i3Psi2Chaos3Gen Q22 Q11 Q21 z z') (χ₂₂ := i3Psi2Chaos3Gen Q22 Q22 Q22 z z')
    (χ := fun w v => i3Psi2DiffChi3 Q11 Q12 Q21 Q22 (w - z) (v - z') (w - v) (w - z') (z - v)
      (z - z'))
    (integrable_chaos3_pair hKi hm11 hm11 hm11 hb11 hb11 hb11 z z')
    (integrable_chaos3_pair hKi hm11 hm22 hm12 hb11 hb22 hb12 z z')
    (integrable_chaos3_pair hKi hm22 hm11 hm21 hb22 hb11 hb21 z z')
    (integrable_chaos3_pair hKi hm22 hm22 hm22 hb22 hb22 hb22 z z')
    (fun w v => rfl)
  -- chaos 1
  obtain ⟨iDaz, bDaz⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Q11) (J := Ja) c1 hJam hJab
    hJai hm11 hb11 hKi z
  obtain ⟨iDbz, bDbz⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Q22) (J := Jb) c2 hJbm hJbb
    hJbi hm22 hb22 hKi z
  obtain ⟨iDaz', bDaz'⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Q11) (J := Ja) c1 hJam hJab
    hJai hm11 hb11 hKi z'
  obtain ⟨iDbz', bDbz'⟩ := integrable_and_bdd_i3Psi2D (K := K) (Q := Q22) (J := Jb) c2 hJbm hJbb
    hJbi hm22 hb22 hKi z'
  have mul_int : ∀ {f g : SpaceTime → ℝ} {C : ℝ}, Integrable f → AEStronglyMeasurable g volume →
      (∀ y, |g y| ≤ C) → Integrable (fun y => f y * g y) := fun hf hg hb =>
    hf.mul_bdd (c := _) hg (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have e1 := integral_sub_mul_sub_eq (f₁ := i3Psi2D K Q11 Ja c1 z) (f₂ := i3Psi2D K Q22 Jb c2 z)
    (g₁ := i3Psi2D K Q11 Ja c1 z') (g₂ := i3Psi2D K Q22 Jb c2 z')
    (mul_int iDaz iDaz'.aestronglyMeasurable bDaz') (mul_int iDaz iDbz'.aestronglyMeasurable bDbz')
    (mul_int iDbz iDaz'.aestronglyMeasurable bDaz') (mul_int iDbz iDbz'.aestronglyMeasurable bDbz')
  have d5' : i3Psi2Double K (i3Psi2Chaos5 Q11) z z' - i3Psi2Double K (i3Psi2Chaos5 Q12) z z' -
      i3Psi2Double K (i3Psi2Chaos5 Q21) z z' + i3Psi2Double K (i3Psi2Chaos5 Q22) z z' =
      ∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
        i3Psi2DiffChi5 Q11 Q12 Q21 Q22 (w - v) (w - z') (z - v) (z - z') := d5
  have d3' : i3Psi2Double K (i3Psi2Chaos3Gen Q11 Q11 Q11) z z' -
      i3Psi2Double K (i3Psi2Chaos3Gen Q11 Q22 Q12) z z' -
      i3Psi2Double K (i3Psi2Chaos3Gen Q22 Q11 Q21) z z' +
      i3Psi2Double K (i3Psi2Chaos3Gen Q22 Q22 Q22) z z' =
      ∫ w, ∫ v, i3Psi2dK K z w * i3Psi2dK K z' v *
        i3Psi2DiffChi3 Q11 Q12 Q21 Q22 (w - z) (v - z') (w - v) (w - z') (z - v) (z - z') := d3
  linarith [d5', d3', e1]

end RegularityStructures.Phi43

end

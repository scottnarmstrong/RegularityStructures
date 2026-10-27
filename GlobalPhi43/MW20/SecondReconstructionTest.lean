/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.SecondReconstructionGerm

/-!
# Testing the product-compatible second reconstruction germ

The corrected auxiliary germ's signed coherence identity is integrated with its actual recentered
YV test, V test and spatial-coordinate V tests. Finite-sum and Bochner linearity
are justified from the constituent integrability hypotheses. Their smooth
compact-test application remains part of the source seminorm attachment.
-/

public section

open MeasureTheory

namespace GlobalPhi43.MW20

/-- Integrated form of the three signed terms in the second germ's increment.
The shared local affine remainder is retained, and the counterterm C₂ stays inside
the recentered YV composite. -/
theorem secondReconstructionGerm_tested_increment {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (K v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ) (x z : E)
    (hA : Integrable (fun y => K y * ((Y y - Y z) * V y - C₂)) μ)
    (hV : Integrable (fun y => K y * V y) μ)
    (hX : ∀ i, Integrable (fun y => K y * ((X y i - X z i) * V y)) μ) :
    (∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y -
      secondReconstructionGerm v Y Z V ν X C₂ z y) ∂μ) =
      -(3 * (v x - v z)) * (∫ y, K y * ((Y y - Y z) * V y - C₂) ∂μ) -
      (Local.expansion v Y Z x z -
        ∑ i, ν x i * (X z i - X x i)) * (∫ y, K y * V y ∂μ) +
      ∑ i, (ν x i - ν z i) * (∫ y, K y * ((X y i - X z i) * V y) ∂μ) := by
  let R := Local.expansion v Y Z x z -
    ∑ i, ν x i * (X z i - X x i)
  have hsum (y : E) : K y * ((∑ i, (ν x i - ν z i) * (X y i - X z i)) * V y) =
      ∑ i, (ν x i - ν z i) * (K y * ((X y i - X z i) * V y)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hid (y : E) : K y * (secondReconstructionGerm v Y Z V ν X C₂ x y -
      secondReconstructionGerm v Y Z V ν X C₂ z y) =
      -(3 * (v x - v z)) * (K y * ((Y y - Y z) * V y - C₂)) -
      R * (K y * V y) + ∑ i, (ν x i - ν z i) * (K y * ((X y i - X z i) * V y)) := by
    rw [secondReconstructionGerm_increment]
    change K y * (-(3 * (v x - v z) * ((Y y - Y z) * V y - C₂)) - R * V y +
      (∑ i, (ν x i - ν z i) * (X y i - X z i)) * V y) = _
    rw [mul_add, mul_sub, hsum]
    ring
  have hIsum : Integrable (fun y => ∑ i, (ν x i - ν z i) *
      (K y * ((X y i - X z i) * V y))) μ := by
    exact integrable_finsetSum Finset.univ fun i _ => (hX i).const_mul _
  have hsumint : (∫ y, ∑ i, (ν x i - ν z i) *
      (K y * ((X y i - X z i) * V y)) ∂μ) =
      ∑ i, (ν x i - ν z i) * (∫ y, K y * ((X y i - X z i) * V y) ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun i _ => (hX i).const_mul _)]
    simp only [integral_const_mul]
  have hIleft : Integrable (fun y =>
      -(3 * (v x - v z)) * (K y * ((Y y - Y z) * V y - C₂)) - R * (K y * V y)) μ :=
    (hA.const_mul (-(3 * (v x - v z)))).sub (hV.const_mul R)
  rw [integral_congr_ae (Filter.Eventually.of_forall hid),
    integral_add hIleft hIsum,
    integral_sub (hA.const_mul (-(3 * (v x - v z)))) (hV.const_mul R), hsumint,
    integral_const_mul, integral_const_mul]

/-- Tested coherence with the actual source A, V and XV bounds. The local
remainder uses the shared expansion, and the finite spatial factor is explicit. -/
theorem secondReconstructionGerm_tested_increment_bound {E ι : Type*}
    [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (K v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ) (x z : E)
    (hA : Integrable (fun y => K y * ((Y y - Y z) * V y - C₂)) μ)
    (hV : Integrable (fun y => K y * V y) μ)
    (hX : ∀ i, Integrable (fun y => K y * ((X y i - X z i) * V y)) μ)
    {H R N a b c : ℝ} (hv : |v x - v z| ≤ H)
    (hU : |Local.expansion v Y Z x z - ∑ i, ν x i * (X z i - X x i)| ≤ R)
    (hν : ∀ i, |ν x i - ν z i| ≤ N)
    (ha : |∫ y, K y * ((Y y - Y z) * V y - C₂) ∂μ| ≤ a)
    (hb : |∫ y, K y * V y ∂μ| ≤ b)
    (hc : ∀ i, |∫ y, K y * ((X y i - X z i) * V y) ∂μ| ≤ c) :
    |∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y -
      secondReconstructionGerm v Y Z V ν X C₂ z y) ∂μ| ≤
      3 * H * a + R * b + (Fintype.card ι : ℝ) * N * c := by
  have hprod : ∀ {a₁ a₂ c₁ c₂ : ℝ}, |a₁| ≤ c₁ → |a₂| ≤ c₂ →
      |a₁ * a₂| ≤ c₁ * c₂ := by
    intro a₁ a₂ c₁ c₂ ha₁ ha₂
    rw [abs_mul]
    exact mul_le_mul ha₁ ha₂ (abs_nonneg _) ((abs_nonneg _).trans ha₁)
  have h₁ : |-(3 * (v x - v z)) *
      (∫ y, K y * ((Y y - Y z) * V y - C₂) ∂μ)| ≤ 3 * H * a := by
    simpa only [neg_mul] using
      hprod (hprod (show |(-3 : ℝ)| ≤ 3 by norm_num) hv) ha
  have h₂ := hprod hU hb
  have hsum : |∑ i, (ν x i - ν z i) *
      (∫ y, K y * ((X y i - X z i) * V y) ∂μ)| ≤ (Fintype.card ι : ℝ) * N * c := by
    calc
      _ ≤ ∑ i, |(ν x i - ν z i) * (∫ y, K y * ((X y i - X z i) * V y) ∂μ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, N * c := Finset.sum_le_sum fun i _ => hprod (hν i) (hc i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  have htriangle (p q r : ℝ) : |p - q + r| ≤ |p| + |q| + |r| := by
    apply (abs_add_le (p - q) r).trans
    apply add_le_add _ (le_refl |r|)
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le p (-q)
  rw [secondReconstructionGerm_tested_increment μ K v Y Z V ν X C₂ x z hA hV hX]
  exact (htriangle _ _ _).trans (add_le_add (add_le_add h₁ h₂) hsum)

end GlobalPhi43.MW20

end

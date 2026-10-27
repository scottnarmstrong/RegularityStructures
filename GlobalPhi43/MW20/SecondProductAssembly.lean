/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.SecondProductSmooth

/-!
# The actual signed Lemma 2.10 reconstruction estimate

The corrected auxiliary germ is assembled with canonical D, A and XV tests.
This is conditional on the actual reconstruction-error bound, not a proof of
Theorem 2.8 or of the source seminorm attachment. Smooth compact tests derive all
integrability facts in the final wrapper.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace GlobalPhi43.MW20

/-- Integral version of the exact signed Lemma 2.10 estimate identity. -/
theorem secondReconstructionGerm_tested_consumer {E ι : Type*}
    [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (K v J Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ) (x : E)
    (hE : Integrable (fun y => K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y)) μ)
    (hD : Integrable (fun y => K y * ((Z y - Z x) * V y - 3 * C₂ * J y)) μ)
    (hA : Integrable (fun y => K y * ((Y y - Y x) * V y - C₂)) μ)
    (hX : ∀ i, Integrable (fun y => K y * ((X y i - X x i) * V y)) μ) :
    (∫ y, K y * ((v y - v x) * V y + 3 * C₂ * (v y + J y)) ∂μ) =
      -(∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y) ∂μ) -
      (∫ y, K y * ((Z y - Z x) * V y - 3 * C₂ * J y) ∂μ) -
      3 * v x * (∫ y, K y * ((Y y - Y x) * V y - C₂) ∂μ) +
      ∑ i, ν x i * (∫ y, K y * ((X y i - X x i) * V y) ∂μ) := by
  have hsum (y : E) : K y * ((∑ i, ν x i * (X y i - X x i)) * V y) =
      ∑ i, ν x i * (K y * ((X y i - X x i) * V y)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hid (y : E) : K y * ((v y - v x) * V y + 3 * C₂ * (v y + J y)) =
      -(K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y)) -
      K y * ((Z y - Z x) * V y - 3 * C₂ * J y) -
      3 * v x * (K y * ((Y y - Y x) * V y - C₂)) +
      ∑ i, ν x i * (K y * ((X y i - X x i) * V y)) := by
    rw [secondReconstructionGerm_consumer_identity v J Y Z V ν X C₂ x y, mul_add, hsum]
    ring
  have hIsum : Integrable (fun y => ∑ i, ν x i * (K y * ((X y i - X x i) * V y))) μ :=
    integrable_finsetSum Finset.univ fun i _ => (hX i).const_mul _
  have hIEneg : Integrable (fun y => -(K y *
      (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y))) μ := hE.neg
  have hIED : Integrable (fun y => -(K y *
      (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y)) -
      K y * ((Z y - Z x) * V y - 3 * C₂ * J y)) μ := hIEneg.sub hD
  have hIleft : Integrable (fun y =>
      -(K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y)) -
      K y * ((Z y - Z x) * V y - 3 * C₂ * J y) -
      3 * v x * (K y * ((Y y - Y x) * V y - C₂))) μ :=
    hIED.sub (hA.const_mul (3 * v x))
  have hsumint : (∫ y, ∑ i, ν x i * (K y * ((X y i - X x i) * V y)) ∂μ) =
      ∑ i, ν x i * (∫ y, K y * ((X y i - X x i) * V y) ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun i _ => (hX i).const_mul _)]
    simp only [integral_const_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hid), integral_add hIleft hIsum,
    integral_sub hIED (hA.const_mul (3 * v x)),
    integral_sub hIEneg hD, integral_neg, integral_const_mul, hsumint]

/-- Source product budget from its actual signed reconstruction error and
canonical D, A and XV tests. No bound on C₂ is added. -/
theorem secondReconstructionGerm_product_bound {E ι : Type*}
    [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (K v J Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ) (x : E)
    (hE : Integrable (fun y => K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y)) μ)
    (hD : Integrable (fun y => K y * ((Z y - Z x) * V y - 3 * C₂ * J y)) μ)
    (hA : Integrable (fun y => K y * ((Y y - Y x) * V y - C₂)) μ)
    (hX : ∀ i, Integrable (fun y => K y * ((X y i - X x i) * V y)) μ)
    {R D A M N NX : ℝ}
    (hrec : |∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y) ∂μ| ≤ R)
    (hd : |∫ y, K y * ((Z y - Z x) * V y - 3 * C₂ * J y) ∂μ| ≤ D)
    (ha : |∫ y, K y * ((Y y - Y x) * V y - C₂) ∂μ| ≤ A)
    (hv : |v x| ≤ M) (hν : ∀ i, |ν x i| ≤ N)
    (hx : ∀ i, |∫ y, K y * ((X y i - X x i) * V y) ∂μ| ≤ NX) :
    |∫ y, K y * ((v y - v x) * V y + 3 * C₂ * (v y + J y)) ∂μ| ≤
      R + D + 3 * M * A + (Fintype.card ι : ℝ) * N * NX := by
  let e := ∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y - v y * V y) ∂μ
  let d := ∫ y, K y * ((Z y - Z x) * V y - 3 * C₂ * J y) ∂μ
  let a := ∫ y, K y * ((Y y - Y x) * V y - C₂) ∂μ
  let xv := fun i => ∫ y, K y * ((X y i - X x i) * V y) ∂μ
  have hprod : ∀ {a₁ a₂ c₁ c₂ : ℝ}, |a₁| ≤ c₁ → |a₂| ≤ c₂ → |a₁ * a₂| ≤ c₁ * c₂ := by
    intro a₁ a₂ c₁ c₂ ha₁ ha₂
    rw [abs_mul]
    exact mul_le_mul ha₁ ha₂ (abs_nonneg _) ((abs_nonneg _).trans ha₁)
  have hlocal : |3 * v x * a| ≤ 3 * M * A :=
    hprod (hprod (show |(3 : ℝ)| ≤ 3 by norm_num) hv) ha
  have hsum : |∑ i, ν x i * xv i| ≤ (Fintype.card ι : ℝ) * N * NX := by
    calc
      _ ≤ ∑ i, |ν x i * xv i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, N * NX := Finset.sum_le_sum fun i _ => hprod (hν i) (hx i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  have hfour (p q r s : ℝ) : |p + q + r + s| ≤ |p| + |q| + |r| + |s| := by
    calc
      _ ≤ |p + q + r| + |s| := abs_add_le _ _
      _ ≤ (|p + q| + |r|) + |s| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (abs_add_le p q) le_rfl) le_rfl
  rw [secondReconstructionGerm_tested_consumer μ K v J Y Z V ν X C₂ x hE hD hA hX]
  change |-e - d - 3 * v x * a + ∑ i, ν x i * xv i| ≤ _
  have ht : |-e - d - 3 * v x * a + ∑ i, ν x i * xv i| ≤
      |e| + |d| + |3 * v x * a| + |∑ i, ν x i * xv i| := by
    simpa only [sub_eq_add_neg, abs_neg] using hfour (-e) (-d) (-(3 * v x * a)) (∑ i, ν x i * xv i)
  exact ht.trans (add_le_add (add_le_add (add_le_add hrec hd) hlocal) hsum)

end GlobalPhi43.MW20

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarSupNorm

/-! A bounded perturbation contributes only d0 squared times its supremum
to the uniform weighted one-point allowance. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

 theorem weighted_scalarSup_toReal_of_pointwise
    (f : ParabolicSpace → ℝ) (D : Set ParabolicSpace) {w B : ℝ}
    (hw : 0 ≤ w) (hB : 0 ≤ B) (hb : ∀ y ∈ D, w * |f y| ≤ B) :
    w * (localScalarSup f D).toReal ≤ B := by
  have hh : ENNReal.ofReal w * localScalarSup f D ≤ ENNReal.ofReal B := by
    simp only [localScalarSup, ENNReal.mul_iSup]
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    rw [← ENNReal.ofReal_mul hw]
    exact ENNReal.ofReal_le_ofReal (hb y hy)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw, ENNReal.toReal_ofReal hB] at hr

 theorem bounded_forcing_weighted_scale {d d₀ T L γ a F : ℝ}
    (hd : 0 < d) (hdd : d ≤ d₀) (hT : 0 < T) (hTL : T ≤ L) (hLd : L ≤ d)
    (hγ : γ ≤ 2) (ha : a ≤ 2) (hF : 0 ≤ F) :
    d ^ γ * T ^ 2 * F ≤ d₀ ^ 2 * F * (T ^ a * L ^ (γ - a)) := by
  have hL : 0 < L := hT.trans_le hTL
  have hp : d ^ γ * L ^ (2 - γ) ≤ d ^ 2 := by
    calc
      _ ≤ d ^ γ * d ^ (2 - γ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL.le hLd (by linarith))
          (Real.rpow_nonneg hd.le γ)
      _ = _ := by rw [← Real.rpow_add hd]; norm_num
  have hsq : d ^ 2 ≤ d₀ ^ 2 := by nlinarith
  have hw := mul_le_mul_of_nonneg_left (bounded_forcing_scale (γ := γ) hT hTL ha hF)
    (Real.rpow_nonneg hd.le γ)
  calc
    _ ≤ (d ^ γ * L ^ (2 - γ)) * F * (T ^ a * L ^ (γ - a)) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hw
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hp.trans hsq) hF) (by positivity)

 theorem perturbed_one_point_allowance {I : Type*} (A : Finset I) (α : I → ℝ)
    (hA : A.Nonempty) {γ : ℝ} (hαγ : ∀ i ∈ A, α i ≤ γ) (hγ : γ ≤ 2)
    (f g : ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    {d d₀ T L P F : ℝ} (hd : 0 < d) (hdd : d ≤ d₀)
    (hT : 0 < T) (hTL : T ≤ L) (hLd : L ≤ d) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hclose : ∀ y ∈ D, |f y - g y| ≤ F)
    (hbase : ∀ y ∈ D, d ^ γ * T ^ 2 * |g y| ≤
      P * ∑ i ∈ A, T ^ α i * L ^ (γ - α i)) :
    d ^ γ * T ^ 2 * (localScalarSup f D).toReal ≤
      (P + d₀ ^ 2 * F) * ∑ i ∈ A, T ^ α i * L ^ (γ - α i) := by
  obtain ⟨i, hi⟩ := hA
  have hL : 0 < L := hT.trans_le hTL
  have hsum : 0 ≤ ∑ i ∈ A, T ^ α i * L ^ (γ - α i) := by positivity
  apply weighted_scalarSup_toReal_of_pointwise f D (by positivity) (by positivity)
  intro y hy
  have he : |f y| ≤ |g y| + F := by
    calc
      _ = |g y + (f y - g y)| := by congr 1; ring
      _ ≤ |g y| + |f y - g y| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (hclose y hy)
  have herror := bounded_forcing_weighted_scale hd hdd hT hTL hLd hγ
    ((hαγ i hi).trans hγ) hF
  have hterm : T ^ α i * L ^ (γ - α i) ≤ ∑ j ∈ A, T ^ α j * L ^ (γ - α j) :=
    Finset.single_le_sum (f := fun j => T ^ α j * L ^ (γ - α j)) (fun j _ => by positivity) hi
  have herror' := herror.trans (mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ d₀ ^ 2 * F))
  have hw := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ d ^ γ * T ^ 2)
  nlinarith only [hw, hbase y hy, herror']

end GlobalPhi43.Local

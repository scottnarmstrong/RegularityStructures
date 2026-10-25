/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Causal.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# The causal shells annihilate polynomials

`∫ z^k annShellC N n z dz = 0` for `|k|_𝔰 < N` (`integral_monomial_mul_annShellC`) and
`annihilatesPolynomials_annShellC N : AnnihilatesPolynomials (fun n x y => annShellC N n (x - y)) (N - 1)`
[Hai14, Assumption 5.4].  Same proofs as for the non-causal shells.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5 and Assumption 5.4.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem annKernel0C_eq (N : ℕ) (z : ParabolicSpace) :
    annKernel0C N z = heatShell 0 z - annBumpC N z + scaledShell (annBumpC N) 1 z := by
  simp [annKernel0C, scaledShell]

theorem integral_monoFn_mul_annKernel0C {N : ℕ} (k : PolyIndex N) :
    ∫ z, monoFn k.1 z * annKernel0C N z = 0 := by
  have i1 := integrable_monoFn_mul (contDiff_heatShell 0) (fun z hz => heatShell_eq_zero
    (by simpa using hz)) k.1
  have i2 := integrable_monoFn_mul (contDiff_annBumpC N) (fun _ hz => annBumpC_eq_zero hz) k.1
  have i3 : Integrable fun z => monoFn k.1 z * scaledShell (annBumpC N) 1 z := by
    have h3 := (integrable_monoFn_mul (contDiff_scaledShell (contDiff_annBumpC N) 1)
      (fun _ hz => scaledShell_eq_zero (fun _ hz => annBumpC_eq_zero hz) (n := 1)
        (by have : (2 : ℝ)⁻¹ ^ 1 < 1 := by norm_num
            linarith)) k.1)
    exact h3
  have hpt : ∀ z, monoFn k.1 z * annKernel0C N z =
      monoFn k.1 z * heatShell 0 z - monoFn k.1 z * annBumpC N z +
        monoFn k.1 z * scaledShell (annBumpC N) 1 z := fun z => by
    rw [annKernel0C_eq]; ring
  simp_rw [hpt]
  have e1 := integral_add (i1.sub i2) i3
  have e2 := integral_sub i1 i2
  simp only [Pi.sub_apply] at e1 e2
  rw [e1, e2, integral_monoFn_mul_scaledShell]
  have hμ : ∫ z, monoFn k.1 z * annBumpC N z = annMoment k := by
    simpa only [evalParabolic_monomial_eq] using integral_monomial_mul_annBumpC k
  rw [hμ]
  set m := ∫ z, monoFn k.1 z * heatShell 0 z with hm
  have hne : (1 : ℝ) - ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹ ≠ 0 := by
    have h1 : (1 : ℝ) < 2 ^ (2 + multiDeg k.1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    have : ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  have hμm : annMoment k * (1 - ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹) = m := by
    unfold annMoment
    simp only [momentMono, evalParabolic_monomial_eq, hm]
    exact div_mul_cancel₀ _ hne
  have he : ((2 : ℝ) ^ 1) ^ 3 * (((2 : ℝ) ^ 1) ^ multiDeg k.1)⁻¹ * (((2 : ℝ) ^ 1) ^ 5)⁻¹ =
      ((2 : ℝ) ^ (2 + multiDeg k.1))⁻¹ := by
    simp only [pow_one]
    field_simp
    ring
  rw [he]
  linarith

end RegularityStructures

end

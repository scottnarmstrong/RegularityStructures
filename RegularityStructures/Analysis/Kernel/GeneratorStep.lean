/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorBridge

/-!
# The derivative of `v ↦ ∫ q_v(z - y) φ(y) dy` after integration by parts

For `φ` smooth with compact support and `v > 0`,
`∫ (∂_v q_v)(z - y) φ(y) dy = ∫ q_v(z - y) (L φ)(y) dy`, where `∂_v q_v = L q_v` pointwise
(`parabolicTimeDeriv_eq`) and the derivatives of `L` are moved onto `φ` by `D_d^n` integration by
parts (`integral_iterate_dirDeriv_mul`).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem parabolicGenerator_eq {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (y : ParabolicSpace) :
    parabolicGenerator φ y = generatorTimeCoeff * (dirDeriv timeDir)^[2] φ y -
      generatorSpaceCoeff * ∑ i : Fin 3, (dirDeriv (spaceDir i))^[4] φ y := by
  unfold parabolicGenerator
  rw [← congrFun (iteratedFDeriv_const_eq_iterate hφ timeDir 2) y]
  simp only [← congrFun (iteratedFDeriv_const_eq_iterate hφ (spaceDir _) 4) y]

theorem integral_comb {a b : ℝ} {F : ParabolicSpace → ℝ} {G : Fin 3 → ParabolicSpace → ℝ}
    (hF : Integrable F) (hG : ∀ i, Integrable (G i)) :
    ∫ y, (a * F y - b * ∑ i, G i y) = a * (∫ y, F y) - b * ∑ i, (∫ y, G i y) := by
  rw [integral_sub (hF.const_mul a) ((integrable_finsetSum _ fun i _ => hG i).const_mul b),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => hG i]

theorem integral_parabolicTimeDeriv_mul {v : ℝ} (hv : 0 < v) {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (z : ParabolicSpace) :
    ∫ y, parabolicTimeDeriv v (z - y) * φ y =
      ∫ y, parabolicKernel v (z - y) * parabolicGenerator φ y := by
  have hq := contDiff_parabolicKernel hv
  have hU : ContDiff ℝ ∞ fun y => parabolicKernel v (z - y) :=
    hq.comp (contDiff_const.sub contDiff_id)
  -- the reflected iterates, for even order
  have E : ∀ (d : ParabolicSpace) (n : ℕ), Even n → ∀ y,
      ((dirDeriv d)^[n] (parabolicKernel v)) (z - y) =
        ((dirDeriv d)^[n] fun y => parabolicKernel v (z - y)) y := by
    intro d n hn y
    have := congrFun (iterate_dirDeriv_comp_sub d z n 1 hq) y
    simp only [one_mul, hn.neg_one_pow] at this
    simpa using this.symm
  -- integrability of `D^n U * φ` and `U * D^n φ`
  have I1 : ∀ (d : ParabolicSpace) (n : ℕ), Integrable fun y =>
      ((dirDeriv d)^[n] fun y => parabolicKernel v (z - y)) y * φ y := fun d n =>
    ((contDiff_iterate_dirDeriv hU d n).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have I2 : ∀ (d : ParabolicSpace) (n : ℕ), Integrable fun y =>
      parabolicKernel v (z - y) * ((dirDeriv d)^[n] φ) y := fun d n =>
    (hU.continuous.mul (contDiff_iterate_dirDeriv hφ d n).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_iterate_dirDeriv hc d n).mul_left
  have IB : ∀ (d : ParabolicSpace) (n : ℕ), Even n →
      ∫ y, ((dirDeriv d)^[n] fun y => parabolicKernel v (z - y)) y * φ y =
        ∫ y, parabolicKernel v (z - y) * ((dirDeriv d)^[n] φ) y := by
    intro d n hn
    rw [integral_iterate_dirDeriv_mul d n hU hφ hc, hn.neg_one_pow, one_mul]
  -- left side
  have hL : ∀ y, parabolicTimeDeriv v (z - y) * φ y =
      generatorTimeCoeff * (((dirDeriv timeDir)^[2] fun y => parabolicKernel v (z - y)) y * φ y) -
        generatorSpaceCoeff * ∑ i : Fin 3,
          ((dirDeriv (spaceDir i))^[4] fun y => parabolicKernel v (z - y)) y * φ y := by
    intro y
    rw [parabolicTimeDeriv_eq hv, E timeDir 2 even_two,
      Finset.sum_congr rfl fun i _ => E (spaceDir i) 4 (by decide) y]
    simp only [sub_mul, mul_assoc, Finset.sum_mul]
  have hR : ∀ y, parabolicKernel v (z - y) * parabolicGenerator φ y =
      generatorTimeCoeff * (parabolicKernel v (z - y) * (dirDeriv timeDir)^[2] φ y) -
        generatorSpaceCoeff * ∑ i : Fin 3,
          parabolicKernel v (z - y) * (dirDeriv (spaceDir i))^[4] φ y := by
    intro y
    have e : parabolicKernel v (z - y) * (generatorSpaceCoeff *
        ∑ i : Fin 3, (dirDeriv (spaceDir i))^[4] φ y) = generatorSpaceCoeff *
        ∑ i : Fin 3, parabolicKernel v (z - y) * (dirDeriv (spaceDir i))^[4] φ y := by
      rw [mul_left_comm, Finset.mul_sum]
    rw [parabolicGenerator_eq hφ, mul_sub, e]
    ring
  simp_rw [hL, hR]
  rw [integral_comb (I1 timeDir 2) fun i => I1 (spaceDir i) 4,
    integral_comb (I2 timeDir 2) fun i => I2 (spaceDir i) 4]
  have h2 := IB timeDir 2 even_two
  have h4 := fun i : Fin 3 => IB (spaceDir i) 4 (by decide)
  rw [h2, Finset.sum_congr rfl fun i _ => h4 i]

end RegularityStructures

end

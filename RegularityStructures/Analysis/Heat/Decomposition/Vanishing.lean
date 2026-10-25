/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Scaling

/-!
# Vanishing of moments by integration by parts

If `J` is a list of coordinate indices in which some index `i` occurs more often than the exponent
`l i` of the monomial `z^l`, then `∫ z^l D_J g = 0` for every smooth compactly supported `g`.
Integrating by parts removes one derivative at a time and differentiates the monomial.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The monomial `z ↦ ∏ᵢ zᵢ^{lᵢ}` in the four parabolic coordinates. -/
def monoFn (l : Fin 4 → ℕ) (z : ParabolicSpace) : ℝ := ∏ i, parabolicCoords z i ^ l i

end RegularityStructures

end

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem evalParabolic_monomial_eq (l : Fin 4 →₀ ℕ) (z : ParabolicSpace) :
    evalParabolic (MvPolynomial.monomial l 1) z = monoFn l z := by
  unfold evalParabolic monoFn
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp), one_mul]

private theorem contDiff_parabolicCoords (i : Fin 4) : ContDiff ℝ ∞ fun z => parabolicCoords z i := by
  fin_cases i <;> simp [parabolicCoords] <;> try fun_prop

theorem contDiff_monoFn (l : Fin 4 → ℕ) : ContDiff ℝ ∞ (monoFn l) :=
  contDiff_prod fun i _ => (contDiff_parabolicCoords i).pow _

theorem coordDir_one : coordDir 1 = spaceDir 0 := rfl

theorem coordDir_two : coordDir 2 = spaceDir 1 := rfl

theorem coordDir_three : coordDir 3 = spaceDir 2 := rfl

theorem parabolicCoords_add_smul_coordDir (z : ParabolicSpace) (s : ℝ) (j i : Fin 4) :
    parabolicCoords (z + s • coordDir j) i =
      parabolicCoords z i + s * (if i = j then 1 else 0) := by
  fin_cases j <;> fin_cases i <;>
    simp [parabolicCoords, coordDir_zero, coordDir_one, coordDir_two, coordDir_three, timeDir,
      spaceDir]

theorem monoFn_add_smul_coordDir (l : Fin 4 → ℕ) (z : ParabolicSpace) (s : ℝ) (j : Fin 4) :
    monoFn l (z + s • coordDir j) =
      (parabolicCoords z j + s) ^ l j *
        ∏ i ∈ Finset.univ.erase j, parabolicCoords z i ^ l i := by
  unfold monoFn
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  congr 1
  · simp [parabolicCoords_add_smul_coordDir]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [parabolicCoords_add_smul_coordDir, Finset.ne_of_mem_erase hi]

/-- The derivative of a monomial in direction `j`. -/
theorem dirDeriv_coordDir_monoFn (l : Fin 4 → ℕ) (j : Fin 4) :
    dirDeriv (coordDir j) (monoFn l) =
      fun z => (l j : ℝ) * monoFn (Function.update l j (l j - 1)) z := by
  funext z
  rw [dirDeriv_eq_deriv_line (contDiff_monoFn l)]
  have e : (fun s : ℝ => monoFn l (z + s • coordDir j)) = fun s =>
      (parabolicCoords z j + s) ^ l j * ∏ i ∈ Finset.univ.erase j, parabolicCoords z i ^ l i :=
    funext fun s => monoFn_add_smul_coordDir l z s j
  rw [e]
  have h1 : HasDerivAt (fun s : ℝ => (parabolicCoords z j + s) ^ l j)
      ((l j : ℝ) * (parabolicCoords z j + 0) ^ (l j - 1) * 1) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (parabolicCoords z j)).pow (l j)
  rw [(h1.mul_const _).deriv]
  unfold monoFn
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self, add_zero, mul_one]
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end RegularityStructures

end

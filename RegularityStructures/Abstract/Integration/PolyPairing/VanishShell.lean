/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyPairing.Vanish
public import RegularityStructures.Analysis.Heat.Annihilating.ScaledRegularising
public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Annihilating.KernelMoment
public import RegularityStructures.Analysis.Heat.Decomposition.Regularising
public import RegularityStructures.Analysis.Kernel.GeneratorIBP
public import RegularityStructures.Abstract.Polynomial.Structure
public import RegularityStructures.Abstract.RegularityStructureDegrees

/-!
# Vanishing moments of the annihilating shells

`integral_polyEval_mul_lineIter_annShell`: `∫ (w - y)^l D^k K_n(y - w) dw = 0` for `|l|_𝔰 < N`, where
`K_n = annShell N n`.

Source: [Hai14, Assumption 5.4].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem integral_monoFn_mul_lineIter_annShell_eq_zero (N n : ℕ) (k : Fin 4 →₀ ℕ)
    (l : Fin 4 → ℕ) (hl : fnWeight l < N) :
    ∫ z, monoFn l z * lineIter (multiDirs k) (annShell N n) z = 0 := by
  refine integral_monoFn_mul_lineIter_eq_zero_of_moments
    (contDiff_scaledShell (contDiff_annKernel0 N) n)
    (hasCompactSupport_scaledShell (fun _ hz => annKernel0_eq_zero N hz) n)
    (fun l' hl' => ?_) ((Finsupp.toMultiset k).toList) l hl
  have h1 := integral_monoFn_mul_scaledShell (annKernel0 N) (Finsupp.equivFunOnFinite.symm l') n
  have h2 := integral_monoFn_mul_annKernel0
    (⟨Finsupp.equivFunOnFinite.symm l', by rw [fnWeight_equivFunOnFinite]; exact hl'⟩ :
      PolyIndex N)
  simp only [Finsupp.coe_equivFunOnFinite_symm] at h1 h2
  rw [h1, h2, mul_zero]

/-- `∫ (w - y)^l D^k K_n(y - w) dw = 0` for `|l|_𝔰 < N`. -/
theorem integral_polyEval_mul_lineIter_annShell {N N' : ℕ} (hN : N' ≤ N) (n : ℕ)
    (k : Fin 4 →₀ ℕ) (y : ParabolicSpace) (l : PolyIndex N') :
    ∫ w, polyEval y (Pi.single l 1) w * lineIter (multiDirs k) (annShell N n) (y - w) = 0 := by
  have : (volume : Measure ParabolicSpace).IsAddHaarMeasure :=
    (inferInstance : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure)
  have hl : fnWeight (l.1 : Fin 4 → ℕ) < N := by
    have h1 := l.2
    rw [← fnWeight_equivFunOnFinite] at *
    have : (Finsupp.equivFunOnFinite.symm (l.1 : Fin 4 → ℕ)) = l.1 := by ext; rfl
    rw [this]; omega
  have hsub := integral_sub_left_eq_self
    (fun v => monoFn (l.1 : Fin 4 → ℕ) (-v) * lineIter (multiDirs k) (annShell N n) v) volume y
  simp only [neg_sub] at hsub
  have e : ∀ w, polyEval y (Pi.single l 1) w * lineIter (multiDirs k) (annShell N n) (y - w) =
      monoFn (l.1 : Fin 4 → ℕ) (w - y) * lineIter (multiDirs k) (annShell N n) (y - w) := fun w => by
    rw [polyEval_single, evalParabolic_monomial_eq]
  simp_rw [e]
  rw [hsub]
  simp_rw [monoFn_neg, mul_assoc]
  rw [integral_const_mul, integral_monoFn_mul_lineIter_annShell_eq_zero N n k _ hl, mul_zero]

end RegularityStructures

end

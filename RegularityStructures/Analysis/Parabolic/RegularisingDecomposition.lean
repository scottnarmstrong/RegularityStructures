/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.SingularKernel
public import RegularityStructures.Analysis.Parabolic.Generator
public import RegularityStructures.Analysis.Parabolic.Polynomial
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Regularising kernel decompositions

`kernelDeriv`: partial derivatives of a kernel on `ℝ⁴ × ℝ⁴`; `IsRegularisingDecomposition`: a
decomposition `(K_n)_{n ≥ 0}` improving regularity by `β`.

Source: [Hai14, Assumption 5.1, (5.3)–(5.5)].
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

/-- The partial derivative `D^k K_n(x, y)` in the first (`D₁^k`) and second (`D₂^l`) argument
of a function on `ℝ⁴ × ℝ⁴`: the iterated derivative along the directions of `k` in the first
factor followed by those of `l` in the second. -/
def kernelDeriv (k l : Fin 4 →₀ ℕ) (F : ParabolicSpace → ParabolicSpace → ℝ)
    (x y : ParabolicSpace) : ℝ :=
  let L : List (ParabolicSpace × ParabolicSpace) :=
    (multiDirs k).map (fun v => (v, 0)) ++ (multiDirs l).map (fun v => (0, v))
  iteratedFDeriv ℝ L.length (Function.uncurry F) (x, y) (fun i => L.get i)

/-- Hairer's Assumption 5.1: `(K_n)_{n ≥ 0}` is a decomposition of a kernel improving regularity
by `β` [Hai14, (5.3)–(5.5)]. -/
structure IsRegularisingDecomposition (K : ℕ → ParabolicSpace → ParabolicSpace → ℝ) (β : ℝ) :
    Prop where
  smooth : ∀ n, ContDiff ℝ ∞ (Function.uncurry (K n))
  support : ∀ n x y, (2 : ℝ)⁻¹ ^ n < parabolicNorm (x - y) → K n x y = 0
  deriv_le : ∀ k l : Fin 4 →₀ ℕ, ∃ C, ∀ n x y,
    |kernelDeriv k l (K n) x y| ≤ C * (2 : ℝ) ^ ((5 - β + multiDeg l + multiDeg k) * n)
  moment_fst_le : ∀ k l : Fin 4 →₀ ℕ, ∃ C, ∀ n y,
    |∫ x, evalParabolic (MvPolynomial.monomial l 1) (x - y) * kernelDeriv 0 k (K n) x y| ≤
      C * (2 : ℝ) ^ (-β * n)
  moment_snd_le : ∀ k l : Fin 4 →₀ ℕ, ∃ C, ∀ n x,
    |∫ y, evalParabolic (MvPolynomial.monomial l 1) (y - x) * kernelDeriv k 0 (K n) x y| ≤
      C * (2 : ℝ) ^ (-β * n)

end RegularityStructures

end

public section

namespace RegularityStructures

end RegularityStructures

end

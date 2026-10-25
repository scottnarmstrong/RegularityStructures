/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Bounds
public import Phi43.Structure.AbstractPolynomial
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Model

/-!
# The deterministic part `Dπ` of the `Π`-components

`Dπ` is the set of polynomial symbols, the range of the embedding of `phi43PolynomialSector`.
For *every* model `Z` that is polynomial compatible (`Z.IsPolyCompatible`, in particular for every
model with `IsRenormalisedCanonicalModel`, via `IsRealisingP.poly`), and every `i ∈ Dπ`,

* `|(Q_t Π_x e_i)(x)| ≤ C t^(deg i / 4)` with the explicit constant `polyPiConst 2`
  (`abs_regPi_diag_le_of_mem_piDeterministic`), pathwise, for every `t > 0` and `x`;
* `Q_t Π_x e_i` does not depend on the model (`regPi_eq_of_mem_piDeterministic`), so the
  difference of two polynomial compatible models vanishes.
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- The deterministic part `Dπ`: the polynomial symbols. -/
def piDeterministic : Set Symbol := Set.range phi43PolyEmb

end RegularityStructures.Phi43

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {κ : Kappa} {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- **Pathwise bound on `Dπ`.** -/
theorem abs_regPi_diag_le_of_mem_piDeterministic
    (hpoly : Z.IsPolyCompatible (phi43PolynomialSector κ)) {i : Symbol}
    (hi : i ∈ piDeterministic) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    |Z.regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t x| ≤
      polyPiConst 2 * t ^ (homogeneity κ i / parabolicSemigroup.order) := by
  obtain ⟨k, rfl⟩ := hi
  have h := abs_polyReg_single_le (N := 2) k ht x
  have e := hpoly x k t x
  rw [phi43PolynomialSector_emb] at e
  rw [e, phi43PolyEmb_deg]
  have hC : parabolicMomentConst (polyDeg 2 k) ≤ polyPiConst 2 :=
    Finset.single_le_sum (f := fun k : PolyIndex 2 => parabolicMomentConst (polyDeg 2 k))
      (fun j _ => parabolicMomentConst_nonneg _) (Finset.mem_univ k)
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.le _)

/-- **`Dπ` does not depend on the model**: the difference of two polynomial compatible models
vanishes on the polynomial symbols. -/
theorem regPi_eq_of_mem_piDeterministic
    (hpoly : Z.IsPolyCompatible (phi43PolynomialSector κ))
    (hpoly' : Z'.IsPolyCompatible (phi43PolynomialSector κ)) {i : Symbol}
    (hi : i ∈ piDeterministic) (x : ParabolicSpace) (t : ℝ) (z : ParabolicSpace) :
    Z.regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t z =
      Z'.regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t z := by
  obtain ⟨k, rfl⟩ := hi
  have e := hpoly x k t z
  have e' := hpoly' x k t z
  rw [phi43PolynomialSector_emb] at e e'
  rw [e, e']

/-- The difference bound on `Dπ`, in the form of the Kolmogorov bound for the model norms: the
difference is `0`. -/
theorem abs_regPi_diag_sub_le_of_mem_piDeterministic
    (hpoly : Z.IsPolyCompatible (phi43PolynomialSector κ))
    (hpoly' : Z'.IsPolyCompatible (phi43PolynomialSector κ)) {i : Symbol}
    (hi : i ∈ piDeterministic) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) {C ε θ : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    |Z.regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t x -
        Z'.regPi x (Pi.single i (1 : ℝ) : Symbol → ℝ) t x| ≤
      C * ε ^ θ * t ^ (homogeneity κ i / parabolicSemigroup.order) := by
  rw [regPi_eq_of_mem_piDeterministic hpoly hpoly' hi, sub_self, abs_zero]
  exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hε _)) (Real.rpow_nonneg ht.le _)

end RegularityStructures.Phi43

end

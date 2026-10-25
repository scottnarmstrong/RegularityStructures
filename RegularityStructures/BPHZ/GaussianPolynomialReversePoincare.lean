/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialProjection
public import RegularityStructures.BPHZ.GaussianPolynomialCalculus

/-!
# Reverse Poincaré inequality for Gaussian polynomials (algebraic form)

For a polynomial `f` of total degree at most `m`, the Dirichlet form is bounded by `m` times the
`L²(γ)` norm squared, with no dependence on the number of variables:
`∑ i, E[(∂_i f)²] ≤ m E[f²]` (`sum_gaussExp_sq_pderiv_le`).

The proof is by induction on `m`.  Split `f = g + h` with `h` the `L²(γ)` projection of `f` onto
polynomials of degree at most `m - 1`.  The generator satisfies `gaussGen g - m g` of degree
below `m`, hence orthogonal to `g`, so `E[g L g] = m E[g²]`, and the cross terms vanish by
symmetry of the generator.
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

theorem gaussExp_zero : gaussExp (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [gaussExp]

theorem totalDegree_smul_le' (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    (c • p).totalDegree ≤ p.totalDegree :=
  totalDegree_smul_le c p

/-- The reverse Poincaré inequality for polynomials, in the algebraic form. -/
theorem sum_gaussExp_sq_pderiv_le (m : ℕ) : ∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ m →
    ∑ i, gaussExp (pderiv i f * pderiv i f) ≤ m * gaussExp (f * f) := by
  induction m with
  | zero =>
    intro f hf
    simp [pderiv_eq_zero_of_totalDegree_le_zero hf, gaussExp_zero]
  | succ m ih =>
    intro f hf
    obtain ⟨h, hh, horth⟩ := exists_orthogonal_part m f
    set g := f - h with hg
    have hfgh : f = g + h := by rw [hg]; ring
    have hGh : (gaussGen h).totalDegree ≤ m := totalDegree_gaussGen_le hh
    have hA : gaussExp (g * gaussGen h) = 0 := horth _ hGh
    have hB : gaussExp (h * gaussGen g) = 0 := by
      rw [gaussExp_mul_gaussGen_comm]; exact hA
    have hgh : gaussExp (g * h) = 0 := horth _ hh
    have hu : (gaussGen g - ((m + 1 : ℕ) : ℝ) • g).totalDegree ≤ m := by
      have e : gaussGen g - ((m + 1 : ℕ) : ℝ) • g =
          (gaussGen f - ((m + 1 : ℕ) : ℝ) • f) - (gaussGen h - ((m + 1 : ℕ) : ℝ) • h) := by
        rw [hg, map_sub]; module
      rw [e]
      refine (totalDegree_sub _ _).trans (max_le (totalDegree_gaussGen_sub_le hf) ?_)
      refine (totalDegree_sub _ _).trans (max_le hGh ?_)
      exact (totalDegree_smul_le' _ _).trans hh
    have hC : gaussExp (g * gaussGen g) = (m + 1 : ℕ) * gaussExp (g * g) := by
      have h0 : gaussExp (g * (gaussGen g - ((m + 1 : ℕ) : ℝ) • g)) = 0 := by
        exact horth _ hu
      have e : g * gaussGen g = g * (gaussGen g - ((m + 1 : ℕ) : ℝ) • g) +
          ((m + 1 : ℕ) : ℝ) • (g * g) := by
        rw [mul_sub, mul_smul_comm]; abel
      rw [e, gaussExp_add, h0, gaussExp_smul, zero_add]
    have hD := ih h hh
    have hEf : ∑ i, gaussExp (pderiv i f * pderiv i f) = gaussExp (f * gaussGen f) :=
      sum_gaussExp_pderiv_mul_pderiv f f
    have hEh : ∑ i, gaussExp (pderiv i h * pderiv i h) = gaussExp (h * gaussGen h) :=
      sum_gaussExp_pderiv_mul_pderiv h h
    have hexp : f * gaussGen f = g * gaussGen g + g * gaussGen h + h * gaussGen g +
        h * gaussGen h := by
      conv_lhs => rw [hfgh]
      rw [map_add]; ring
    have hff : f * f = g * g + (2 : ℝ) • (g * h) + h * h := by
      conv_lhs => rw [hfgh]
      rw [two_smul]; ring
    have hBff : gaussExp (f * f) = gaussExp (g * g) + gaussExp (h * h) := by
      rw [hff, gaussExp_add, gaussExp_add, gaussExp_smul, hgh]; ring
    rw [hEf, hexp, gaussExp_add, gaussExp_add, gaussExp_add, hA, hB, hC, hBff]
    rw [← hEh] at *
    have hhh := gaussExp_sq_nonneg h
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hC ⊢
    nlinarith [hD]

end RegularityStructures

end

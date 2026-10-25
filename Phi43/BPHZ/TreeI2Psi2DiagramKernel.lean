/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramBounded
public import Phi43.BPHZ.KernelCalculusIncrement

/-!
# The increment of the kernel `K` against singular weights

For `K` with `|K| ≤ B s^(-3)`, increments `|K(u + h) - K u| ≤ B s(h) s(u)^(-4)` for `s(h) ≤ s(u)/2`
and time support `|t| ≤ 1`, put `A(w) = K(y - w) - K(x - w)`.  By [Hai14, Lemma 10.18] (in the form
`abs_sub_le_of_increment`), for `θ ∈ [0, 1]`,
`|A(w)| ≤ 12 B s(y - x)^θ (s(y - w)^(-3-θ) + s(x - w)^(-3-θ))`
(`abs_kernel_sub_le`), and `A` vanishes outside the slab `|t - x₀| ≤ 2` when `|y₀ - x₀| ≤ 1`
(`abs_kernel_sub_le_slab`).  Integrating against one or two further singular weights gives
the three estimates used for the diagram integrals of `I(Ψ²) Ψ²`:

* `i2Psi2LintBound_kernel_sub_two`: against `s(g - w)^(-2)` (total order `5 + θ > 5`);
* `i2Psi2LintBound_kernel_sub_three`: against `s(g₁ - w)^(-1) s(g₂ - w)^(-κ)`;
* `i2Psi2LintBound_kernel_sub_slab`: against two weights of total exponent `< 2 - θ`,
  on the slab (a bounded integral).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- [Hai14, Lemma 10.18] applied to `A(w) = K(y - w) - K(x - w)`:
`|A(w)| ≤ 12 B s(y - x)^θ (s(y - w)^(-3-θ) + s(x - w)^(-3-θ))`. -/
theorem abs_kernel_sub_le {K : SpaceTime → ℝ} {B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hKb : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ)))
    (hKi : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    {x y w : SpaceTime} (hy : 0 < torusParabolicSize (y - w)) (hx : 0 < torusParabolicSize (x - w)) :
    |K (y - w) - K (x - w)| ≤ 12 * B * torusParabolicSize (y - x) ^ θ *
      (torusParabolicSize (y - w) ^ (-(3 + θ)) + torusParabolicSize (x - w) ^ (-(3 + θ))) := by
  have hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(3 : ℝ) - 1) := by
    intro u h hu hh
    have e : (-(3 : ℝ) - 1) = -(4 : ℝ) := by norm_num
    rw [e]
    exact hKi u h hu hh
  have h := abs_sub_le_of_increment (f := K) (a := 3) hB hθ0 hθ1 hKb hinc hy hx
  have e1 : y - w - (x - w) = y - x := by abel
  have e2 : (-(3 : ℝ) - θ) = -(3 + θ) := by ring
  rw [e1, e2] at h
  exact h

/-- `A` vanishes outside the slab `|t - x₀| ≤ 2` when `|y₀ - x₀| ≤ 1`. -/
theorem kernel_sub_eq_zero_of_not_slab {K : SpaceTime → ℝ}
    (hKs : ∀ u : SpaceTime, 1 < |u.1| → K u = 0) {x y w : SpaceTime} (hxy : |y.1 - x.1| ≤ 1)
    (hw : i2Psi2Slab x.1 w = 0) : K (y - w) - K (x - w) = 0 := by
  have hw' : ¬ |w.1 - x.1| ≤ 2 := fun h => by
    have := i2Psi2Slab_of_le h
    rw [this] at hw
    exact one_ne_zero hw
  have h1 : K (y - w) = 0 := by
    refine hKs _ ?_
    by_contra hc
    refine hw' ?_
    have hc' : |(y - w).1| ≤ 1 := not_lt.1 hc
    simp only [Prod.fst_sub] at hc'
    calc |w.1 - x.1| = |(y.1 - x.1) - (y.1 - w.1)| := by congr 1; ring
      _ ≤ |y.1 - x.1| + |y.1 - w.1| := abs_sub _ _
      _ ≤ 2 := by linarith
  have h2 : K (x - w) = 0 := by
    refine hKs _ ?_
    by_contra hc
    refine hw' ?_
    have hc' : |(x - w).1| ≤ 1 := not_lt.1 hc
    simp only [Prod.fst_sub] at hc'
    calc |w.1 - x.1| = |x.1 - w.1| := abs_sub_comm _ _
      _ ≤ 2 := by linarith
  rw [h1, h2, sub_zero]

/-- The bound `abs_kernel_sub_le` with the slab factor. -/
theorem abs_kernel_sub_le_slab {K : SpaceTime → ℝ} {B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hKs : ∀ u : SpaceTime, 1 < |u.1| → K u = 0)
    (hKb : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ)))
    (hKi : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    {x y w : SpaceTime} (hxy : |y.1 - x.1| ≤ 1) (hy : 0 < torusParabolicSize (y - w))
    (hx : 0 < torusParabolicSize (x - w)) :
    |K (y - w) - K (x - w)| ≤ i2Psi2Slab x.1 w * (12 * B * torusParabolicSize (y - x) ^ θ *
      (torusParabolicSize (y - w) ^ (-(3 + θ)) + torusParabolicSize (x - w) ^ (-(3 + θ)))) := by
  by_cases hw : i2Psi2Slab x.1 w = 0
  · rw [kernel_sub_eq_zero_of_not_slab hKs hxy hw, hw]
    simp
  · have h1 := abs_sub_le_two_of_i2Psi2Slab_ne_zero hw
    rw [i2Psi2Slab_of_le h1, one_mul]
    exact abs_kernel_sub_le hB hθ0 hθ1 hKb hKi hy hx

end RegularityStructures

end

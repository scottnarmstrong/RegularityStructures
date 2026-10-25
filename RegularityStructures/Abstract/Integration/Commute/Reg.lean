/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.Compat
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Integration.Realising.Reg

/-!
# `Q_t Π_x (I + J(x)) e_i = Q_t (K ∗ Π_x e_i)`

For a realising, polynomially compatible model and a basis vector `e_i ∈ V` with `deg i < γ`,

  `(Q_t Π_x (I e_i + J(x) e_i))(z) = Q_t (kConv N (Π_x e_i)) (z)`  for `t > 0`

(`regPi_integral_add_jMap`; [Hai14, proof of Lemma 5.16]). Indeed `Q_t Π_x I e_i = Q_t g_{x,i}`
(`RealisesKernel`) and `Π_x J(x) e_i` is the polynomial `∑_k jCoeff/k! (· - x)^k`
(`IsPolyCompatible`), and `g_{x,i} + ∑_k jCoeff/k! (· - x)^k = kConv N (Π_x e_i)` by the germ identity
`realGerm_eq`. The hypothesis `hN'` says that `jVec` uses exactly the multi-indices `taylorIdx (deg i + 2)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Functions of polynomial growth are closed under subtraction. -/
theorem PolyBounded.sub {f g : ParabolicSpace → ℝ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun w => f w - g w) := by
  obtain ⟨hfm, B₁, n₁, h₁⟩ := hf
  obtain ⟨hgm, B₂, n₂, h₂⟩ := hg
  refine ⟨hfm.sub hgm, |B₁| + |B₂|, max n₁ n₂, fun u => ?_⟩
  have hu : 1 ≤ 1 + parabolicNorm u := by linarith [parabolicNorm_nonneg u]
  have e1 : (1 + parabolicNorm u) ^ n₁ ≤ (1 + parabolicNorm u) ^ max n₁ n₂ :=
    pow_le_pow_right₀ hu (le_max_left _ _)
  have e2 : (1 + parabolicNorm u) ^ n₂ ≤ (1 + parabolicNorm u) ^ max n₁ n₂ :=
    pow_le_pow_right₀ hu (le_max_right _ _)
  have p0 : 0 ≤ (1 + parabolicNorm u) ^ n₁ := by positivity
  have p1 : 0 ≤ (1 + parabolicNorm u) ^ n₂ := by positivity
  calc |f u - g u| ≤ |f u| + |g u| := abs_sub _ _
    _ ≤ B₁ * (1 + parabolicNorm u) ^ n₁ + B₂ * (1 + parabolicNorm u) ^ n₂ := add_le_add (h₁ u) (h₂ u)
    _ ≤ |B₁| * (1 + parabolicNorm u) ^ max n₁ n₂ + |B₂| * (1 + parabolicNorm u) ^ max n₁ n₂ := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self _) p0).trans
            (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self _) p1).trans
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    _ = _ := by ring

/-- `Q_t` is additive on functions of polynomial growth. -/
theorem PolyBounded.apply_add {f g : ParabolicSpace → ℝ} (hf : PolyBounded f) (hg : PolyBounded g)
    {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    parabolicSemigroup.apply t (fun w => f w + g w) y =
      parabolicSemigroup.apply t f y + parabolicSemigroup.apply t g y := by
  simp only [RegularisingSemigroup.apply, mul_add]
  exact integral_add (hf.integrable_parabolicKernel_mul ht y) (hg.integrable_parabolicKernel_mul ht y)

/-- `Q_t` commutes with finite linear combinations of functions of polynomial growth. -/
theorem PolyBounded.apply_finsetSum {J : Type*} (s : Finset J) (c : J → ℝ)
    (f : J → ParabolicSpace → ℝ) (hf : ∀ j ∈ s, PolyBounded (f j)) {t : ℝ} (ht : 0 < t)
    (y : ParabolicSpace) :
    parabolicSemigroup.apply t (fun w => ∑ j ∈ s, c j * f j w) y =
      ∑ j ∈ s, c j * parabolicSemigroup.apply t (f j) y := by
  simp only [RegularisingSemigroup.apply, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  · intro j hj
    have := ((hf j hj).integrable_parabolicKernel_mul ht y).const_mul (c j)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    have e : parabolicSemigroup.kernel t y w = parabolicKernel t (y - w) := rfl
    simp only [e]
    ring

end RegularityStructures

end

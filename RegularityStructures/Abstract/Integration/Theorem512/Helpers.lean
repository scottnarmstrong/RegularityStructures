/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute
public import RegularityStructures.Abstract.Integration.Commute.Reg

/-!
# Auxiliary lemmas for `R 𝒦_γ f = K ∗ Rf`

Closure of `PolyBounded` under finite linear combinations, `Q_t` of a difference, linearity of
`Q_t Π_x` over finite sums, the Taylor polynomial `polyEval x σ` of a coefficient family
(`polyEval_coeffPoly`, the abstract form of `polyEval_jPolyCoeff`), and `N_γ f(x)` as an embedded
polynomial (`nVec_eq_polyEmbed`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem PolyBounded.const_mul {g : ParabolicSpace → ℝ} (hg : PolyBounded g) (c : ℝ) :
    PolyBounded fun w => c * g w := by
  obtain ⟨hm, B, n, hB⟩ := hg
  refine ⟨hm.const_mul c, |c| * B, n, fun u => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB u) (abs_nonneg c)

theorem PolyBounded.add {f g : ParabolicSpace → ℝ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun w => f w + g w := by
  have h := hf.sub (hg.const_mul (-1))
  simpa [sub_eq_add_neg] using h

theorem PolyBounded.finsetSum {J : Type*} (s : Finset J) (c : J → ℝ) (f : J → ParabolicSpace → ℝ)
    (hf : ∀ j ∈ s, PolyBounded (f j)) : PolyBounded fun w => ∑ j ∈ s, c j * f j w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 0, 0, fun u => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_mul (c a)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem PolyBounded.apply_sub {f g : ParabolicSpace → ℝ} (hf : PolyBounded f) (hg : PolyBounded g)
    {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    parabolicSemigroup.apply t (fun w => f w - g w) y =
      parabolicSemigroup.apply t f y - parabolicSemigroup.apply t g y := by
  simp only [RegularisingSemigroup.apply, mul_sub]
  exact integral_sub (hf.integrable_parabolicKernel_mul ht y) (hg.integrable_parabolicKernel_mul ht y)

end RegularityStructures

end

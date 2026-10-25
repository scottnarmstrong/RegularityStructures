/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelSingularWeight
public import Phi43.BPHZ.GammaMomentWick
import Mathlib.Tactic

/-!
# Second moment of a single kernel test, uniform in the base point

For a random field `Y` with covariance `E[Y(u) Y(v)] = R(u - v)`, `|R(u - v)| ≤ A s(v - u)^(-p)`,
`2 ≤ p ≤ 7/2`, the test `z ↦ ∫ K(z - w) Y(w) dw` against the Hairer kernel `K = hairerKernelTorus N`
has second moment `≤ A C` with `C = C(N, p)` independent of `z` (`kernelTest_second_moment_le`).
The structure-group entries `v₂(x, y) = ∫ δK_{x,y} :Ψ²:` are differences of two such tests
(`v₂(x, y) = T(y) - T(x)`), so this gives a bound uniform in `x, y`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of a single kernel test**, uniform in the base point. -/
theorem kernelTest_second_moment_le (N : ℕ) {p : ℝ} (hp2 : 2 ≤ p) (hp7 : p ≤ 7 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {Y : Ω → SpaceTime → ℝ}, (Measurable fun q : Ω × SpaceTime => Y q.1 q.2) →
      (∀ u, MemLp (fun ω => Y ω u) 2 P) → ∀ {M₀ : ℝ}, (∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M₀) →
      ∀ {R : SpaceTime → ℝ}, (∀ u v, ∫ ω, Y ω u * Y ω v ∂P = R (u - v)) →
      ∀ {A : ℝ}, 0 ≤ A → (∀ u v : SpaceTime, 0 < torusParabolicSize (v - u) →
        |R (u - v)| ≤ A * torusParabolicSize (v - u) ^ (-p)) → ∀ z : SpaceTime,
      ∫ ω, (∫ w, hairerKernelTorus N (z - w) * Y ω w) ^ 2 ∂P ≤ A * C := by
  obtain ⟨BK, hBK, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_kernel_shift_sq_of_le hp2 hp7
  refine ⟨C0 * BK ^ 2, mul_nonneg hC0 (sq_nonneg _), ?_⟩
  intro Ω _ P _ Y hY hL2 M₀ hM₀ R hcov A hA hRb z
  have hm : Measurable fun w : SpaceTime => hairerKernelTorus N (z - w) :=
    (measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)
  have key := gammaMoment_second_le_of_lintBound (P := P) hY hL2 hM₀ hcov (p := p) hA hRb hm
    (integrable_hairerKernelTorus_sub N z) (M := C0 * BK ^ 2)
    (mul_nonneg hC0 (sq_nonneg _)) (h0 hK z)
  have e : ∀ ω, |∫ w, Y ω w * hairerKernelTorus N (z - w)| ^ 2 =
      (∫ w, hairerKernelTorus N (z - w) * Y ω w) ^ 2 := fun ω => by
    rw [sq_abs]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)
  simp only [e] at key
  exact key

end RegularityStructures.Phi43

end

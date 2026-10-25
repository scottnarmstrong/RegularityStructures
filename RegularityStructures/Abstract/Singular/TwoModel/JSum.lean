/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear
public import RegularityStructures.Abstract.Singular.TwoModel.IntegrationData
public import RegularityStructures.Abstract.Model

/-!
# The map `J⊕(x)` of the difference model

For the profile `h`, `J⊕(x) = jMapP M⊕ h P⊕ x` has `λ⁻¹ (jCoeffP¹ - jCoeffP²)` on the left basis
vectors and `jCoeffP²` on the right ones
(`RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear`); `J¹, J²` agree on `P.subspace`
(`jMapP_eq_of_mem_subspace`). Hence, on vectors of `V⊕` of degree `< γ`:

`J⊕(x) (a, b) = (0, λ⁻¹ (J¹(x) - J²(x)) E₀ a + J²(x) b)` (`jMapP_modelSum_parts`),
and for the lift: `J⊕(x) f⊕(x) = (0, J¹(x) f₁(x) - J²(x) f₂(x))` (`jMapP_modelSum_liftVec`).
-/

public section

open Set

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

theorem jMapP_apply (M : Model 𝒯 parabolicSemigroup) (x : ParabolicSpace) (τ : ι → ℝ) :
    jMapP M h P x τ = ∑ i, τ i • jVecP M h P x i := rfl

theorem jVecP_eq_of_mem_range (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) {j : ι} (hj : j ∈ Set.range P.emb) :
    jVecP M₁ h P x j = jVecP M₂ h P x j := by
  obtain ⟨kk, rfl⟩ := hj
  have e : M₁.regPi x (Pi.single (P.emb kk) 1) = M₂.regPi x (Pi.single (P.emb kk) 1) := by
    funext t y
    exact congrArg (fun F : parabolicSemigroup.distributions => (F : ℝ → ParabolicSpace → ℝ) t y)
      (pi_eq_of_mem_subspace h₁ h₂ x (single_emb_mem_subspace P kk))
  simp only [jVecP, jCoeffP, e]

theorem jVecP_modelSum_inr (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (j : ι)
    (x : ParabolicSpace) :
    leftPart P (jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (Sum.inr j)) = 0 ∧
      rightPart P (jVecP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x (Sum.inr j)) =
        jVecP M₂ h P x j := by
  classical
  unfold jVecP
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun kk _ => ?_
    split_ifs
    · change leftPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = 0
      rw [map_smul, leftPart_single_inr, smul_zero]
    · exact map_zero _
  · rw [map_sum]
    refine Finset.sum_congr rfl fun kk _ => ?_
    by_cases hk : polyDeg N' kk < (structSumU P).deg (Sum.inr j) + 2
    · have hk'' : polyDeg N' kk < 𝒯.deg j + 2 := hk
      simp only [hk, hk'', ite_true]
      change rightPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = _
      rw [map_smul, rightPart_single_inr, jCoeffP_modelSum_inr h₁ h₂ j x]
    · have hk'' : ¬ polyDeg N' kk < 𝒯.deg j + 2 := hk
      simp [hk, hk'']

end TwoModel

end RegularityStructures

end

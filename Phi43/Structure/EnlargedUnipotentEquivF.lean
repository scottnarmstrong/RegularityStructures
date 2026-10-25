/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedIntegrationF
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Invertibility of graded-unipotent extension maps

In the finite integration extension of Hairer [Hai14, Theorem 5.14],
triangular basis formulas first define a linear map. Graded unipotence
already implies invertibility: a maximal-degree nonzero coefficient
cannot disappear. No inverse or group law is an additional premise.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43GradedUnipotentF_injective (deg : SymbolF → ℝ)
    (L : (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ)) (hL : IsGradedUnipotent deg L) :
    Function.Injective L := by
  apply LinearMap.ker_eq_bot.1
  apply (Submodule.eq_bot_iff _).2
  intro a ha
  change L a = 0 at ha
  by_contra hn
  have hs : (Finset.univ.filter (fun i : SymbolF => a i ≠ 0)).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hn
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨i, hi, hm⟩ := Finset.exists_max_image _ deg hs
  have hai : a i ≠ 0 := (Finset.mem_filter.1 hi).2
  have hc : L a i = a i := by
    conv_lhs => rw [eq_sum_single a]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hL.apply_single_self, mul_one]
    · intro j _ hji
      by_cases haj : a j = 0
      · rw [haj, zero_mul]
      · rw [hL.apply_single_of_le (Ne.symm hji)
          (hm j (Finset.mem_filter.2 ⟨Finset.mem_univ _, haj⟩)), mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  have hz := congrFun ha i
  rw [hc] at hz
  exact hai hz

theorem phi43GradedUnipotentF_surjective (deg : SymbolF → ℝ)
    (L : (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ)) (hL : IsGradedUnipotent deg L) :
    Function.Surjective L :=
  LinearMap.injective_iff_surjective.1 (phi43GradedUnipotentF_injective deg L hL)

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The linear equivalence determined by a finite graded-unipotent map. -/
def phi43LinearEquivOfGradedUnipotentF (deg : SymbolF → ℝ)
    (L : (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ)) (hL : IsGradedUnipotent deg L) :
    (SymbolF → ℝ) ≃ₗ[ℝ] (SymbolF → ℝ) :=
  LinearEquiv.ofBijective L ⟨phi43GradedUnipotentF_injective deg L hL,
    phi43GradedUnipotentF_surjective deg L hL⟩

end RegularityStructures.Phi43

end


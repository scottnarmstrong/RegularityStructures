/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.Lemma516
public import RegularityStructures.Abstract.Integration.Commute.Integral

/-!
# Hairer's Lemma 5.16

`Model.gammaMap_integral_add_jMap`: `Γ_{xy} (I + J(y)) e_i = (I + J(x)) Γ_{xy} e_i` for a model
realising the kernel.

Source: [Hai14, Lemma 5.16].
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup}

/-- **Hairer's Lemma 5.16** [Hai14]: `Γ_{xy} (I + J(y)) e_i = (I + J(x)) Γ_{xy} e_i`. -/
theorem gammaMap_integral_add_jMap {N : ℕ} {γ CPi CGam : ℝ} {P : PolynomialSector 𝒯 N'}
    {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hreal : M.IsRealising N γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    (hN' : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {i : ι} (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace) :
    M.gammaMap x y (I (Pi.single i 1) + jMap M N P y (Pi.single i 1)) =
      I (M.gammaMap x y (Pi.single i 1)) + jMap M N P x (M.gammaMap x y (Pi.single i 1)) := by
  set τ : ι → ℝ := M.gammaMap x y (Pi.single i 1) with hτ
  have hτV : τ ∈ V := hV.invariant _ (M.gamma x y).2 _ hVi
  have hτlow : τ ∈ lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap x y).map_lowerSubspace (single_mem_lowerSubspace hi 1)
  -- the difference lies in `T̄`
  have hD : M.gammaMap x y (I (Pi.single i 1) + jMap M N P y (Pi.single i 1)) -
      (I τ + jMap M N P x τ) ∈ P.subspace := by
    have h1 : I τ - M.gammaMap x y (I (Pi.single i 1)) ∈ P.subspace :=
      hI.comm _ (M.gamma x y).2 _ hVi
    have h2 : M.gammaMap x y (jMap M N P y (Pi.single i 1)) ∈ P.subspace :=
      P.invariant _ (M.gamma x y).2 _ (jMap_mem_subspace M N P y _)
    have h3 := jMap_mem_subspace M N P x τ
    have e : M.gammaMap x y (I (Pi.single i 1) + jMap M N P y (Pi.single i 1)) -
        (I τ + jMap M N P x τ) = -(I τ - M.gammaMap x y (I (Pi.single i 1))) +
        M.gammaMap x y (jMap M N P y (Pi.single i 1)) - jMap M N P x τ := by
      rw [map_add]; abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ h1) h2) h3
  refine sub_eq_zero.1 (eq_zero_of_regPi_eq_zero hreal.poly x hD fun t ht z => ?_)
  -- the support `S` of the expansion
  set S : Finset ι := Finset.univ.filter fun j => 𝒯.deg j < γ with hS
  have hKR : ∀ j ∈ S, KRegular (fun t w => M.regPi x (Pi.single j 1) t w) x := fun j hj =>
    M.kRegular_regPi_single hdeg hPi hGam hCPi (Finset.mem_filter.1 hj).2 x
  have hτsum : τ = ∑ j ∈ S, τ j • (Pi.single j 1 : ι → ℝ) := by
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, mul_one]
    · intro j _ hj
      simp [hj.symm]
    · intro hl
      have : ¬ 𝒯.deg l < γ := fun h => hl (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      simp [hτlow l (not_lt.1 this)]
  have hvec : I τ + jMap M N P x τ =
      ∑ j ∈ S, τ j • (I (Pi.single j 1) + jMap M N P x (Pi.single j 1)) := by
    conv_lhs => rw [hτsum]
    simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib]
  rw [M.regPi_sub, M.regPi_gammaMap, hvec, regPi_finsetSum_smul,
    regPi_integral_add_jMap hreal hdeg hPi hGam hCPi hi hVi (hN' i hi) y ht z, sub_eq_zero]
  have hterm : ∀ j ∈ S, τ j * M.regPi x (I (Pi.single j 1) + jMap M N P x (Pi.single j 1)) t z =
      τ j * parabolicSemigroup.apply t (kConv N (fun t w => M.regPi x (Pi.single j 1) t w)) z := by
    intro j hj
    by_cases h0 : τ j = 0
    · rw [h0, zero_mul, zero_mul]
    · exact congrArg _ (regPi_integral_add_jMap hreal hdeg hPi hGam hCPi (Finset.mem_filter.1 hj).2
        (hVb τ hτV j h0) (hN' j (Finset.mem_filter.1 hj).2) x ht z)
  rw [Finset.sum_congr rfl hterm]
  have hfam : (fun t w => M.regPi y (Pi.single i 1) t w) =
      fun t w => ∑ j ∈ S, τ j * M.regPi x (Pi.single j 1) t w := by
    funext t' w
    rw [← M.regPi_gammaMap x y, M.regPi_eq_sum_filter hτlow]
  have hk : kConv N (fun t w => M.regPi y (Pi.single i 1) t w) =
      fun w => ∑ j ∈ S, τ j * kConv N (fun t w => M.regPi x (Pi.single j 1) t w) w := by
    rw [hfam]
    funext w
    exact kConv_finset_sum S (fun j t w => M.regPi x (Pi.single j 1) t w) τ hKR N w
  rw [hk, PolyBounded.apply_finsetSum S τ _ (fun j hj => (hKR j hj).polyBounded_kConv N) ht z]

end Model

end RegularityStructures

end

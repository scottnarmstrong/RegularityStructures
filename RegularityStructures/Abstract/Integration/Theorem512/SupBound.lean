/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Abstract.Integration.Theorem512.Setting

/-!
# Theorem 5.12: the sup bound

Bounds on the components of `𝒦_γ f(x)`: the components outside the range of `I + J(x)` vanish, the
polynomial components are bounded by `supConst`, and `𝒦_γ f(x) ∈ T_{<γ+2}`
(`Model.kGamma_mem_lowerSubspace`).

Source: [Hai14, Theorem 5.12].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The constant of the sup bound on the `X^k` component of `𝒦_γ f`:
`∑_{i : |k| < deg i + 2} jCoeffConst i k + nCoeffConst k`. -/
def supConst (𝒯 : RegularityStructure ι) (γ : ℝ) (N : ℕ) (k : Fin 4 →₀ ℕ) : ℝ :=
  (∑ i, if (multiDeg k : ℝ) < 𝒯.deg i + 2 then jCoeffConst 𝒯 γ N i k else 0) +
    nCoeffConst 𝒯 γ N k

end RegularityStructures

end

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem kGamma_apply_of_notMem_range {j : ι} (hj' : j ∉ Set.range P.emb)
    (f : ParabolicSpace → ι → ℝ) (γ : ℝ) (x : ParabolicSpace) :
    kGamma M N P I γ f x j = I (f x) j := by
  have h1 := jMap_mem_subspace M N P x (f x) j hj'
  have h2 := nVec_mem_subspace M N P γ f x j hj'
  simp only [kGamma, Pi.add_apply, h1, h2, add_zero]

theorem abs_kGamma_apply_le_of_notMem_range
    (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) {Cf : ℝ}
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) {j : ι} (hj : j ∉ Set.range P.emb)
    (x : ParabolicSpace) :
    |kGamma M N P I γ f x j| ≤ Fintype.card ι * CI * Cf := by
  rw [kGamma_apply_of_notMem_range hj, linearMap_apply_eq_sum]
  have hterm : ∀ i, |f x i * I (Pi.single i 1) j| ≤ CI * Cf := by
    intro i
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (S.entry_bound i j)
    by_cases hfi : f x i = 0
    · rw [hfi, zero_mul, abs_zero]; exact mul_nonneg hCI0 hCf
    · have hi : 𝒯.deg i < γ := by
        by_contra hge; exact hfi (hf.2.1 x i (not_lt.1 hge))
      rw [abs_mul, mul_comm]
      exact mul_le_mul (S.entry_bound i j) (hfb.1 x (mem_univ x) i hi) (abs_nonneg _) hCI0
  calc |∑ i, f x i * I (Pi.single i 1) j|
      ≤ ∑ _i : ι, CI * Cf :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem abs_fx_mul_jVec_le (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) {Cf : ℝ}
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (x : ParabolicSpace)
    (k : PolyIndex N') (i : ι) :
    |f x i * (if polyDeg N' k < 𝒯.deg i + 2 then jCoeff M N x i k.1 / multiFactorial k.1
      else 0)| ≤ Cf *
      ((if (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 then jCoeffConst 𝒯 γ N i k.1 else 0) * CPi *
        max CGam 1) := by
  have hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [S.deg_gt j hj]
  have hG : 0 ≤ max CGam 1 := le_trans zero_le_one (le_max_right _ _)
  by_cases hc : (multiDeg k.1 : ℝ) < 𝒯.deg i + 2
  · have hc' : polyDeg N' k < 𝒯.deg i + 2 := hc
    simp only [hc', hc, ↓reduceIte]
    have hJ := jCoeffConst_nonneg (N := N) (γ := γ) (i := i) (k := k.1) hdeg4 hc
    by_cases hfi : f x i = 0
    · rw [hfi, zero_mul, abs_zero]
      exact mul_nonneg hCf (mul_nonneg (mul_nonneg hJ S.piBound_nonneg) hG)
    · have hi : 𝒯.deg i < γ := by
        by_contra hge; exact hfi (hf.2.1 x i (not_lt.1 hge))
      have h1 := abs_jCoeff_le M N x i k.1 S.piBound S.gammaBound S.piBound_nonneg hi hdeg4 hc
      have hfac : (1 : ℝ) ≤ multiFactorial k.1 := by exact_mod_cast multiFactorial_pos k.1
      have h2 : |jCoeff M N x i k.1 / multiFactorial k.1| ≤
          jCoeffConst 𝒯 γ N i k.1 * CPi * max CGam 1 := by
        rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos hfac)]
        exact (div_le_self (abs_nonneg _) hfac).trans h1
      rw [abs_mul]
      exact mul_le_mul (hfb.1 x (mem_univ x) i hi) h2 (abs_nonneg _) hCf
  · have hc' : ¬ polyDeg N' k < 𝒯.deg i + 2 := hc
    simp [hc', hc]

theorem abs_kGamma_apply_emb_le (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) {Cf : ℝ}
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (hfV : ∀ x, f x ∈ V)
    (k : PolyIndex N') (hk : polyDeg N' k < γ + 2) (x : ParabolicSpace) :
    |kGamma M N P I γ f x (P.emb k)| ≤
      supConst 𝒯 γ N k.1 * CPi * max CGam 1 * Cf := by
  have hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [S.deg_gt j hj]
  have hG : 1 ≤ max CGam 1 := le_max_right _ _
  have hk' : (multiDeg k.1 : ℝ) < γ + 2 := hk
  have hI0 : I (f x) (P.emb k) = 0 := S.integration_poly _ (hfV x) k
  have e : kGamma M N P I γ f x (P.emb k) = (∑ i, f x i * (if polyDeg N' k < 𝒯.deg i + 2 then jCoeff M N x i k.1 /
        multiFactorial k.1 else 0)) +
      nCoeff M N f x k.1 / multiFactorial k.1 := by
    simp only [kGamma, Pi.add_apply, hI0, zero_add, jMap_apply_emb, nVec_apply_emb, hk, ↓reduceIte]
  rw [e]
  have hJ : |∑ i, f x i * (if polyDeg N' k < 𝒯.deg i + 2 then
      jCoeff M N x i k.1 / multiFactorial k.1 else 0)| ≤
      (∑ i, if (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 then jCoeffConst 𝒯 γ N i k.1 else 0) *
        CPi * max CGam 1 * Cf := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |f x i * (if polyDeg N' k < 𝒯.deg i + 2 then
          jCoeff M N x i k.1 / multiFactorial k.1 else 0)|
        ≤ ∑ i, Cf * ((if (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 then jCoeffConst 𝒯 γ N i k.1 else 0) *
            CPi * max CGam 1) :=
          Finset.sum_le_sum fun i _ => abs_fx_mul_jVec_le S hf hfb hCf x k i
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]; ring
  have hN1 := abs_nCoeff_le M S.pos S.piBound S.piBound_nonneg hf hfb hCf
    (fun j hj => by linarith [S.deg_gt j hj]) N x hk'
  have hfac : (1 : ℝ) ≤ multiFactorial k.1 := by exact_mod_cast multiFactorial_pos k.1
  have hN2 : |nCoeff M N f x k.1 / multiFactorial k.1| ≤
      nCoeffConst 𝒯 γ N k.1 * CPi * max CGam 1 * Cf := by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos hfac)]
    refine (div_le_self (abs_nonneg _) hfac).trans (hN1.trans ?_)
    have h0 : 0 ≤ nCoeffConst 𝒯 γ N k.1 * CPi * Cf := (abs_nonneg _).trans hN1
    calc nCoeffConst 𝒯 γ N k.1 * CPi * Cf
        ≤ (nCoeffConst 𝒯 γ N k.1 * CPi * Cf) * max CGam 1 := le_mul_of_one_le_right h0 hG
      _ = _ := by ring
  calc |(∑ i, f x i * (if polyDeg N' k < 𝒯.deg i + 2 then jCoeff M N x i k.1 /
        multiFactorial k.1 else 0)) + nCoeff M N f x k.1 / multiFactorial k.1|
      ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hJ hN2
    _ = _ := by unfold supConst; ring

theorem kGamma_mem_lowerSubspace (S : SchauderSetting M N γ P I V CPi CGam CI)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfV : ∀ x, f x ∈ V)
    (x : ParabolicSpace) : kGamma M N P I γ f x ∈ lowerSubspace 𝒯.deg (γ + 2) := by
  rw [mem_lowerSubspace]
  intro j hj
  by_cases hjr : j ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hjr
    have hdk : γ + 2 ≤ polyDeg N' k := by rw [← P.deg_emb]; exact hj
    have hk' : ¬ (multiDeg k.1 : ℝ) < γ + 2 := not_lt.2 hdk
    have hI0 : I (f x) (P.emb k) = 0 := S.integration_poly _ (hfV x) k
    have hJ : ∑ i, f x i * (if polyDeg N' k < 𝒯.deg i + 2 then
        jCoeff M N x i k.1 / multiFactorial k.1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hfi : f x i = 0
      · rw [hfi, zero_mul]
      · have hi : 𝒯.deg i < γ := by
          by_contra hge; exact hfi (hf.2.1 x i (not_lt.1 hge))
        have : ¬ polyDeg N' k < 𝒯.deg i + 2 := by linarith
        simp [this]
    have hk2 : ¬ polyDeg N' k < γ + 2 := not_lt.2 hdk
    simp only [kGamma, Pi.add_apply, hI0, jMap_apply_emb, nVec_apply_emb, hk2, ↓reduceIte, hJ,
      add_zero]
  · rw [kGamma_apply_of_notMem_range hjr, linearMap_apply_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hfi : f x i = 0
    · rw [hfi, zero_mul]
    · have hi : 𝒯.deg i < γ := by
        by_contra hge; exact hfi (hf.2.1 x i (not_lt.1 hge))
      have hIi : I (Pi.single i 1) ∈ homogeneousSubspace 𝒯.deg (𝒯.deg i + 2) :=
        S.integration.map_homogeneous _ _ (S.basis_mem _ (hfV x) i hfi)
          (single_mem_homogeneousSubspace i 1)
      have hne : ¬ 𝒯.deg j = 𝒯.deg i + 2 := by
        intro h; linarith
      rw [hIi j hne, mul_zero]

end Model

end RegularityStructures

end

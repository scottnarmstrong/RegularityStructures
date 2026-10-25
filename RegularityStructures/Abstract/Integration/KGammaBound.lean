/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.KGamma
public import RegularityStructures.Abstract.Integration.Commute
public import RegularityStructures.Abstract.Integration.Commute.Lemma516Integral

/-!
# Multilevel Schauder: the non-polynomial components of `𝒦_γ f`

By Hairer's Lemma 5.16 (`Model.gammaMap_integral_add_jMap`), extended linearly to the sector
(`Model.gammaMap_integral_add_jMap_of_mem`),

  `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x) = I(f(y) − Γ_{yx} f(x)) + (an element of T̄)`.

Hence every component outside `T̄` of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` is a component of
`I(f(y) − Γ_{yx} f(x))`, and since `I` raises degrees by exactly `2`,

  `|(𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_j| ≤ C_I |ι| C_f d(y, x)^{(γ + 2) − deg j}`

for `j ∉ T̄` (`Model.abs_kGamma_sub_gamma_nonpoly_le`): this is the non-polynomial part of the
`D^{γ+2}` bound in [Hai14, Theorem 5.12] (cf. the first step of its proof).

Source: [Hai14, Lemma 5.16 and the proof of Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

/-- Lemma 5.16 for every `a ∈ V ∩ T_{<γ}`: `Γ_{xy}(I + J(y)) a = (I + J(x)) Γ_{xy} a`. -/
theorem gammaMap_integral_add_jMap_of_mem
    (hreal : M.IsRealising N γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    (hN' : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {a : ι → ℝ} (haV : a ∈ V) (hal : a ∈ lowerSubspace 𝒯.deg γ) (x y : ParabolicSpace) :
    M.gammaMap x y (I a + jMap M N P y a) =
      I (M.gammaMap x y a) + jMap M N P x (M.gammaMap x y a) := by
  have hterm : ∀ i, M.gammaMap x y (I (a i • Pi.single i 1) + jMap M N P y (a i • Pi.single i 1))
      = I (M.gammaMap x y (a i • Pi.single i 1)) +
        jMap M N P x (M.gammaMap x y (a i • Pi.single i 1)) := by
    intro i
    by_cases hai : a i = 0
    · simp [hai]
    · have hi : 𝒯.deg i < γ := by
        by_contra hge
        exact hai (hal i (not_lt.1 hge))
      have h := M.gammaMap_integral_add_jMap hreal hI hV hVb hdeg hPi hGam hCPi hN' hi
        (hVb a haV i hai) x y
      simp only [map_smul, ← smul_add, h]
  conv_lhs => rw [eq_sum_single a]
  conv_rhs => rw [eq_sum_single a]
  simp only [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hterm i

/-- **Multilevel Schauder, non-polynomial components** ([Hai14, Theorem 5.12]): for `j ∉ T̄` with
`deg j < γ + 2`, `|(𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_j| ≤ C_I |ι| C_f d(y, x)^{γ + 2 − deg j}`, where
`C_I` bounds the matrix entries of `I`. -/
theorem abs_kGamma_sub_gamma_nonpoly_le
    (hreal : M.IsRealising N γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    (hN' : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {CI : ℝ} (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI)
    {f : ParabolicSpace → ι → ℝ} {Cf : ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (hfV : ∀ x, f x ∈ V)
    {j : ι} (hj : j ∉ Set.range P.emb) (x y : ParabolicSpace) :
    |(kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) j| ≤
      Fintype.card ι * CI * (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j)) := by
  set τ := f y - M.gammaMap y x (f x) with hτ
  have hτV : τ ∈ V :=
    Submodule.sub_mem _ (hfV y) (hV.invariant _ (M.gamma y x).2 _ (hfV x))
  have hτl : τ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (hf.2.1 y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace
      (hf.2.1 x))
  -- Lemma 5.16 for `a = f x`
  have h516 := gammaMap_integral_add_jMap_of_mem hreal hI hV hVb hdeg hPi hGam hCPi hN'
    (hfV x) (hf.2.1 x) y x
  -- the polynomial corrections do not contribute to the `j`-component
  have hpoly : ∀ v ∈ P.subspace, v j = 0 := fun v hv => hv j hj
  have hdecomp : (kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) j = I τ j := by
    have e1 : kGamma M N P I γ f y = (I (f y) + jMap M N P y (f y)) + nVec M N P γ f y := rfl
    have e2 : M.gammaMap y x (kGamma M N P I γ f x) =
        M.gammaMap y x (I (f x) + jMap M N P x (f x)) + M.gammaMap y x (nVec M N P γ f x) := by
      simp only [kGamma, map_add]
    rw [e1, e2, h516]
    have hJ1 := hpoly _ (jMap_mem_subspace M N P y (f y))
    have hJ2 := hpoly _ (jMap_mem_subspace M N P y (M.gammaMap y x (f x)))
    have hN1 := hpoly _ (nVec_mem_subspace M N P γ f y)
    have hN2 : M.gammaMap y x (nVec M N P γ f x) j = 0 :=
      hpoly _ (P.invariant _ (M.gamma y x).2 _ (nVec_mem_subspace M N P γ f x))
    simp only [Pi.add_apply, Pi.sub_apply, hτ, map_sub] at hJ1 hJ2 hN1 hN2 ⊢
    linarith
  rw [hdecomp]
  -- expand `I τ` over the basis
  have hIτ : I τ j = ∑ i, τ i * I (Pi.single i 1) j := by
    conv_lhs => rw [eq_sum_single τ]
    simp [map_sum, Finset.sum_apply]
  rw [hIτ]
  have hd0 : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg _ _
  have hterm : ∀ i, |τ i * I (Pi.single i 1) j| ≤
      CI * (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j)) := by
    intro i
    by_cases hτi : τ i = 0
    · rw [hτi, zero_mul, abs_zero]
      exact mul_nonneg ((abs_nonneg _).trans (hCI i j)) (mul_nonneg hCf (Real.rpow_nonneg hd0 _))
    · have hi : 𝒯.deg i < γ := by
        by_contra hge; exact hτi (hτl i (not_lt.1 hge))
      have hIi : I (Pi.single i 1) ∈ homogeneousSubspace 𝒯.deg (𝒯.deg i + 2) :=
        hI.map_homogeneous _ _ (hVb τ hτV i hτi) (single_mem_homogeneousSubspace i 1)
      by_cases hdj : 𝒯.deg j = 𝒯.deg i + 2
      · have hτb : |τ i| ≤ Cf * parabolicSemigroup.scaleDist y x ^ (γ - 𝒯.deg i) :=
          hfb.2 x (mem_univ x) y (mem_univ y) i hi
        have hexp : γ + 2 - 𝒯.deg j = γ - 𝒯.deg i := by rw [hdj]; ring
        rw [abs_mul, hexp, mul_comm]
        exact mul_le_mul (hCI i j) hτb (abs_nonneg _) ((abs_nonneg _).trans (hCI i j))
      · rw [hIi j hdj, mul_zero, abs_zero]
        exact mul_nonneg ((abs_nonneg _).trans (hCI i j))
          (mul_nonneg hCf (Real.rpow_nonneg hd0 _))
  calc |∑ i, τ i * I (Pi.single i 1) j|
      ≤ ∑ _i : ι, CI * (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Model

end RegularityStructures

end

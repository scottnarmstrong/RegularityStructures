/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.DecompG
public import RegularityStructures.Abstract.Singular.KGamma.Bracket
public import RegularityStructures.Abstract.Profile.Growth.Coeff
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The `X^k` component of the increment of `𝒦_γ f` as a series: pointwise summability form

The series for the `X^k` component of the increment of `𝒦_γ f` [Hai14, proof of Theorem 5.12]
under pointwise summability: the shell pairings need only be summable at the two points `y` (index
`k`) and `x` (indices `k + l`) involved.  Weighted models.

Source: [Hai14] = arXiv:1303.5113v4, proof of Theorem 5.12 / Proposition 6.16.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ CPi CGam p qG : ℝ}
  {ρP ρG : ParabolicSpace → ℝ}
  {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

/-- The `X^k` component of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` as the series `∑ₙ polyUS n`, given
summability of the shell pairings at the two points involved (weighted models). -/
theorem poly_bracketS_of_summable_growth
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N')
    (hIpoly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0)
    {f : ParabolicSpace → ι → ℝ} (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) (k : PolyIndex N')
    (hSy : Summable (M.singShellPairing h f y k.1))
    (hSe : ∀ l ∈ taylorIdx (γ + 2 - multiDeg k.1), Summable fun n =>
      M.singShellPairing h f x (k.1 + l) n)
    (hk : polyDeg N' k < γ + 2) :
    Summable (polyUS M h γ f x y k.1) ∧
    (kGammaS M h P I γ f y - M.gammaMap y x (kGammaS M h P I γ f x)) (P.emb k) *
        multiFactorial k.1 = ∑' n, polyUS M h γ f x y k.1 n := by
  classical
  have hdeg4 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j :=
    fun j hjV hj => by linarith [hdeg j hjV hj]
  have hk' : (multiDeg k.1 : ℝ) < γ + 2 := hk
  have hkf : (multiFactorial k.1 : ℝ) ≠ 0 := by exact_mod_cast (multiFactorial_pos k.1).ne'
  set τ := f y - M.gammaMap y x (f x) with hτ
  have hτV : τ ∈ V :=
    Submodule.sub_mem _ (hfV y) (hV.invariant _ (M.gamma y x).2 _ (hfV x))
  have hτl : τ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (hf y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace (hf x))
  -- summability of the three kinds of series
  have hSa : ∀ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
      Summable fun n => τ i * parabolicSemigroup.pairing
        (fun t z => M.regPi y (Pi.single i 1) t z)
        (fun w => lineIter (multiDirs k.1) (scaledShell h n) (y - w)) := by
    intro i hi
    by_cases hτi : τ i = 0
    · simp [hτi]
    · have hlt : 𝒯.deg i < γ := by
        by_contra hge; exact hτi (hτl i (not_lt.1 hge))
      exact (summable_jCoeff_terms_growthP M hh G y i k.1 hV hVb (hVb τ hτV i hτi) hlt
        hdeg4 (Finset.mem_filter.1 hi).2).mul_left _
  have hSb : Summable (M.singShellPairing h f y k.1) := hSy
  have hSe' : ∀ l ∈ taylorIdx (γ + 2 - multiDeg k.1), Summable fun n =>
      coeffT (parabolicCoords (y - x)) l * M.singShellPairing h f x (k.1 + l) n :=
    fun l hl => (hSe l hl).mul_left _
  have hsum : Summable (polyUS M h γ f x y k.1) :=
    (((summable_sum hSa).add hSb).sub (summable_sum hSe'))
  refine ⟨hsum, ?_⟩
  rw [kGammaS_sub_gamma_apply_emb_growth hh hreal hI hV hVb hdeg G hN' hIpoly hf hfV x y k]
  have hΓ := gammaMap_nVecS_apply_emb (h := h) hreal.poly γ f x y k hNγ
  have hAs := summable_sum hSa
  have hEs := summable_sum hSe'
  have e1 : ∑' n, polyUS M h γ f x y k.1 n =
      (∑' n, ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
        τ i * parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
          (fun w => lineIter (multiDirs k.1) (scaledShell h n) (y - w))) +
      (∑' n, M.singShellPairing h f y k.1 n) -
      ∑' n, ∑ l ∈ taylorIdx (γ + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
        M.singShellPairing h f x (k.1 + l) n := by
    unfold polyUS
    rw [Summable.tsum_sub (hAs.add hSb) hEs, Summable.tsum_add hAs hSb]
  rw [e1, Summable.tsum_finsetSum hSa, Summable.tsum_finsetSum hSe']
  have e2 : ∀ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
      ∑' n, τ i * parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
        (fun w => lineIter (multiDirs k.1) (scaledShell h n) (y - w)) =
          τ i * jCoeffP M h y i k.1 := fun i _ => by
    rw [tsum_mul_left]; rfl
  have e3 : ∀ l ∈ taylorIdx (γ + 2 - multiDeg k.1), ∑' n, coeffT (parabolicCoords (y - x)) l *
      M.singShellPairing h f x (k.1 + l) n =
        coeffT (parabolicCoords (y - x)) l * M.nCoeffS h f x (k.1 + l) := fun l _ => by
    rw [tsum_mul_left]; rfl
  have hite : (if polyDeg N' k < γ + 2 then M.nCoeffS h f y k.1 / multiFactorial k.1 else 0) =
      M.nCoeffS h f y k.1 / multiFactorial k.1 := by simp [hk]
  rw [Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, ← hΓ, hite]
  have e4 : (∑ i, τ i * (if polyDeg N' k < 𝒯.deg i + 2 then
        jCoeffP M h y i k.1 / multiFactorial k.1 else 0)) * multiFactorial k.1 =
      ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
        τ i * jCoeffP M h y i k.1 := by
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : polyDeg N' k < 𝒯.deg i + 2
    · have hp' : (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 := hp
      simp only [hp, hp', ite_true]
      field_simp
    · have hp' : ¬ (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 := hp
      simp [hp, hp']
  have e5 : M.nCoeffS h f y k.1 / multiFactorial k.1 * multiFactorial k.1 =
      M.nCoeffS h f y k.1 := by
    field_simp
  rw [sub_mul, add_mul, e4, e5]
  rfl

end Model

end RegularityStructures

end

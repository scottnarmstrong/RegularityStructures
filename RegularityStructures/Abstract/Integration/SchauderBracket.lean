/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderDecomp
public import RegularityStructures.Abstract.Integration.KGamma

/-!
# Multilevel Schauder: the series for the `X^k` component

`polyU M N γ f x y k n` is the `n`-th term of the series, `k! ·` the `X^k`-component of
`𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` (`poly_bracket`):

  `∑_{i : |k| < deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩ + ⟨Rf − Π_y f(y), D^k K_n(y−·)⟩
     − ∑_{|l| < γ+2−|k|} (y−x)^l/l! ⟨Rf − Π_x f(x), D^{k+l} K_n(x−·)⟩`,  `τ = f(y) − Γ_{yx} f(x)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

open Classical in
/-- The `n`-th term of the series for `k! (𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_{X^k}`. -/
def polyU (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ) (f : ParabolicSpace → ι → ℝ)
    (x y : ParabolicSpace) (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
      (f y - M.gammaMap y x (f x)) i *
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n) +
    derivShellPairing (M.reconstructSubAt f y) (annKernel0 N) k y n -
    ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
      derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) (k + l) x n

end RegularityStructures

end

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam Cf : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem poly_bracket
    (hreal : M.IsRealising N γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hγ : 0 < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    (hN' : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N')
    (hIpoly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0)
    (hM : M.IsPolyCompatible P)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) (k : PolyIndex N') (hk : polyDeg N' k < γ + 2) :
    Summable (polyU M N γ f x y k.1) ∧
    (kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) (P.emb k) *
        multiFactorial k.1 = ∑' n, polyU M N γ f x y k.1 n := by
  classical
  have hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [hdeg j hj]
  have hk' : (multiDeg k.1 : ℝ) < γ + 2 := hk
  have hkf : (multiFactorial k.1 : ℝ) ≠ 0 := by exact_mod_cast (multiFactorial_pos k.1).ne'
  set τ := f y - M.gammaMap y x (f x) with hτ
  have hτl : τ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (hf.2.1 y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace
      (hf.2.1 x))
  -- summability of the three kinds of series
  have hSa : ∀ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
      Summable fun n => τ i * derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z)
        (annKernel0 N) k.1 y n := by
    intro i hi
    by_cases hτi : τ i = 0
    · simp [hτi]
    · have hlt : 𝒯.deg i < γ := by
        by_contra hge; exact hτi (hτl i (not_lt.1 hge))
      exact (summable_jCoeff_terms M N y i k.1 hPi hGam hCPi hlt hdeg4
        (Finset.mem_filter.1 hi).2).mul_left _
  have hSb : Summable (derivShellPairing (M.reconstructSubAt f y) (annKernel0 N) k.1 y) :=
    summable_nCoeff_terms M hγ hPi hCPi hf hfb hCf hdeg4 N y hk'
  have hSe : ∀ l ∈ taylorIdx (γ + 2 - multiDeg k.1), Summable fun n =>
      coeffT (parabolicCoords (y - x)) l *
        derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) (k.1 + l) x n := by
    intro l hl
    have hl' := (mem_taylorIdx_iff _).1 hl
    have hadd : multiDeg (k.1 + l) = multiDeg k.1 + multiDeg l := map_add _ _ _
    refine (summable_nCoeff_terms M hγ hPi hCPi hf hfb hCf hdeg4 N x (k := k.1 + l) ?_).mul_left _
    rw [hadd]; push_cast; linarith
  have hsum : Summable (polyU M N γ f x y k.1) :=
    (((summable_sum hSa).add hSb).sub (summable_sum hSe))
  refine ⟨hsum, ?_⟩
  rw [kGamma_sub_gamma_apply_emb hreal hI hV hVb hdeg hPi hGam hCPi hN' hIpoly hf hfV x y k]
  have hΓ := gammaMap_nVec_apply_emb hM N γ f x y k hNγ
  have hAs := summable_sum hSa
  have hEs := summable_sum hSe
  have e1 : ∑' n, polyU M N γ f x y k.1 n =
      (∑' n, ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
        τ i * derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k.1 y n) +
      (∑' n, derivShellPairing (M.reconstructSubAt f y) (annKernel0 N) k.1 y n) -
      ∑' n, ∑ l ∈ taylorIdx (γ + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
        derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) (k.1 + l) x n := by
    unfold polyU
    rw [Summable.tsum_sub (hAs.add hSb) hEs, Summable.tsum_add hAs hSb]
  rw [e1, Summable.tsum_finsetSum hSa, Summable.tsum_finsetSum hSe]
  have e2 : ∀ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
      ∑' n, τ i * derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N)
        k.1 y n = τ i * jCoeff M N y i k.1 := fun i _ => by
    rw [tsum_mul_left]; rfl
  have e3 : ∀ l ∈ taylorIdx (γ + 2 - multiDeg k.1), ∑' n, coeffT (parabolicCoords (y - x)) l *
      derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) (k.1 + l) x n =
        coeffT (parabolicCoords (y - x)) l * nCoeff M N f x (k.1 + l) := fun l _ => by
    rw [tsum_mul_left]; rfl
  have hite : (if polyDeg N' k < γ + 2 then nCoeff M N f y k.1 / multiFactorial k.1 else 0) =
      nCoeff M N f y k.1 / multiFactorial k.1 := by simp [hk]
  rw [Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, ← hΓ, hite]
  have e4 : (∑ i, τ i * (if polyDeg N' k < 𝒯.deg i + 2 then
        jCoeff M N y i k.1 / multiFactorial k.1 else 0)) * multiFactorial k.1 =
      ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k.1 : ℝ) < 𝒯.deg i + 2),
        τ i * jCoeff M N y i k.1 := by
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : polyDeg N' k < 𝒯.deg i + 2
    · have h' : (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 := h
      simp only [h, h', ite_true]
      field_simp
    · have h' : ¬ (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 := h
      simp [h, h']
  have e5 : nCoeff M N f y k.1 / multiFactorial k.1 * multiFactorial k.1 = nCoeff M N f y k.1 := by
    field_simp
  rw [sub_mul, add_mul, e4, e5]
  rfl

end Model

end RegularityStructures

end

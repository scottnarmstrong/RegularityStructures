/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupTerm
public import RegularityStructures.Abstract.Singular.KGamma.Emb
public import RegularityStructures.Abstract.Profile.Growth.Coeff
public import RegularityStructures.Abstract.Integration.SchauderComp
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# The `X^k` coordinate of `𝒦_γ f` for the lattice reconstruction, weighted models

Weighted (`_growth`) version: the global model bounds are replaced by a
`Model.GrowthModel`; only qualitative convergence of the `J`-coefficients (Lemma 5.16) is used.

For `kk : PolyIndex N'` with `|kk| < γ + 2` and `I (f x)_{X^k} = 0`,
`(kGammaS M h P I γ f x)_{X^k} = (∑_n shellTerm M h f x k n) / k!`
(`kGammaS_apply_emb_growth`): the `J`-part contributes `f(x)_i ∑_n ⟨Π_x e_i, D^k K_n(x − ·)⟩` for the `i`
with `|k| < deg i + 2`, which combines term by term with `nCoeffS`.
-/

public section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {N : ℕ} {h : ParabolicSpace → ℝ}

/-- The `J`-coefficient series converges for a weighted model (profile `h`, no sector). -/
theorem summable_jCoeffTermsP_of_growth (M : Model 𝒯 parabolicSemigroup) (hh : ShellProfile h N)
    (x : ParabolicSpace) (i : ι) (k : Fin 4 →₀ ℕ) {γ CPi CGam p qG : ℝ}
    {ρP ρG : ParabolicSpace → ℝ} (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hi : 𝒯.deg i < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) :
    Summable fun n : ℕ => parabolicSemigroup.pairing
      (fun t y => M.regPi x (Pi.single i 1) t y)
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) :=
  summable_jCoeff_terms_growthP M hh G x i k (V := (⊤ : Submodule ℝ (ι → ℝ)))
    ⟨fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩ (fun _ _ _ _ => trivial) trivial hi
    (fun j _ hj => hdeg j hj) hk

theorem summable_singShellPairing_of_shellTerm_growth (M : Model 𝒯 parabolicSemigroup)
    (hh : ShellProfile h N) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {f : ParabolicSpace → ι → ℝ} {x : ParabolicSpace} (hfx : f x ∈ lowerSubspace 𝒯.deg γ)
    (k : Fin 4 →₀ ℕ) (hsum : Summable (fun n => M.shellTerm h f x k n)) :
    Summable (fun n => M.singShellPairing h f x k n) := by
  classical
  set Pp : Finset ι := Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2) with hPp
  set b : ι → ℕ → ℝ := fun i n => f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
    (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) with hb
  have hbsum : ∀ i ∈ Pp, Summable (b i) := by
    intro i hi
    by_cases hfi : f x i = 0
    · have : b i = fun _ => 0 := by funext n; simp [hb, hfi]
      rw [this]; exact summable_zero
    · have hi' : 𝒯.deg i < γ := by
        by_contra hge
        exact hfi ((mem_lowerSubspace).1 hfx i (not_lt.1 hge))
      exact (summable_jCoeffTermsP_of_growth M hh x i k G hi' hdeg
        (Finset.mem_filter.1 hi).2).mul_left (f x i)
  have : (fun n => M.singShellPairing h f x k n) =
      fun n => M.shellTerm h f x k n - ∑ i ∈ Pp, b i n := by
    funext n; simp [shellTerm, hb, hPp]
  rw [this]
  exact hsum.sub (summable_sum hbsum)

theorem kGammaS_apply_emb_growth (M : Model 𝒯 parabolicSemigroup) (hh : ShellProfile h N)
    {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {f : ParabolicSpace → ι → ℝ}
    {x : ParabolicSpace} (hfx : f x ∈ lowerSubspace 𝒯.deg γ) (kk : PolyIndex N')
    (hI0 : I (f x) (P.emb kk) = 0) (hkk : polyDeg N' kk < γ + 2)
    (hsum : Summable (fun n => M.shellTerm h f x kk.1 n)) :
    M.kGammaS h P I γ f x (P.emb kk) =
      (∑' n, M.shellTerm h f x kk.1 n) / multiFactorial kk.1 := by
  classical
  set Pp : Finset ι := Finset.univ.filter (fun i => (multiDeg kk.1 : ℝ) < 𝒯.deg i + 2) with hPp
  set b : ι → ℕ → ℝ := fun i n => f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
    (fun y => lineIter (multiDirs kk.1) (scaledShell h n) (x - y)) with hb
  have hbsum : ∀ i ∈ Pp, Summable (b i) := by
    intro i hi
    by_cases hfi : f x i = 0
    · have : b i = fun _ => 0 := by funext n; simp [hb, hfi]
      rw [this]; exact summable_zero
    · have hi' : 𝒯.deg i < γ := by
        by_contra hge
        exact hfi ((mem_lowerSubspace).1 hfx i (not_lt.1 hge))
      exact (summable_jCoeffTermsP_of_growth M hh x i kk.1 G hi' hdeg
        (Finset.mem_filter.1 hi).2).mul_left (f x i)
  have hsing := summable_singShellPairing_of_shellTerm_growth M hh G hdeg hfx kk.1 hsum
  have htsum : ∑' n, M.shellTerm h f x kk.1 n =
      M.nCoeffS h f x kk.1 + ∑ i ∈ Pp, f x i * jCoeffP M h x i kk.1 := by
    have e1 : ∀ n, M.shellTerm h f x kk.1 n = M.singShellPairing h f x kk.1 n + ∑ i ∈ Pp, b i n :=
      fun n => rfl
    simp only [e1]
    rw [hsing.tsum_add (summable_sum hbsum), Summable.tsum_finsetSum hbsum]
    unfold nCoeffS
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hb]
    rw [tsum_mul_left]
    rfl
  have hpd : polyDeg N' kk = (multiDeg kk.1 : ℝ) := rfl
  have hJ : ∑ i, f x i * (if polyDeg N' kk < 𝒯.deg i + 2 then
      jCoeffP M h x i kk.1 / multiFactorial kk.1 else 0) =
      (∑ i ∈ Pp, f x i * jCoeffP M h x i kk.1) / multiFactorial kk.1 := by
    rw [Finset.sum_div, hPp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hpd]
    split_ifs <;> simp [mul_div_assoc]
  unfold kGammaS
  simp only [Pi.add_apply, hI0, zero_add, jMapP_apply_emb, nVecS_apply_emb, hkk, ite_true, hJ, htsum]
  ring

end Model

end RegularityStructures

end

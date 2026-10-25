/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Abstract.Integration.Theorem512.SupBound

/-!
# The `D^{γ+2}` bound for `𝒦_γ f`

`Model.exists_modelledBoundOn_kGamma`: there is a constant `c`, depending only on `𝒯, γ, N`,
such that for every model satisfying a `SchauderSetting` and every `f ∈ D^γ` with values in `V`
and `D^γ`-bound `C_f`, `𝒦_γ f` satisfies the bounds of `D^{γ+2}` with constant
`c · max 1 C_I · max 1 C_Π · max C_Γ 1 · C_f` (`ModelledBoundOn (γ + 2)`): the sup bounds are those
of `Sup`, the increment bounds `abs_kGamma_sub_gamma_nonpoly_le` and
`exists_abs_kGamma_sub_gamma_poly_le`.

Source: [Hai14, Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem mul_five_le {a c p q G Cf m : ℝ} (hac : a ≤ c) (hc : 0 ≤ c) (hp : p ≤ q) (hp0 : 0 ≤ p)
    (hG : 1 ≤ G) (hCf : 0 ≤ Cf) (hm : 1 ≤ m) : a * p * G * Cf ≤ c * m * q * G * Cf := by
  have hq : 0 ≤ q := hp0.trans hp
  have h1 : a * p ≤ c * q := mul_le_mul hac hp hp0 hc
  have h2 : c * q ≤ c * m * q := by
    have : 0 ≤ c * q * (m - 1) := mul_nonneg (mul_nonneg hc hq) (by linarith)
    nlinarith
  have hG0 : 0 ≤ G := by linarith
  calc a * p * G * Cf ≤ (c * m * q) * G * Cf := 
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h1.trans h2) hG0) hCf
    _ = _ := rfl

theorem le_scaled {a c m q G Cf : ℝ} (hab : a ≤ c * m) (hc : 0 ≤ c) (hm : 1 ≤ m) (hq : 1 ≤ q)
    (hG : 1 ≤ G) (hCf : 0 ≤ Cf) : a * Cf ≤ c * m * q * G * Cf := by
  have h : c * m ≤ c * m * q * G := by
    have h0 : 0 ≤ c * m := mul_nonneg hc (by linarith)
    have : 1 ≤ q * G := one_le_mul_of_one_le_of_one_le hq hG
    nlinarith
  exact mul_le_mul_of_nonneg_right (hab.trans h) hCf

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

/-- **`D^{γ+2}` bound for `𝒦_γ f`** [Hai14, Theorem 5.12]: the bounds of `D^{γ+2}` with constant
`c · max 1 C_I · max 1 C_Π · max C_Γ 1 · C_f`. -/
theorem exists_modelledBoundOn_kGamma {γ : ℝ} (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (N : ℕ) (P : PolynomialSector 𝒯 N') (hNN : N' ≤ N)
    (hn : SchauderNonIntegral 𝒯 γ N' P) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam CI Cf : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)),
      SchauderSetting M N γ P I V CPi CGam CI → ∀ {f : ParabolicSpace → ι → ℝ},
      f ∈ M.modelledDistributions γ → M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf →
      (∀ x, f x ∈ V) →
      M.ModelledBoundOn (γ + 2) (c * max 1 CI * max 1 CPi * max CGam 1 * Cf) univ
        (fun x => kGamma M N P I γ f x) := by
  classical
  have hex : ∀ k : PolyIndex N', polyDeg N' k < γ + 2 → _ := fun k hk =>
    exists_abs_kGamma_sub_gamma_poly_le hγ hdeg N P hNN k hk (hn.nonint₁ k hk) (hn.nonint₂ k hk)
  set ck : PolyIndex N' → ℝ := fun k => if hk : polyDeg N' k < γ + 2 then
    Classical.choose (hex k hk) else 0 with hck
  have hck0 : ∀ k, 0 ≤ ck k := fun k => by
    by_cases hk : polyDeg N' k < γ + 2
    · simp only [hck, hk, ↓reduceDIte]; exact (Classical.choose_spec (hex k hk)).1
    · simp only [hck, hk, ↓reduceDIte]; exact le_rfl
  have hS0 : 0 ≤ ∑ k, ck k := Finset.sum_nonneg fun k _ => hck0 k
  have hS1 : 0 ≤ ∑ k : PolyIndex N', |supConst 𝒯 γ N k.1| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hcard0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  refine ⟨Fintype.card ι + ∑ k, ck k + ∑ k : PolyIndex N', |supConst 𝒯 γ N k.1|,
    by linarith, ?_⟩
  intro M CPi CGam CI Cf I V S f hf hfb hCf hfV
  set c : ℝ := Fintype.card ι + ∑ k, ck k + ∑ k : PolyIndex N', |supConst 𝒯 γ N k.1| with hc
  have hc0 : 0 ≤ c := by linarith
  have hm : 1 ≤ max 1 CI := le_max_left _ _
  have hq : 1 ≤ max 1 CPi := le_max_left _ _
  have hG : 1 ≤ max CGam 1 := le_max_right _ _
  have hpq : CPi ≤ max 1 CPi := le_max_right _ _
  refine ⟨?_, ?_⟩
  · intro x _ j hj
    by_cases hjr : j ∈ Set.range P.emb
    · obtain ⟨k, rfl⟩ := hjr
      have hk : polyDeg N' k < γ + 2 := by rw [← P.deg_emb]; exact hj
      refine (abs_kGamma_apply_emb_le S hf hfb hCf hfV k hk x).trans ?_
      have hsc : supConst 𝒯 γ N k.1 ≤ c := by
        have h1 : |supConst 𝒯 γ N k.1| ≤ ∑ k' : PolyIndex N', |supConst 𝒯 γ N k'.1| :=
          Finset.single_le_sum (f := fun k' : PolyIndex N' => |supConst 𝒯 γ N k'.1|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
        linarith [le_abs_self (supConst 𝒯 γ N k.1)]
      exact mul_five_le hsc hc0 hpq S.piBound_nonneg hG hCf hm
    · refine (abs_kGamma_apply_le_of_notMem_range S hf hfb hCf hjr x).trans ?_
      refine le_scaled ?_ hc0 hm hq hG hCf
      have hCI : CI ≤ max 1 CI := le_max_right _ _
      have hcc : (Fintype.card ι : ℝ) ≤ c := by linarith
      calc (Fintype.card ι : ℝ) * CI ≤ Fintype.card ι * max 1 CI :=
            mul_le_mul_of_nonneg_left hCI hcard0
        _ ≤ c * max 1 CI := mul_le_mul_of_nonneg_right hcc (by linarith)
  · intro x _ y _ j hj
    by_cases hjr : j ∈ Set.range P.emb
    · obtain ⟨k, rfl⟩ := hjr
      have hk : polyDeg N' k < γ + 2 := by rw [← P.deg_emb]; exact hj
      have hspec := Classical.choose_spec (hex k hk)
      have h := hspec.2 M I V S.realising S.integration S.sector S.basis_mem S.piBound
        S.gammaBound S.piBound_nonneg S.poly_large S.poly_large' S.integration_poly
        S.realising.poly hf hfb hCf hfV x y
      have hckk : ck k = Classical.choose (hex k hk) := by simp only [hck, hk, ↓reduceDIte]
      rw [← hckk] at h
      have hdeg' : γ + 2 - 𝒯.deg (P.emb k) = γ + 2 - (multiDeg k.1 : ℝ) := by
        rw [P.deg_emb]; rfl
      rw [hdeg']
      have hsc : ck k ≤ c := by
        have h1 : ck k ≤ ∑ k', ck k' :=
          Finset.single_le_sum (f := ck) (fun k _ => hck0 k) (Finset.mem_univ k)
        linarith
      have hcoef : ck k * CPi * max CGam 1 * Cf ≤ c * max 1 CI * max 1 CPi * max CGam 1 * Cf :=
        mul_five_le hsc hc0 hpq S.piBound_nonneg hG hCf hm
      have hrp : 0 ≤ parabolicNorm (y - x) ^ (γ + 2 - (multiDeg k.1 : ℝ)) :=
        Real.rpow_nonneg (parabolicNorm_nonneg _) _
      have h' : |(kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) (P.emb k)| ≤
          (ck k * CPi * max CGam 1 * Cf) *
            parabolicNorm (y - x) ^ (γ + 2 - (multiDeg k.1 : ℝ)) := by
        refine h.trans (le_of_eq ?_); ring
      exact h'.trans (mul_le_mul_of_nonneg_right hcoef hrp)
    · have h := abs_kGamma_sub_gamma_nonpoly_le S.realising S.integration S.sector S.basis_mem
        S.deg_gt S.piBound S.gammaBound S.piBound_nonneg S.poly_large S.entry_bound hf hfb hCf hfV
        hjr x y
      refine h.trans ?_
      have hrp : 0 ≤ parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) :=
        Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _
      have hCI : CI ≤ max 1 CI := le_max_right _ _
      have hcc : (Fintype.card ι : ℝ) ≤ c := by linarith
      have h1 : (Fintype.card ι : ℝ) * CI ≤ c * max 1 CI :=
        calc (Fintype.card ι : ℝ) * CI ≤ Fintype.card ι * max 1 CI :=
              mul_le_mul_of_nonneg_left hCI hcard0
          _ ≤ c * max 1 CI := mul_le_mul_of_nonneg_right hcc (by linarith)
      have h2 := le_scaled h1 hc0 hm hq hG hCf
      calc (Fintype.card ι : ℝ) * CI * (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j))
          = (Fintype.card ι * CI * Cf) * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hrp

end Model

end RegularityStructures

end

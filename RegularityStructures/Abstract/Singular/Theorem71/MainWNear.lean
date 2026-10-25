/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Theorem71.IncrNonpolyWNear
public import RegularityStructures.Abstract.Singular.Theorem71.IncrWNear
public import RegularityStructures.Abstract.Singular.Theorem71.SupWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.KGamma.SupMain
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Abstract.Singular.Remainder.GammaG
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# The bound on `𝒦_γ f + R_γ f` on a time slab, near-pair `Γ`-bounds

Time slab form of [Hai14, Theorem 7.1] (with Prop. 6.16): in the window layer setting
`LayerSettingWNear`, `𝒦_γ f + R_γ f` (`kGammaRemG`) takes values below degree `γ + 2`, is singular
modelled of order `(γ + 2, α ∧ η + 2)` on the slab, and its components satisfy the weighted sup
bound `C w_x^{α∧η+2−deg i}`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem consts_le_W {K₀ cI G Cs C : ℝ} (hK₀ : 0 ≤ K₀) (hcI : 0 ≤ cI) (hG : 1 ≤ G)
    (hC1 : 1 ≤ C) (hCs : Cs ≤ C) :
    Cs * K₀ ≤ C * ((K₀ + cI) * G) ∧ cI ≤ C * ((K₀ + cI) * G) := by
  have hs : 0 ≤ K₀ + cI := add_nonneg hK₀ hcI
  have h1 : K₀ + cI ≤ (K₀ + cI) * G := le_mul_of_one_le_right hs hG
  have h2 : (K₀ + cI) * G ≤ C * ((K₀ + cI) * G) :=
    le_mul_of_one_le_left (mul_nonneg hs (zero_le_one.trans hG)) hC1
  exact ⟨by nlinarith, by linarith⟩

namespace Model

/-- **Hairer's Theorem 7.1** (with Prop. 6.16), time slab form. -/
theorem exists_singularBoundOn_kGammaRemG_win_near {𝒯 : RegularityStructure ι} (γ η α : ℝ) (N : ℕ)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N)
    (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hαγ : α ≤ γ) (hαη : -2 < min α η)
    (hN : N' ≤ N) (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hVα : ∀ i, (Pi.single i 1 : ι → ℝ) ∈ V → α ≤ 𝒯.deg i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam CI CΓ2 : ℝ) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsRealisingP h γ P I V → IsAbstractIntegration P V I 2 →
      (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) → (∀ z, f z ∈ V) →
      M.GammaNearOn (γ + 2) CΓ2 (timeSlab T) →
      (∀ x ∈ timeSlab T, M.kGammaRemG h r P I γ f x ∈ lowerSubspace 𝒯.deg (γ + 2)) ∧
      M.SingularBoundOn timeZeroDist (γ + 2) (min α η + 2)
        (C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf) (timeSlab T)
        (M.kGammaRemG h r P I γ f) ∧
      (∀ x ∈ timeSlab T, ∀ i, 𝒯.deg i < γ + 2 →
        |M.kGammaRemG h r P I γ f x i| ≤
          C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf *
            singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg i)) := by
  classical
  have hpk : ∀ kk : PolyIndex N', polyDeg N' kk < γ + 2 → (multiDeg kk.1 : ℝ) < γ + 2 :=
    fun kk hk => hk
  have Hs : ∀ kk : PolyIndex N', polyDeg N' kk < γ + 2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯
      parabolicSemigroup) (f : ParabolicSpace → ι → ℝ) (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)),
        (∀ z, f z ∈ V) → (∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0) →
      ∀ {x : ParabolicSpace}, x ∈ timeSlab T →
      |(M.kGammaRemG h r P I γ f x) (P.emb kk)| ≤
        C * (max 1 CGam * CPi) * Cf *
          singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk) := fun kk hk =>
    exists_abs_kGammaRemG_apply_emb_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη hp P hN kk hk
      (hni kk.1 (hpk kk hk))
  have Hi : ∀ kk : PolyIndex N', polyDeg N' kk < γ + 2 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam CI CΓ2 : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.IsRealisingP h γ P I V →
        IsAbstractIntegration P V I 2 → (∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0) →
        (∀ i j, |I (Pi.single i 1) j| ≤ CI) → (∀ z, f z ∈ V) →
        M.GammaNearOn (γ + 2) CΓ2 (timeSlab T) →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab T → y ∈ timeSlab T →
        parabolicNorm (y - x) ≤
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) →
      |(M.kGammaRemG h r P I γ f y -
          M.gammaMap y x (M.kGammaRemG h r P I γ f x))
          (P.emb kk)| ≤
        C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf *
          (parabolicNorm (y - x) ^ (γ + 2 - polyDeg N' kk) *
            min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
              (min α η - γ)) := fun kk hk =>
    exists_abs_kGammaRemG_sub_gamma_apply_emb_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη hp hN P hNγ hnat hni
      hV hVb hVα kk hk
  choose! Cs hCs0 hCs using Hs
  choose! Ci hCi0 hCi using Hi
  set C : ℝ := 1 + ∑ kk : PolyIndex N', (|Cs kk| + |Ci kk|) with hC
  have hsum : 0 ≤ ∑ kk : PolyIndex N', (|Cs kk| + |Ci kk|) :=
    Finset.sum_nonneg fun kk _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hle : ∀ kk : PolyIndex N', |Cs kk| + |Ci kk| ≤ C := fun kk => by
    rw [hC]
    have := Finset.single_le_sum (f := fun k : PolyIndex N' => |Cs k| + |Ci k|)
      (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ kk)
    linarith
  have hCsC : ∀ kk, Cs kk ≤ C := fun kk => by
    linarith [le_abs_self (Cs kk), abs_nonneg (Ci kk), hle kk]
  have hCiC : ∀ kk, Ci kk ≤ C := fun kk => by
    linarith [le_abs_self (Ci kk), abs_nonneg (Cs kk), hle kk]
  refine ⟨C, zero_le_one.trans hC1, fun M f T Cf CPi CGam CI CΓ2 I S hreal hInt hIp hCI hfV
    hΓ2 => ?_⟩
  have hdeg2 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j :=
    fun j hjV _ => by linarith [hVα j hjV, min_le_left α η]
  have hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N' :=
    fun j _ hj k hkj => hNγ k (by linarith)
  have hK₀0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hG : (1 : ℝ) ≤ max 1 CΓ2 := le_max_left _ _
  have hCf := S.hCf
  -- pointwise bound
  have hpt : ∀ x ∈ timeSlab T, ∀ i, 𝒯.deg i < γ + 2 →
      |M.kGammaRemG h r P I γ f x i| ≤
        C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf *
          singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg i) := by
    intro x hx i hi
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i i)
    have hcI : 0 ≤ (Fintype.card ι : ℝ) * CI := mul_nonneg (Nat.cast_nonneg _) hCI0
    have hw0 : 0 ≤ singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg i) :=
      Real.rpow_nonneg (KGammaSup.weight_pos hx).le _
    by_cases hjr : i ∈ Set.range P.emb
    · obtain ⟨kk, rfl⟩ := hjr
      have hdk : 𝒯.deg (P.emb kk) = polyDeg N' kk := P.deg_emb kk
      rw [hdk] at hi hw0 ⊢
      have hb := hCs kk hi M f T Cf CPi CGam S hreal.poly I V hfV hIp hx
      refine hb.trans ?_
      have := (consts_le_W hK₀0 hcI hG hC1 (hCsC kk)).1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hCf) hw0
    · have hb := abs_kGammaRemG_apply_le_of_notMem_range_win_near S h r P I V hVb hInt hfV hCI hx hjr
      refine hb.trans ?_
      have := (consts_le_W (Cs := 0) hK₀0 hcI hG hC1 (zero_le_one.trans hC1)).2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hCf) hw0
  refine ⟨fun x hx => ?_, ⟨?_, ?_⟩, hpt⟩
  · exact Submodule.add_mem _ (kGammaS_mem_lowerSubspace h P I V hVb hInt hIp
      (hfV x) (S.hfT x)) (M.remVecG_mem_lowerSubspace r P γ f x)
  · intro x hx _ i hi
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i i)
    have hK₁0 : 0 ≤ C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf :=
      mul_nonneg (mul_nonneg (zero_le_one.trans hC1) (mul_nonneg (add_nonneg hK₀0
        (mul_nonneg (Nat.cast_nonneg _) hCI0)) (zero_le_one.trans hG))) hCf
    have hw := KGammaSup.weight_pos hx
    have hw1 := singularWeight_le_one timeZeroDist x
    refine (hpt x hx i hi).trans (mul_le_mul_of_nonneg_left ?_ hK₁0)
    exact Real.rpow_le_rpow_of_exponent_ge hw hw1 (min_le_left _ _)
  · intro x hx y hy _ _ hd j hj
    have hsd : parabolicSemigroup.scaleDist y x = parabolicNorm (y - x) := rfl
    have hexp : min α η + 2 - (γ + 2) = min α η - γ := by ring
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI j j)
    have hcI : 0 ≤ (Fintype.card ι : ℝ) * CI := mul_nonneg (Nat.cast_nonneg _) hCI0
    have hK1 : 0 ≤ (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2 :=
      mul_nonneg (add_nonneg hK₀0 hcI) (zero_le_one.trans hG)
    have hWpos : 0 < min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) :=
      lt_min (KGammaSup.weight_pos hx) (KGammaSup.weight_pos hy)
    have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
    rw [hsd, hexp]
    by_cases hjr : j ∈ Set.range P.emb
    · obtain ⟨kk, rfl⟩ := hjr
      have hdk : 𝒯.deg (P.emb kk) = polyDeg N' kk := P.deg_emb kk
      rw [hdk] at hj ⊢
      have hb := hCi kk hj M f T Cf CPi CGam CI CΓ2 S I hreal hInt hIp hCI hfV hΓ2 hx hy hd
      refine hb.trans ?_
      have h1 : Ci kk * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) ≤
          C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) :=
        mul_le_mul_of_nonneg_right (hCiC kk) hK1
      have hX0 : 0 ≤ parabolicNorm (y - x) ^ (γ + 2 - polyDeg N' kk) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ) :=
        mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hWpos.le _)
      calc _ ≤ C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf *
            (parabolicNorm (y - x) ^ (γ + 2 - polyDeg N' kk) *
              min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
                (min α η - γ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCf) hX0
        _ = _ := by ring
    · have hb := abs_kGammaRemG_sub_gamma_apply_le_of_notMem_range_win_near (r := r) S hp.shell hreal hInt hV hVb
        hdeg2 hN' hCI hfV hx hy hd hjr
      rw [hsd] at hb
      refine hb.trans ?_
      have h1 := (consts_le_W (Cs := 0) hK₀0 hcI hG hC1 (zero_le_one.trans hC1)).2
      have hnn : 0 ≤ Cf * parabolicNorm (y - x) ^ (γ + 2 - 𝒯.deg j) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ) :=
        mul_nonneg (mul_nonneg hCf (Real.rpow_nonneg hd0 _)) (Real.rpow_nonneg hWpos.le _)
      calc _ ≤ (C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2)) *
            (Cf * parabolicNorm (y - x) ^ (γ + 2 - 𝒯.deg j) *
              min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
                (min α η - γ)) :=
            mul_le_mul_of_nonneg_right h1 hnn
        _ = _ := by ring

end Model

end RegularityStructures

end

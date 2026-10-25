/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarNonpolyWNear
public import RegularityStructures.Abstract.Singular.KGamma.FarPolyMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Singular Schauder estimate for far pairs, all components, near-pair `Γ`-bounds

The bound on all components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` for far pairs `(x, y)` on the time
slab [Hai14, Proposition 6.16], for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

/-- **Singular Schauder for far pairs, all components** [Hai14, Prop. 6.16]. -/
theorem exists_abs_kGammaS_sub_gamma_apply_le_far_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {N : ℕ} {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (hN : N' ≤ N)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
        (V : Submodule ℝ (ι → ℝ)), (∀ z, f z ∈ V) →
        M.IsRealisingP h γ P I V → IsAbstractIntegration P V I 2 → 𝒯.IsSector V →
        (∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) →
        (∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) →
        (∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ,
          (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N') →
        (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      ∀ {CI CΓ2 : ℝ}, (∀ i j, |I (Pi.single i 1) j| ≤ CI) →
      M.GammaNearOn (γ + 2) CΓ2 (timeSlab T) →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab T → y ∈ timeSlab T →
      parabolicSemigroup.scaleDist y x ≤
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) →
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤
        64 * parabolicSemigroup.scaleDist y x →
      ∀ j : ι, 𝒯.deg j < γ + 2 →
      |(M.kGammaS h P I γ f y - M.gammaMap y x (M.kGammaS h P I γ f x)) j| ≤
        C * (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2 * Cf *
          (parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) *
            min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
              (min α η - γ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_kGammaS_sub_gamma_apply_emb_le_far_win_near 𝒯 γ η α hdeg hγ hαγ hαη hh
    hc P hN hni
  refine ⟨max C 1, (hC0.trans (le_max_left _ _)), ?_⟩
  intro M f T Cf CPi CGam S I V hfV hreal hInt hV hVb hdeg2 hN' hIp CI CΓ2 hCI hΓ2 x y hx hy
    hdW hW64 j hj
  have hexp : min α η - γ = min α η + 2 - (γ + 2) := by ring
  have hWpos : 0 < min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) :=
    lt_min (KGammaSup.weight_pos hx) (KGammaSup.weight_pos hy)
  have hd0 : 0 < parabolicSemigroup.scaleDist y x := by linarith
  by_cases hjr : j ∈ Set.range P.emb
  · obtain ⟨kk, rfl⟩ := hjr
    have hdj : 𝒯.deg (P.emb kk) = polyDeg N' kk := P.deg_emb kk
    have hk : polyDeg N' kk < γ + 2 := by rw [← hdj]; exact hj
    have := hC M f T Cf CPi CGam S hreal.poly I V hfV hVb hInt hIp hCI hΓ2 hx hy hdW hW64 kk hk
    rw [hdj, hexp]
    refine this.trans ?_
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI (P.emb kk) (P.emb kk))
    have hK : 0 ≤ max 1 CGam * CPi + Fintype.card ι * CI :=
      add_nonneg S.hK0 (mul_nonneg (Nat.cast_nonneg _) hCI0)
    have hnn : 0 ≤ (max 1 CΓ2) * Cf * (parabolicSemigroup.scaleDist y x ^ (γ + 2 - polyDeg N' kk) *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
          (min α η + 2 - (γ + 2))) :=
      mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _)) S.hCf)
        (mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.rpow_nonneg hWpos.le _))
    have := mul_le_mul_of_nonneg_right (le_max_left C 1) (mul_nonneg hK hnn)
    nlinarith [this]
  · have hne := abs_kGammaS_sub_gamma_nonpoly_le_singular_win_near S hh hreal hInt hV hVb hdeg2 hN' hCI hfV
      hx hy hdW hjr
    refine hne.trans ?_
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI j j)
    have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
    have hcard : 0 ≤ (Fintype.card ι : ℝ) * CI := mul_nonneg (Nat.cast_nonneg _) hCI0
    have hG : (1 : ℝ) ≤ max 1 CΓ2 := le_max_left _ _
    have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    have hq : 0 ≤ Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ) :=
      mul_nonneg (mul_nonneg S.hCf (Real.rpow_nonneg hd0.le _)) (Real.rpow_nonneg hWpos.le _)
    have h1 : (Fintype.card ι : ℝ) * CI ≤ max C 1 * (max 1 CGam * CPi + Fintype.card ι * CI) := by
      nlinarith [mul_nonneg hK0 (zero_le_one.trans hC1), mul_nonneg (sub_nonneg.2 hC1) hcard]
    have h2 : (Fintype.card ι : ℝ) * CI ≤ max C 1 * (max 1 CGam * CPi + Fintype.card ι * CI) *
        max 1 CΓ2 := by
      have hp : 0 ≤ max C 1 * (max 1 CGam * CPi + Fintype.card ι * CI) :=
        mul_nonneg (zero_le_one.trans hC1) (add_nonneg hK0 hcard)
      nlinarith [mul_le_mul_of_nonneg_left hG hp]
    calc _ ≤ (max C 1 * (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) *
          (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ)) :=
          mul_le_mul_of_nonneg_right h2 hq
      _ = _ := by ring

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarPolyBoundWNear
public import RegularityStructures.Abstract.Singular.KGamma.FarPolyWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.FarPoly
public import RegularityStructures.Abstract.Singular.KGamma.SupMain
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Singular Schauder estimate for far pairs, polynomial components, near-pair `Γ`-bounds

The bound on the polynomial components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` for far pairs `(x, y)` on
the time slab [Hai14, Proposition 6.16], for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {N' : ℕ}

/-- **Singular Schauder, polynomial components, far pairs** [Hai14, Prop. 6.16]. -/
theorem exists_abs_kGammaS_sub_gamma_apply_emb_le_far_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {N : ℕ} {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (hN : N' ≤ N)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
        (V : Submodule ℝ (ι → ℝ)), (∀ z, f z ∈ V) →
        (∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) →
        IsAbstractIntegration P V I 2 →
        (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      ∀ {CI CΓ2 : ℝ}, (∀ i j, |I (Pi.single i 1) j| ≤ CI) →
      M.GammaNearOn (γ + 2) CΓ2 (timeSlab T) →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab T → y ∈ timeSlab T →
      parabolicSemigroup.scaleDist y x ≤
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) →
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤
        64 * parabolicSemigroup.scaleDist y x →
      ∀ kk : PolyIndex N', polyDeg N' kk < γ + 2 →
      |(M.kGammaS h P I γ f y - M.gammaMap y x (M.kGammaS h P I γ f x)) (P.emb kk)| ≤
        C * (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2 * Cf *
          (parabolicSemigroup.scaleDist y x ^ (γ + 2 - polyDeg N' kk) *
            min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
              (min α η + 2 - (γ + 2))) := by
  obtain ⟨C0, hC00, hC0⟩ := exists_uniform_abs_kGammaS_apply_emb_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη hh hc
    P hN hni
  set Cc : ℝ := ∑ l : ι, (2 : ℝ) ^ |min α η + 2 - 𝒯.deg l| * (64 : ℝ) ^ |γ + 2 - 𝒯.deg l|
    with hCc
  have hCcl : ∀ l : ι, (2 : ℝ) ^ |min α η + 2 - 𝒯.deg l| * (64 : ℝ) ^ |γ + 2 - 𝒯.deg l| ≤ Cc :=
    fun l => Finset.single_le_sum (f := fun l : ι => (2 : ℝ) ^ |min α η + 2 - 𝒯.deg l| *
      (64 : ℝ) ^ |γ + 2 - 𝒯.deg l|) (fun l _ => by positivity) (Finset.mem_univ l)
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun l _ => by positivity
  refine ⟨Cc * (1 + Fintype.card ι) * max C0 1, by positivity, ?_⟩
  intro M f T Cf CPi CGam S hM I V hfV hVb hInt hIp CI CΓ2 hCI hΓ2 x y hx hy hdW hW64 kk hk
  set W := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hW
  set d := parabolicSemigroup.scaleDist y x with hdd
  set e : ℝ := min α η + 2 with he
  set c : ℝ := γ + 2 with hc2
  set q : ℝ := polyDeg N' kk with hq
  set j : ι := P.emb kk with hj
  set G : ℝ := max 1 CΓ2 with hG
  set K0 : ℝ := max 1 CGam * CPi with hK0
  set A : ℝ := C0 * K0 + Fintype.card ι * CI with hA
  have hWpos : 0 < W := lt_min (KGammaSup.weight_pos hx) (KGammaSup.weight_pos hy)
  have hd0 : 0 < d := by linarith
  have hG1 : 1 ≤ G := le_max_left _ _
  have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI j j)
  have hK00 : 0 ≤ K0 := S.hK0
  have hA0 : 0 ≤ A := by positivity
  have hCf := S.hCf
  have hR : 0 ≤ d ^ (c - q) * W ^ (e - c) :=
    mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.rpow_nonneg hWpos.le _)
  set R : ℝ := d ^ (c - q) * W ^ (e - c) with hRdef
  obtain ⟨hwx2, hwy2⟩ := weight_le_two_mul_min hdW
  have hwx1 : W ≤ singularWeight timeZeroDist x := min_le_left _ _
  have hwy1 : W ≤ singularWeight timeZeroDist y := min_le_right _ _
  have hdj : 𝒯.deg j = q := P.deg_emb kk
  -- bound at a point `z`
  have hpt : ∀ z, z ∈ timeSlab T → W ≤ singularWeight timeZeroDist z →
      singularWeight timeZeroDist z ≤ 2 * W → ∀ l : ι, 𝒯.deg l < c →
      |M.kGammaS h P I γ f z l| * d ^ (𝒯.deg l - q) ≤ A * Cf * Cc * R := by
    intro z hz h1 h2 l hl
    have hb := abs_kGammaS_apply_le_of_lt_win_near S h P I V hVb hInt hfV hCI hC00 hz
      (fun kk' hk' => hC0 M f T Cf CPi CGam S hM I V hfV hIp hz kk' hk') hl
    have hsc := rpow_mul_rpow_le_far hd0 hdW hW64 h1 h2 e (𝒯.deg l) q c hl.le
    have hsc' : singularWeight timeZeroDist z ^ (e - 𝒯.deg l) * d ^ (𝒯.deg l - q) ≤ Cc * R := by
      refine hsc.trans ?_
      have h64 : (64 : ℝ) ^ (c - 𝒯.deg l) ≤ (64 : ℝ) ^ |c - 𝒯.deg l| :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self _)
      have := hCcl l
      have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ |e - 𝒯.deg l| := by positivity
      calc _ ≤ (2 : ℝ) ^ |e - 𝒯.deg l| * (64 : ℝ) ^ |c - 𝒯.deg l| * R :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h64 h2n) hR
        _ ≤ Cc * R := mul_le_mul_of_nonneg_right this hR
    have hdp : 0 ≤ d ^ (𝒯.deg l - q) := Real.rpow_nonneg hd0.le _
    calc |M.kGammaS h P I γ f z l| * d ^ (𝒯.deg l - q)
        ≤ (A * Cf * singularWeight timeZeroDist z ^ (e - 𝒯.deg l)) * d ^ (𝒯.deg l - q) :=
          mul_le_mul_of_nonneg_right hb hdp
      _ = A * Cf * (singularWeight timeZeroDist z ^ (e - 𝒯.deg l) * d ^ (𝒯.deg l - q)) := by ring
      _ ≤ A * Cf * (Cc * R) := mul_le_mul_of_nonneg_left hsc' (mul_nonneg hA0 hCf)
      _ = _ := by ring
  have hNN : 0 ≤ A * Cf * Cc * R := by positivity
  -- the `b_j` term
  have hbj : |M.kGammaS h P I γ f y j| ≤ A * Cf * Cc * R := by
    have := hpt y hy hwy1 hwy2 j (by rw [hdj]; exact hk)
    rwa [hdj, sub_self, Real.rpow_zero, mul_one] at this
  -- the `Γ a` term
  have ha : M.kGammaS h P I γ f x ∈ lowerSubspace 𝒯.deg (γ + 2) :=
    kGammaS_mem_lowerSubspace h P I V hVb hInt hIp (hfV x) (S.hfT x)
  have hterm : ∀ l : ι, |M.kGammaS h P I γ f x l * M.gammaMap y x (Pi.single l 1) j| ≤
      A * Cf * G * Cc * R := by
    intro l
    have hnn : 0 ≤ A * Cf * G * Cc * R := by positivity
    by_cases hal : M.kGammaS h P I γ f x l = 0
    · rw [hal, zero_mul, abs_zero]; exact hnn
    · have hl : 𝒯.deg l < c := by
        by_contra hge; exact hal (ha l (not_lt.1 hge))
      have hΓl : |M.gammaMap y x (Pi.single l 1) j| ≤ G * d ^ (𝒯.deg l - q) := by
        have hdp : 0 ≤ d ^ (𝒯.deg l - q) := Real.rpow_nonneg hd0.le _
        by_cases hlj : l = j
        · subst hlj
          rw [(M.isGradedUnipotent_gammaMap y x).apply_single_self, abs_one, hdj, sub_self,
            Real.rpow_zero, mul_one]
          exact hG1
        · by_cases hle : 𝒯.deg l ≤ 𝒯.deg j
          · rw [(M.isGradedUnipotent_gammaMap y x).apply_single_of_le (Ne.symm hlj) hle]
            simp only [abs_zero]; exact mul_nonneg (zero_le_one.trans hG1) hdp
          · have hlt : 𝒯.deg j < 𝒯.deg l := not_le.1 hle
            have := hΓ2 l j hl hlt x hx y hy
              (le_gammaNearRadius_of_le_one (hdW.trans (hwx1.trans (singularWeight_le_one _ _))))
            rw [hdj] at this
            exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hdp)
      have hpl := hpt x hx hwx1 hwx2 l hl
      rw [abs_mul]
      calc |M.kGammaS h P I γ f x l| * |M.gammaMap y x (Pi.single l 1) j|
          ≤ |M.kGammaS h P I γ f x l| * (G * d ^ (𝒯.deg l - q)) :=
            mul_le_mul_of_nonneg_left hΓl (abs_nonneg _)
        _ = G * (|M.kGammaS h P I γ f x l| * d ^ (𝒯.deg l - q)) := by ring
        _ ≤ G * (A * Cf * Cc * R) := mul_le_mul_of_nonneg_left hpl (zero_le_one.trans hG1)
        _ = _ := by ring
  have hΓa : |M.gammaMap y x (M.kGammaS h P I γ f x) j| ≤
      Fintype.card ι * (A * Cf * G * Cc * R) := by
    rw [linearMap_apply_eq_sum]
    calc |∑ l, M.kGammaS h P I γ f x l * M.gammaMap y x (Pi.single l 1) j|
        ≤ ∑ _l : ι, A * Cf * G * Cc * R :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => hterm l)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hAm : A ≤ max C0 1 * (K0 + Fintype.card ι * CI) := by
    have h1 : C0 ≤ max C0 1 := le_max_left _ _
    have h2 : (1 : ℝ) ≤ max C0 1 := le_max_right _ _
    have hc0 : (0 : ℝ) ≤ Fintype.card ι * CI := mul_nonneg (Nat.cast_nonneg _) hCI0
    linarith [mul_le_mul_of_nonneg_right h1 hK00, mul_le_mul_of_nonneg_right h2 hc0]
  have hmain : |(M.kGammaS h P I γ f y - M.gammaMap y x (M.kGammaS h P I γ f x)) j| ≤
      (1 + Fintype.card ι) * (A * Cf * G * Cc * R) := by
    rw [Pi.sub_apply]
    refine (abs_sub _ _).trans ?_
    have hb1 : |M.kGammaS h P I γ f y j| ≤ A * Cf * G * Cc * R := by
      refine hbj.trans ?_
      have : A * Cf * Cc * R * 1 ≤ A * Cf * Cc * R * G :=
        mul_le_mul_of_nonneg_left hG1 hNN
      linarith
    linarith [hb1, hΓa]
  refine hmain.trans ?_
  have hpre : 0 ≤ (1 + (Fintype.card ι : ℝ)) * (Cf * G * Cc * R) := by positivity
  calc (1 + (Fintype.card ι : ℝ)) * (A * Cf * G * Cc * R)
      = A * ((1 + (Fintype.card ι : ℝ)) * (Cf * G * Cc * R)) := by ring
    _ ≤ (max C0 1 * (K0 + Fintype.card ι * CI)) * ((1 + (Fintype.card ι : ℝ)) * (Cf * G * Cc * R)) :=
        mul_le_mul_of_nonneg_right hAm hpre
    _ = _ := by ring

end Model

end RegularityStructures

end

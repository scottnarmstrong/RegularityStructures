/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupPiecesWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Profile.PolyPairing
public import RegularityStructures.Abstract.Singular.KGamma.SupTerm
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellG
public import RegularityStructures.Analysis.Heat.Schauder.Derivative

/-!
# The term of scale `n` of `𝒦_γ f`, near-pair `Γ`-bounds

The bound `|shellTerm| ≤ C K₀ C_f w^{α∧η + 2 − |k|} min ((2^n w)^a) ((2^n w)^{-b})` on the term of
scale `n` of the `X^k` component of `𝒦_γ f`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

private theorem exists_pos_forall_le_finite {κ : Type*} [Fintype κ] (P : κ → Prop) (g : κ → ℝ)
    (hg : ∀ i, P i → 0 < g i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, P i → δ ≤ g i := by
  classical
  by_cases hne : (Finset.univ.filter P).Nonempty
  · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ g hne
    exact ⟨g j, hg j (Finset.mem_filter.1 hj).2, fun i hi =>
      hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)⟩
  · refine ⟨1, one_pos, fun i hi => absurd ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩ hne⟩

namespace Model

variable (hh : ShellProfile h N) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
  (k : Fin 4 →₀ ℕ)

include hh hc in
/-- **The term of scale `n`.**  Under the non-integrality hypothesis `hni` and `|k| < γ + 2`, there
are `a, b > 0` and `C ≥ 0`, depending only on `𝒯, γ, η, α, h, k`, such that for `x` in the slab
`|shellTerm| ≤ C K₀ C_f w^{α∧η + 2 − |k|} min ((2^n w)^a) ((2^n w)^{-b})`. -/
theorem exists_abs_shellTerm_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) (hkγ : (multiDeg k : ℝ) < γ + 2)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') (hN : N' ≤ N)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ a b C : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup)
      (f : ParabolicSpace → ι → ℝ) (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ {x : ParabolicSpace}, x ∈ timeSlab T → ∀ n : ℕ,
      |M.shellTerm h f x k n| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) *
          min (((2 : ℝ) ^ n * singularWeight timeZeroDist x) ^ a)
            (((2 : ℝ) ^ n * singularWeight timeZeroDist x) ^ (-b)) := by
  classical
  set L : ℝ := (multiDeg k : ℝ) with hL
  set m0 : ℝ := min α η with hm0
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  obtain ⟨C₁, hC₁0, hC₁⟩ := KGammaSup.exists_abs_latticeRecon_shell_le_weight_win_near hh hc k 𝒯 γ η α hdeg
    hγ hαγ hαη
  set m : ℕ := ⌈m0 + 2⌉₊ + 1 with hm
  obtain ⟨C₂, hC₂0, hC₂⟩ := KGammaSup.exists_abs_latticeRecon_shell_le_weight_small_win_near hh hc k 𝒯 γ η
    α hdeg hγ hαγ hαη m
  obtain ⟨C₃, hC₃0, hC₃⟩ := KGammaSup.exists_abs_fx_mul_pairing_shell_le_win_near hh k 𝒯 γ η α hdeg
  obtain ⟨C₄, hC₄0, hC₄⟩ := KGammaSup.exists_abs_singShellPairing_le_weight_win_near hh hc k 𝒯 γ η α hdeg hγ
  set Cmax : ℝ := max (max C₁ C₂) (max C₃ C₄) with hCmax
  have hCmax0 : 0 ≤ Cmax := hC₁0.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hle1 : C₁ ≤ Cmax := (le_max_left _ _).trans (le_max_left _ _)
  have hle2 : C₂ ≤ Cmax := (le_max_right _ _).trans (le_max_left _ _)
  have hle3 : C₃ ≤ Cmax := (le_max_left _ _).trans (le_max_right _ _)
  have hle4 : C₄ ≤ Cmax := (le_max_right _ _).trans (le_max_right _ _)
  -- the exponents
  set aR : ℝ := 2 * (m : ℝ) + (L - 2 - m0) with haR
  have hm_ge : m0 + 2 + 1 ≤ (m : ℝ) := by
    have := Nat.le_ceil (m0 + 2)
    rw [hm]; push_cast; linarith
  have haR0 : 0 < aR := by rw [haR]; linarith
  obtain ⟨δm, hδm0, hδm⟩ := exists_pos_forall_le_finite (fun i => 𝒯.deg i + 2 < L)
    (fun i => L - 2 - 𝒯.deg i) (fun i hi => by simpa using (by linarith : 0 < L - 2 - 𝒯.deg i))
  obtain ⟨δp, hδp0, hδp⟩ := exists_pos_forall_le_finite (fun i => L < 𝒯.deg i + 2)
    (fun i => 𝒯.deg i + 2 - L) (fun i hi => by simpa using (by linarith : 0 < 𝒯.deg i + 2 - L))
  set a : ℝ := min aR δm with ha_def
  set b : ℝ := min (γ + 2 - L) δp with hb_def
  have ha0 : 0 < a := lt_min haR0 hδm0
  have hb0 : 0 < b := lt_min (by linarith) hδp0
  set e : ι → ℝ := fun i => L - 2 - 𝒯.deg i with he
  set Pp : Finset ι := Finset.univ.filter (fun i => L < 𝒯.deg i + 2) with hPp
  set Pm : Finset ι := Finset.univ.filter (fun i => 𝒯.deg i + 2 < L) with hPm
  set K : ℝ := (1 + Pp.card + Pm.card) * 64 ^ (|L - 2 - m0| + ∑ i ∈ Pm, |e i| + b) with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ Pp.card + Pm.card := by positivity
    positivity
  refine ⟨a, b, Cmax * K, ha0, hb0, mul_nonneg hCmax0 hK0, fun M f T Cf CPi CGam S hM x hx n => ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hw := KGammaSup.weight_pos hx
  have hw1 := singularWeight_le_one timeZeroDist x
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set w := singularWeight timeZeroDist x with hwdef
  set t : ℝ := (2 : ℝ) ^ n * w with htdef
  have ht : 0 < t := by positivity
  set K0 : ℝ := max 1 CGam * CPi with hK0def
  have hK00 : 0 ≤ K0 := S.hK0
  have hCf := S.hCf
  set W : ℝ := w ^ (m0 + 2 - L) with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg hw.le _
  set Bc : ℝ := Cmax * K0 * Cf * W with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have bump : ∀ Cj : ℝ, Cj ≤ Cmax → ∀ y : ℝ, 0 ≤ y →
      Cj * K0 * Cf * W * y ≤ Bc * y := fun Cj hCj y hy => by
    refine mul_le_mul_of_nonneg_right ?_ hy
    rw [hBc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCj hK00) hCf) hW0
  -- the pieces
  set R : ℝ := M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))
    with hR
  set J : ι → ℝ := fun i => f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
    (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) with hJ
  have hRb : |R| ≤ Bc * t ^ (L - 2 - m0) := by
    refine (hC₁ M f T Cf CPi CGam S hx n).trans ?_
    refine le_trans (le_of_eq (by ring)) (bump C₁ hle1 _ (Real.rpow_nonneg ht.le _))
  have hRs : t < 1 → |R| ≤ Bc * t ^ aR := fun h1 => by
    refine (hC₂ M f T Cf CPi CGam S hx n h1).trans ?_
    refine le_trans (le_of_eq (by ring)) (bump C₂ hle2 _ (Real.rpow_nonneg ht.le _))
  have hSb : 64 ≤ t → |M.singShellPairing h f x k n| ≤ Bc * t ^ (-b) := fun h64 => by
    refine (hC₄ M f T Cf CPi CGam S hx n h64).trans ?_
    have h1 : t ^ (L - 2 - γ) ≤ t ^ (-b) :=
      KGammaSup.rpow_le_rpow_of_one_le (by linarith) (by
        have : b ≤ γ + 2 - L := min_le_left _ _
        linarith)
    refine le_trans (le_of_eq (by ring)) ((bump C₄ hle4 _ (Real.rpow_nonneg ht.le _)).trans
      (mul_le_mul_of_nonneg_left h1 hBc0))
  have hJ0 : ∀ i, f x i ≠ 0 → 𝒯.deg i < γ ∧ α ≤ 𝒯.deg i ∧
      (i ∉ Set.range P.emb → L ≠ 𝒯.deg i + 2) := by
    intro i hi
    have h1 : 𝒯.deg i < γ := by
      by_contra hge
      exact hi ((mem_lowerSubspace).1 (S.hfT x) i (not_lt.1 hge))
    have h2 : α ≤ 𝒯.deg i := S.hα x i hi
    exact ⟨h1, h2, fun hp => hni i hp h2 h1⟩
  have hJpoly : ∀ i, i ∈ Set.range P.emb → J i = 0 := fun i hp => by
    have := Model.derivShellPairing_regPi_emb_eq_zeroP hM hh hN x hp k n
    simp only [hJ]
    rw [show parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) = 0 from this, mul_zero]
  have hJb : ∀ i, |J i| ≤ Bc * t ^ (e i) := by
    intro i
    by_cases hfi : f x i = 0
    · have : J i = 0 := by simp [hJ, hfi]
      rw [this, abs_zero]
      positivity
    · obtain ⟨h1, h2, -⟩ := hJ0 i hfi
      refine (hC₃ M f T Cf CPi CGam S hx n i h2 h1).trans ?_
      refine le_trans (le_of_eq (by ring)) (bump C₃ hle3 _ (Real.rpow_nonneg ht.le _))
  -- the two expressions for the term
  have hsing : M.singShellPairing h f x k n = R - ∑ i, J i := by
    obtain ⟨Cs, hCs, hS⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
    have hp := M.pairing_regPi_eq_sum_of_scaled_growth G S.hdeg (S.hfT x) (hS n x)
    unfold singShellPairing
    rw [hp]
    congr 1
    rw [Finset.sum_filter_of_ne]
    intro i _ hne
    by_contra hge
    exact hne (by rw [(mem_lowerSubspace).1 (S.hfT x) i (not_lt.1 hge), zero_mul])
  have hsplit : ∑ i, J i = ∑ i ∈ Pp, J i + ∑ i ∈ Pm, J i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => L < 𝒯.deg i + 2)]
    congr 1
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      simp only [hPm, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact not_lt.2 hi.le
    · intro i hi hnot
      simp only [hPm, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hnot
      by_cases hp : i ∈ Set.range P.emb
      · exact hJpoly i hp
      · have hfi : f x i = 0 := by
          by_contra hne
          obtain ⟨-, -, hne'⟩ := hJ0 i hne
          exact hne' hp (le_antisymm hnot hi)
        simp [hJ, hfi]
  have hT1 : M.shellTerm h f x k n = M.singShellPairing h f x k n + ∑ i ∈ Pp, J i := rfl
  have hT2 : M.shellTerm h f x k n = R - ∑ i ∈ Pm, J i := by
    rw [hT1, hsing, hsplit]; ring
  have key := KGammaSup.abs_le_mul_min_of_pieces ha0 hb0 e Pp Pm
    (fun i hi => by
      have hi' : L < 𝒯.deg i + 2 := (Finset.mem_filter.1 hi).2
      have : b ≤ 𝒯.deg i + 2 - L := (min_le_right _ _).trans (hδp i hi')
      simp only [he]; linarith)
    (fun i hi => by
      have hi' : 𝒯.deg i + 2 < L := (Finset.mem_filter.1 hi).2
      exact (min_le_right _ _).trans (hδm i hi'))
    ht hBc0 (min_le_left _ _) J hT1 hT2 hRb hRs hSb (fun i _ => hJb i) (fun i _ => hJb i)
  refine key.trans (le_of_eq ?_)
  rw [hK, hBc]
  ring

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.Recon
public import RegularityStructures.Abstract.Singular.KGamma.SupSumWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.PairingG
public import RegularityStructures.Abstract.Singular.KGamma.SupCoeffG
public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# The unit coefficient of `𝒦_γ f + R_γ f`, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, every nonzero component of `f z` has degree `> −2`,
and the coefficient of the unit `X^0` in `(𝒦_γ f + R_γ f)(x)` is
`∑_n ⟨R f, K_n(x − ·)⟩ + ⟨R f, r(x − ·)⟩` (lattice reconstruction), for models whose `Γ`-bounds hold
only for near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in
place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}
  {h r : ParabolicSpace → ℝ} {N N' : ℕ}

/-- Under the window setting every nonzero component of `f z` has degree `> -2`. -/
theorem _root_.RegularityStructures.LayerSettingWNear.neg_two_lt_deg (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {z : ParabolicSpace} {i : ι} (hi : f z i ≠ 0) : -2 < 𝒯.deg i :=
  lt_of_lt_of_le (lt_of_lt_of_le S.hαη (min_le_left _ _)) (S.hα z i hi)

/-- The `n`-th term of the `k = 0` series is `⟨R f, K_n(x − ·)⟩`. -/
theorem shellTerm_zero_eq_latticeRecon_wnear (hh : ShellProfile h N)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (x : ParabolicSpace) (n : ℕ) :
    M.shellTerm h f x 0 n = M.latticeRecon f (fun y => scaledShell h n (x - y)) := by
  classical
  obtain ⟨Cs, -, hS⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh (0 : Fin 4 →₀ ℕ)
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hp := M.pairing_regPi_eq_sum_single_of_scaled_growth G S.hdeg (S.hfT x) (hS n x)
  have h0 : multiDirs (0 : Fin 4 →₀ ℕ) = [] := by simp [multiDirs]
  have hmd0 : multiDeg (0 : Fin 4 →₀ ℕ) = 0 := by simp [multiDeg]
  have hsing : M.singShellPairing h f x 0 n = M.latticeRecon f
      (fun y => scaledShell h n (x - y)) - ∑ i, f x i * parabolicSemigroup.pairing
        (M.regPi x (Pi.single i 1)) (fun y => lineIter (multiDirs 0) (scaledShell h n) (x - y)) := by
    unfold singShellPairing
    rw [hp]
    simp only [h0, lineIter_nil]
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => ((multiDeg (0 : Fin 4 →₀ ℕ) : ℕ) : ℝ) <
      𝒯.deg i + 2), f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
        (fun y => lineIter (multiDirs 0) (scaledShell h n) (x - y)) =
      ∑ i, f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
        (fun y => lineIter (multiDirs 0) (scaledShell h n) (x - y)) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
    have : f x i = 0 := by
      by_contra hne
      have := S.neg_two_lt_deg hne
      exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hmd0]; push_cast; linarith⟩)
    simp [this]
  unfold shellTerm
  rw [hsing, hsum]
  ring

/-- **The unit coefficient of `𝒦_γ f + R_γ f`** (lattice reconstruction): for the index `kk`
of the unit `X^0` (`kk.1 = 0`),
`(𝒦_γ f + R_γ f)(x)_{X^0} = ∑_n ⟨R f, K_n(x − ·)⟩ + ⟨R f, r(x − ·)⟩`. -/
theorem kGammaRemG_apply_emb_zero_wnear (hh : ShellProfile h N) (hN : N' ≤ N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {x : ParabolicSpace} (hx : x ∈ timeSlab T)
    (kk : PolyIndex N') (hkk : kk.1 = 0) (hI0 : I (f x) (P.emb kk) = 0) :
    M.kGammaRemG h r P I γ f x (P.emb kk) =
      ∑' n, M.latticeRecon f (fun y => scaledShell h n (x - y)) +
        M.remPairing f (fun y => r (x - y)) := by
  classical
  have hmd : multiDeg kk.1 = 0 := by simp [multiDeg, hkk]
  have hpd : polyDeg N' kk = 0 := by simp [polyDeg, hkk]
  have hk : (multiDeg kk.1 : ℝ) < γ + 2 := by
    rw [hmd]; push_cast; linarith [S.hγ]
  have hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg kk.1 : ℝ) ≠ 𝒯.deg i + 2 := by
    intro i _ hαi _
    have h2 : -2 < α := lt_of_lt_of_le S.hαη (min_le_left _ _)
    rw [hmd]; push_cast; linarith
  obtain ⟨C, -, hC⟩ := exists_summable_abs_tsum_shellTerm_le_win_near hh hc kk.1
    𝒯 γ η α S.hdeg S.hγ S.hαγ S.hαη hk P hN hni
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hsum := (hC M f T Cf CPi CGam S hM hx).1
  have e1 := M.kGammaS_apply_emb_growth hh G S.hdeg P I (S.hfT x) kk hI0
    (by rw [hpd]; linarith [S.hγ]) hsum
  have e2 : M.remVecG r P γ f x (P.emb kk) = M.remPairing f (fun y => r (x - y)) := by
    unfold remVecG
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single kk]
    · have hlt : polyDeg N' kk < γ + 2 := by rw [hpd]; linarith [S.hγ]
      simp [hlt, hkk, multiFactorial, multiDirs, lineIter_nil]
    · intro b _ hb
      split_ifs <;> simp [single_emb_apply, hb]
    · simp
  unfold kGammaRemG
  rw [Pi.add_apply, e1, e2, hkk]
  simp only [shellTerm_zero_eq_latticeRecon_wnear hh S]
  simp [multiFactorial]

end Model

end RegularityStructures

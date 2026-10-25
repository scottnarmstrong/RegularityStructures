/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Package
public import Phi43.RestartDiff.Window
public import Phi43.RestartDiff.ExtGammaDiff
public import Phi43.RestartDiff.SlabDiff
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The two-model per-model hypotheses of the `Φ⁴₃` window fixed point at a restart

Two-model companion of `Phi43.Restart.Package`.  `restart_quantitative_diff`: let `Z`, `Z'`
satisfy `IsRenormalisedCanonicalModel N κ noise C Z` and
`IsRenormalisedCanonicalModel N κ noise' C' Z'`, with `phi43Size ≤ ofReal B` for both and
`phi43Dist κ η T Z Z' ψ ψ' ≤ ofReal δ`, let `s ∈ [0, T]`, and let `M₁'`, `M₂'` be enlarged
models compatible (`EnlargedCompat`) with the time translates by `(s, 0)` of the two renormalised
canonical models, both satisfying `RestartQualitative`.  Then, with a constant `c` depending only
on `(κ, N)`:

* the `Π`-difference at level `κ` on `hairerTimeWindow` is bounded by `δ`;
* the near-`1` `Γ`-difference at level `κ` on `hairerTimeWindow` is bounded by `δ`;
* the near-`1` `Γ`-differences on `timeSlab T'`, `T' ≤ 1`, at the levels `gamma κ`,
  `gamma κ + α`, `gamma κ + α + α + 2` are bounded by `restartGammaDiffConst c B * δ`.

Route: pinned data and periodicity (`RestartDiff.Window`), the two-model Hairer estimate (5.18)
for the integrals of the sources (`RestartDiff.ExtGammaDiff`), and the Lipschitz bound of the
structure-group action (`RestartDiff.SlabDiff`).  The chained near-`4` difference constant is
linear in `δ` (`gammaDiffChainConst_eq_mul`).
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Restart

open RegularityStructures.Phi43.LiftBounds

theorem gammaDiffStep_eq_mul (n : ℕ) (C : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    gammaDiffStep n C δ m = δ * gammaDiffStep n C 1 m := by
  induction m with
  | zero => simp [gammaDiffStep]
  | succ k ih =>
      simp only [gammaDiffStep, ih, max_eq_right hδ, max_eq_right zero_le_one]
      ring

/-- The chained near-`4` difference constant is linear in the near-`1` difference constant. -/
theorem gammaDiffChainConst_eq_mul (n : ℕ) (C : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    gammaDiffChainConst n C δ m = δ * gammaDiffChainConst n C 1 m := by
  unfold gammaDiffChainConst
  rw [gammaDiffStep_eq_mul n C hδ m, mul_max_of_nonneg _ _ hδ, mul_one]

theorem gammaDiffChainConst_nonneg (n : ℕ) (C : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    0 ≤ gammaDiffChainConst n C δ m :=
  hδ.trans (le_max_left _ _)

/-- The window `Γ`-constant of the near-`4` chain at size `B`. -/
@[expose] def restartChainG (B : ℝ) : ℝ :=
  max (max (gammaChainConst (Fintype.card SymbolF) B 16)
    (gammaChainConst (Fintype.card SymbolF) B 16)) 1

/-- The difference constant of the Hairer estimate `(5.18)` for unit model distance. -/
@[expose] def extDiffConst (c B : ℝ) : ℝ :=
  c * (restartChainG B * restartChainG B +
    gammaDiffChainConst (Fintype.card SymbolF) B 1 16 * (1 + B * restartChainG B))

/-- The near-`1` `Γ`-difference constant on the slab, per unit model distance. -/
@[expose] def restartGammaDiffConst (c B : ℝ) : ℝ :=
  max (oldGammaDiffConst (max 1 (extConst c B)) * extDiffConst c B) (extDiffConst c B)

theorem restartChainG_one_le (B : ℝ) : 1 ≤ restartChainG B := le_max_right _ _

theorem extDiffConst_nonneg {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) : 0 ≤ extDiffConst c B := by
  unfold extDiffConst
  have hG := zero_le_one.trans (restartChainG_one_le B)
  exact mul_nonneg hc (add_nonneg (mul_nonneg hG hG) (mul_nonneg
    (gammaDiffChainConst_nonneg _ _ zero_le_one _) (add_nonneg zero_le_one (mul_nonneg hB hG))))

theorem extConst_mono {c c' B : ℝ} (hcc : c ≤ c') (hB : 0 ≤ B) : extConst c B ≤ extConst c' B := by
  unfold extConst
  have h1 : 1 ≤ max (gammaChainConst (Fintype.card SymbolF) B 16) 1 := le_max_right _ _
  have hX : 0 ≤ (1 + B * max (gammaChainConst (Fintype.card SymbolF) B 16) 1) :=
    add_nonneg zero_le_one (mul_nonneg hB (zero_le_one.trans h1))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hX) (zero_le_one.trans h1)

theorem extDiffConst_mono {c c' B : ℝ} (hcc : c ≤ c') (hB : 0 ≤ B) :
    extDiffConst c B ≤ extDiffConst c' B := by
  unfold extDiffConst
  have hG := zero_le_one.trans (restartChainG_one_le B)
  exact mul_le_mul_of_nonneg_right hcc (add_nonneg (mul_nonneg hG hG) (mul_nonneg
    (gammaDiffChainConst_nonneg _ _ zero_le_one _) (add_nonneg zero_le_one (mul_nonneg hB hG))))

variable {κ : Kappa}

/-- **The two-model restart package.** -/
theorem restart_quantitative_diff (N : ℕ) (hN : 3 ≤ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {B δ : ℝ}, 0 ≤ B → 0 ≤ δ → ∀ {η T s : ℝ} {ψ ψ' : ℝ → C(Torus3, ℝ)}
      {noise noise' : CanonicalNoise} {Cg Cg' : ℝ} {q q' : ℕ}
      {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
      {hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise'.zeta z‖ ≤ Cg' * (1 + parabolicNorm z) ^ q'}
      {C C' : RenormalisationConstants} {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup},
      Statements.IsRenormalisedCanonicalModel N κ noise C Z →
      Statements.IsRenormalisedCanonicalModel N κ noise' C' Z' → s ∈ Icc (0 : ℝ) T →
      Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
      Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
      Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
      ∀ (M₁' M₂' : Model (phi43RegularityStructureF κ) parabolicSemigroup),
      EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s))
        M₁' →
      EnlargedCompat κ
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate (restartPoint s)) M₂' →
      RestartQualitative κ N M₁' → RestartQualitative κ N M₂' →
      M₁'.PiDiffBoundOn M₂' (gamma κ + phi43Alpha κ + phi43Alpha κ) δ hairerTimeWindow ∧
      M₁'.GammaDiffBoundNearOn M₂' (gamma κ + phi43Alpha κ + phi43Alpha κ) δ 1
        hairerTimeWindow ∧
      ∀ {T' : ℝ}, T' ≤ 1 →
        M₁'.GammaDiffBoundNearOn M₂' (gamma κ) (restartGammaDiffConst c B * δ) 1
          (timeSlab T') ∧
        M₁'.GammaDiffBoundNearOn M₂' (gamma κ + phi43Alpha κ) (restartGammaDiffConst c B * δ) 1
          (timeSlab T') ∧
        M₁'.GammaDiffBoundNearOn M₂' (gamma κ + phi43Alpha κ + phi43Alpha κ + 2)
          (restartGammaDiffConst c B * δ) 1 (timeSlab T') := by
  obtain ⟨c₀, hc₀, hc⟩ := exists_extGamma_const (κ := κ) N
  obtain ⟨c₂, hc₂, hcd⟩ := exists_extGamma_const_diff (κ := κ) N hN
  refine ⟨c₀ + c₂, add_nonneg hc₀ hc₂, fun {B δ} hB hδ η T s ψ ψ' noise noise' Cg Cg' q q' hg hg'
    C C' Z Z' hZ hZ' hs hsize hsize' hdist M₁' M₂' hC₁ hC₂ hQ₁ hQ₂ => ?_⟩
  obtain ⟨hreal₁, hgr₁⟩ := hQ₁
  obtain ⟨hreal₂, hgr₂⟩ := hQ₂
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  rw [gamma_add_alpha_add_alpha] at hreal₁ hgr₁ hreal₂ hgr₂ ⊢
  have hlev : κ.1 ≤ 3 / 2 - 5 * κ.1 := by linarith
  have hlevg : gamma κ ≤ 3 / 2 - 5 * κ.1 := by simp only [gamma]; linarith
  have hkg : κ.1 ≤ gamma κ := by simp only [gamma]; linarith
  -- single-model window bounds
  have hPi₁ : M₁'.PiBoundOn κ.1 B hairerTimeWindow :=
    hC₁.piBoundOn hlev (restart_canonical_piBoundOn_window hZ hB hs hsize)
  have hPi₂ : M₂'.PiBoundOn κ.1 B hairerTimeWindow :=
    hC₂.piBoundOn hlev (restart_canonical_piBoundOn_window hZ' hB hs hsize')
  have hGam₁ : M₁'.GammaBoundNearOn κ.1 B 1 hairerTimeWindow :=
    hC₁.gammaBoundNearOn hlev (Model.GammaBoundNearOn.mono_degree
      (restart_canonical_gammaBoundNearOn_window hZ hB hs hsize) hkg)
  have hGam₂ : M₂'.GammaBoundNearOn κ.1 B 1 hairerTimeWindow :=
    hC₂.gammaBoundNearOn hlev (Model.GammaBoundNearOn.mono_degree
      (restart_canonical_gammaBoundNearOn_window hZ' hB hs hsize') hkg)
  -- window differences
  have hdPi : M₁'.PiDiffBoundOn M₂' κ.1 δ hairerTimeWindow :=
    EnlargedCompat.piDiffBoundOn_diff hC₁ hC₂ hlev
      (restart_canonical_piDiffBoundOn_window_diff hZ hZ' hδ hs hdist)
  have hdGam : M₁'.GammaDiffBoundNearOn M₂' κ.1 δ 1 hairerTimeWindow :=
    EnlargedCompat.gammaDiffBoundNearOn_diff hC₁ hC₂ hlev (Model.GammaDiffBoundNearOn.mono_degree
      (restart_canonical_gammaDiffBoundNearOn_window_diff hZ hZ' hδ hs hdist) hkg)
  refine ⟨hdPi, hdGam, fun {T'} hT' => ?_⟩
  -- the single-model Hairer estimate for both models
  have S₁ := extSetting hN hreal₁ hgr₁ hB hPi₁ hGam₁
  have S₂ := extSetting hN hreal₂ hgr₂ hB hPi₂ hGam₂
  have hb₁ := fun i hi {x y : ParabolicSpace} (hx : x ∈ timeSlab 1) (hy : y ∈ timeSlab 1) hxy j
      hj => (hc M₁' S₁ i hi hx hy hxy j hj).trans (mul_le_mul_of_nonneg_right
        (extConst_mono (B := B) (le_add_of_nonneg_right hc₂) hB)
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
  have hb₂ := fun i hi {x y : ParabolicSpace} (hx : x ∈ timeSlab 1) (hy : y ∈ timeSlab 1) hxy j
      hj => (hc M₂' S₂ i hi hx hy hxy j hj).trans (mul_le_mul_of_nonneg_right
        (extConst_mono (B := B) (le_add_of_nonneg_right hc₂) hB)
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
  -- the two-model Hairer estimate
  have hW := segmentClosed_hairerTimeWindow
  have hGN₁ := hGam₁.toGammaNearOn M₁' hW
  have hGN₂ := hGam₂.toGammaNearOn M₂' hW
  have hdGN := Model.GammaDiffBoundNearOn.toGammaDiffNearOn hW hGam₁ hGam₂ hdGam
  have hbd := fun i hi {x y : ParabolicSpace} (hx : x ∈ timeSlab 1) (hy : y ∈ timeSlab 1) hxy j
      hj => hcd M₁' M₂' hreal₁ hreal₂ hGN₁ hPi₂ hGN₂ hB hdPi hdGN hδ
        (gammaDiffChainConst_nonneg _ _ hδ _) hgr₁ hgr₂ i hi hx hy hxy j hj
  have hEd : c₂ * (δ * max (max (gammaChainConst (Fintype.card SymbolF) B 16)
        (gammaChainConst (Fintype.card SymbolF) B 16)) 1 *
        max (max (gammaChainConst (Fintype.card SymbolF) B 16)
        (gammaChainConst (Fintype.card SymbolF) B 16)) 1 +
      gammaDiffChainConst (Fintype.card SymbolF) B δ 16 *
        (1 + B * max (max (gammaChainConst (Fintype.card SymbolF) B 16)
        (gammaChainConst (Fintype.card SymbolF) B 16)) 1)) ≤ extDiffConst (c₀ + c₂) B * δ := by
    rw [gammaDiffChainConst_eq_mul _ _ hδ]
    have := extDiffConst_mono (B := B) (le_add_of_nonneg_left hc₀ : c₂ ≤ c₀ + c₂) hB
    have hδ' := mul_le_mul_of_nonneg_right this hδ
    refine le_trans (le_of_eq ?_) hδ'
    unfold extDiffConst restartChainG
    ring
  have hbd' := fun i hi {x y : ParabolicSpace} (hx : x ∈ timeSlab 1) (hy : y ∈ timeSlab 1) hxy j
      hj => (hbd i hi hx hy hxy j hj).trans (mul_le_mul_of_nonneg_right hEd
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
  have hEd0 : 0 ≤ extDiffConst (c₀ + c₂) B * δ :=
    mul_nonneg (extDiffConst_nonneg (add_nonneg hc₀ hc₂) hB) hδ
  have h2 := gammaBoundNearOn_kappa_add_two_diff hEd0 hC₁ hC₂ hb₁ hb₂ hbd' hT'
  have hconst : max (oldGammaDiffConst (max 1 (extConst (c₀ + c₂) B)) *
      (extDiffConst (c₀ + c₂) B * δ)) (extDiffConst (c₀ + c₂) B * δ) =
      restartGammaDiffConst (c₀ + c₂) B * δ := by
    unfold restartGammaDiffConst
    rw [← mul_assoc, max_mul_of_nonneg _ _ hδ]
  rw [hconst] at h2
  have hmono : ∀ γ : ℝ, γ ≤ κ.1 + 2 →
      M₁'.GammaDiffBoundNearOn M₂' γ (restartGammaDiffConst (c₀ + c₂) B * δ) 1 (timeSlab T') :=
    fun γ hγ => Model.GammaDiffBoundNearOn.mono_degree h2 hγ
  refine ⟨hmono _ ?_, hmono _ ?_, h2⟩
  · simp only [gamma]; linarith
  · simp only [gamma, phi43Alpha]; linarith

end RegularityStructures.Phi43.Restart

end

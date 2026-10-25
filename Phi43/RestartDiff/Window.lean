/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Window
public import Phi43.Restart.NearBridge
public import Phi43.Restart.Compat
public import Phi43Statements.Defs.Phi43Dist
public import RegularityStructures.Probability.ModelKolmogorovHSDiagonal

/-!
# Window bounds of the difference of two restarted canonical models from the distance of the lifts

Two-model companion of `Phi43.Restart.Window`.  Let
`Z` and `Z'` satisfy `IsRenormalisedCanonicalModel N κ noise C Z` and
`IsRenormalisedCanonicalModel N κ noise' C' Z'`, with `phi43Dist κ η T Z Z' ψ ψ' ≤ ofReal δ`.
The canonical models `M₀ = canonicalRenormalisedModel N κ noise Cg q hg C` and `M₀'` (same noises and
constants) agree with `Z` and `Z'` on the pinned `Π` and on `Γ` away from `X₀`
(`Phi43.Pinned`), so on the box `phi43Box (T + 1)` the differences of `M₀` and `M₀'` are those of
`Z` and `Z'`.  By the spatial periodicity of both canonical models and the time translation by
`(s, 0)`, for `s ∈ [0, T]`, with constant `δ`:

* the `Π`-difference at level `κ` on `hairerTimeWindow`;
* the near-`1` `Γ`-difference at level `gamma κ` on `hairerTimeWindow`.

Below the planted symbols these differences pass to enlarged models compatible with the two
restarted canonical models (`EnlargedCompat.piDiffBoundOn_diff`,
`EnlargedCompat.gammaDiffBoundNearOn_diff`).
-/

public section

open Set
open scoped ENNReal NNReal

namespace RegularityStructures.Phi43.Restart

open RegularityStructures.Phi43.LiftBounds

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Translation covariance of the near-pair `Γ`-difference bound. -/
theorem gammaBoundNearOn_translate_iff_diff (M₁ M₂ : Model 𝒯 parabolicSemigroup)
    (a : ParabolicSpace) {γ C R : ℝ} {S : Set ParabolicSpace} :
    (M₁.translate a).GammaDiffBoundNearOn (M₂.translate a) γ C R S ↔
      M₁.GammaDiffBoundNearOn M₂ γ C R ((· + a) '' S) := by
  constructor
  · intro h i j hi hj x hx y hy hxy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have := h i j hi hj x hx y hy (by
      simpa only [Model.parabolicSemigroup_scaleDist_translate] using hxy)
    simpa only [Model.gammaMap_translate, Model.parabolicSemigroup_scaleDist_translate] using this
  · intro h i j hi hj x hx y hy hxy
    have := h i j hi hj (x + a) ⟨x, hx, rfl⟩ (y + a) ⟨y, hy, rfl⟩ (by
      simpa only [Model.parabolicSemigroup_scaleDist_translate] using hxy)
    simpa only [Model.gammaMap_translate, Model.parabolicSemigroup_scaleDist_translate] using this

/-- A box bound on the `Π`-difference extends to the strip for two periodic models. -/
theorem piBoundOn_timeStrip_of_periodic_diff {M₁ M₂ : Model 𝒯 parabolicSemigroup}
    (hper₁ : PiSpatialPeriodic M₁) (hper₂ : PiSpatialPeriodic M₂) {γ C a b : ℝ}
    {S : Set ParabolicSpace}
    (hS : ∀ z : ParabolicSpace, a ≤ z.1 → z.1 ≤ b → (∀ i, z.2 i ∈ Ico (0 : ℝ) 1) → z ∈ S)
    (h : M₁.PiDiffBoundOn M₂ γ C S) : M₁.PiDiffBoundOn M₂ γ C (timeStrip a b) := by
  intro i hi t ht x hx
  have hmem := hS (x - latticeShift (floorShift x))
    (by rw [sub_floorShift_time]; exact hx.1) (by rw [sub_floorShift_time]; exact hx.2)
    (sub_floorShift_mem x)
  have := h i hi t ht _ hmem
  rwa [← hper₁ (floorShift x) (x - latticeShift (floorShift x)) i t,
    ← hper₂ (floorShift x) (x - latticeShift (floorShift x)) i t, sub_add_cancel] at this

/-- Near pairs: a box bound on the `Γ`-difference extends to the strip for two periodic models. -/
theorem gammaBoundNearOn_timeStrip_of_periodic_diff {M₁ M₂ : Model 𝒯 parabolicSemigroup}
    (hper₁ : GammaSpatialPeriodic M₁) (hper₂ : GammaSpatialPeriodic M₂) {γ C a b : ℝ}
    {S : Set ParabolicSpace}
    (hS : ∀ z w : ParabolicSpace, a ≤ z.1 → z.1 ≤ b → a ≤ w.1 → w.1 ≤ b →
      (∀ i, z.2 i ∈ Ico (0 : ℝ) 1) → parabolicNorm (w - z) ≤ 1 → z ∈ S ∧ w ∈ S)
    (h : M₁.GammaDiffBoundNearOn M₂ γ C 1 S) :
    M₁.GammaDiffBoundNearOn M₂ γ C 1 (timeStrip a b) := by
  intro i j hi hj x hx y hy hxy
  change parabolicNorm (y - x) ≤ 1 at hxy
  set n := floorShift x
  have hd : (y - latticeShift n) - (x - latticeShift n) = y - x := by abel
  have hxy' : parabolicNorm ((y - latticeShift n) - (x - latticeShift n)) ≤ 1 := by
    rw [hd]; exact hxy
  obtain ⟨h1, h2⟩ := hS (x - latticeShift n) (y - latticeShift n)
    (by rw [sub_floorShift_time]; exact hx.1) (by rw [sub_floorShift_time]; exact hx.2)
    (by simp [latticeShift]; exact hy.1) (by simp [latticeShift]; exact hy.2)
    (sub_floorShift_mem x) hxy'
  have := h i j hi hj _ h1 _ h2 hxy'
  change |_ - _| ≤ C * parabolicNorm _ ^ _ at this
  rw [hd, ← hper₁ n (x - latticeShift n) (y - latticeShift n),
    ← hper₂ n (x - latticeShift n) (y - latticeShift n), sub_add_cancel, sub_add_cancel] at this
  exact this

end Generic

variable {N : ℕ} {κ : Kappa} {noise noise' : CanonicalNoise} {Cg Cg' : ℝ} {q q' : ℕ}
  {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
  {hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise'.zeta z‖ ≤ Cg' * (1 + parabolicNorm z) ^ q'}
  {C C' : RenormalisationConstants}
  {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup} {η T δ s : ℝ}
  {ψ ψ' : ℝ → C(Torus3, ℝ)}

/-- The `Π`-difference bound on the box from the distance `phi43Dist`, at the cutoff `gamma κ`. -/
theorem piDiffBoundOn_of_phi43Dist_le_diff (hδ : 0 ≤ δ)
    (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) :
    Z.PiDiffBoundOn Z' (gamma κ) δ (Statements.phi43Box (T + 1)) := by
  have h1 : Z.piDiffNormOn Z' (gamma κ) (Statements.phi43Box (T + 1)) ≤ ((δ.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    ((le_self_add.trans le_self_add).trans h).trans (by rw [ENNReal.ofReal])
  have := (Z.piDiffNormOn_le_iff Z' _ _ δ.toNNReal).1 h1
  rwa [Real.coe_toNNReal _ hδ] at this

/-- The `Γ`-difference bound on the box from the distance `phi43Dist`, at the cutoff `gamma κ`. -/
theorem gammaDiffBoundOn_of_phi43Dist_le_diff (hδ : 0 ≤ δ)
    (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) :
    Z.GammaDiffBoundOn Z' (gamma κ) δ (Statements.phi43Box (T + 1)) := by
  have h1 : Z.gammaDiffNormOn Z' (gamma κ) (Statements.phi43Box (T + 1)) ≤
      ((δ.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    ((le_add_self.trans le_self_add).trans h).trans (by rw [ENNReal.ofReal])
  have := (Z.gammaDiffNormOn_le_iff Z' _ _ δ.toNNReal).1 h1
  rwa [Real.coe_toNNReal _ hδ] at this

/-- The `Π`-difference of the two canonical models at level `κ` on the box. -/
theorem canonical_piDiffBoundOn_box_diff (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise' C' Z') (hδ : 0 ≤ δ)
    (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).PiDiffBoundOn
      (canonicalRenormalisedModel N κ noise' Cg' q' hg' C') κ.1 δ (Statements.phi43Box (T + 1)) := by
  intro τ hτ t ht x hx
  have hpin := isPinnedSymbol_of_homogeneity_lt (κ := κ) hτ
  have hZb := piDiffBoundOn_of_phi43Dist_le_diff hδ h τ (by
    have : homogeneity κ τ < κ.1 := hτ
    have hk0 : 0 < κ.1 := κ.2.1
    have hk' : κ.1 < 1 / 16 := κ.2.2
    simp only [gamma]; linarith) t ht x hx
  rw [regPi_eq_of_isRenormalisedCanonicalModel hZ
      (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C) hpin x ht.1 x,
    regPi_eq_of_isRenormalisedCanonicalModel hZ'
      (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise' Cg' q' hg' C') hpin x
      ht.1 x] at hZb
  exact hZb

/-- The `Γ`-difference of the two canonical models at level `gamma κ` on the box. -/
theorem canonical_gammaDiffBoundOn_box_diff
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise' C' Z') (hδ : 0 ≤ δ)
    (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).GammaDiffBoundOn
      (canonicalRenormalisedModel N κ noise' Cg' q' hg' C') (gamma κ) δ
      (Statements.phi43Box (T + 1)) := by
  intro i j hi hj x hx y hy
  have hZb := gammaDiffBoundOn_of_phi43Dist_le_diff hδ h i j hi hj x hx y hy
  rw [gammaMap_single_eq_of_isRenormalisedCanonicalModel hZ
      (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C)
      (homogeneity_lt_gamma_ne_x0 hi),
    gammaMap_single_eq_of_isRenormalisedCanonicalModel hZ'
      (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise' Cg' q' hg' C')
      (homogeneity_lt_gamma_ne_x0 hi)] at hZb
  exact hZb

/-- `Π`-difference of the two restarted canonical models on the window, level `κ`. -/
theorem restart_canonical_piDiffBoundOn_window_diff
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise' C' Z') (hδ : 0 ≤ δ)
    (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) :
    ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)).PiDiffBoundOn
      ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate (restartPoint s))
      κ.1 δ hairerTimeWindow := by
  rw [Model.piDiffBoundOn_translate_iff, hairerTimeWindow_eq_timeStrip,
    image_add_restartPoint_timeStrip]
  exact piBoundOn_timeStrip_of_periodic_diff
    (canonicalRenormalisedModel_piSpatialPeriodic N κ noise Cg q hg C)
    (canonicalRenormalisedModel_piSpatialPeriodic N κ noise' Cg' q' hg' C')
    (hS := fun _ h1 h2 h3 => mem_phi43Box_of_cell (a := -1 + s) (b := 2 + s)
      (by linarith [hs.1]) (by linarith [hs.2]) h1 h2 h3)
    (canonical_piDiffBoundOn_box_diff hZ hZ' hδ h)

/-- Near-`1` `Γ`-difference of the two restarted canonical models on the window, level
`gamma κ`. -/
theorem restart_canonical_gammaDiffBoundNearOn_window_diff
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise' C' Z') (hδ : 0 ≤ δ)
    (hs : s ∈ Icc (0 : ℝ) T) (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) :
    ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s)).GammaDiffBoundNearOn
      ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate (restartPoint s))
      (gamma κ) δ 1 hairerTimeWindow := by
  rw [gammaBoundNearOn_translate_iff_diff, hairerTimeWindow_eq_timeStrip,
    image_add_restartPoint_timeStrip]
  refine gammaBoundNearOn_timeStrip_of_periodic_diff
    (canonicalRenormalisedModel_gammaSpatialPeriodic N κ noise Cg q hg C)
    (canonicalRenormalisedModel_gammaSpatialPeriodic N κ noise' Cg' q' hg' C') ?_
    ((canonical_gammaDiffBoundOn_box_diff hZ hZ' hδ h).toNear 1)
  intro z w h1 h2 h1' h2' h3 hzw
  have hz := mem_phi43Box_of_cell (a := -1 + s) (b := 2 + s) (T := T)
    (by linarith [hs.1]) (by linarith [hs.2]) h1 h2 h3
  refine ⟨hz, ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, fun i _ => ?_⟩⟩
  have := abs_le.1 ((abs_sub_le_parabolicNorm z w i).trans hzw)
  have hi := h3 i
  exact ⟨by linarith [hi.1, hi.2], by linarith [hi.1, hi.2]⟩

section Compat

variable {M₁ M₂ : Model (phi43RegularityStructure κ) parabolicSemigroup}
  {M₁' M₂' : Model (phi43RegularityStructureF κ) parabolicSemigroup}

private theorem not_lt_planted_diff {γ' : ℝ} (hγ : γ' ≤ 3 / 2 - 5 * κ.1) (p : Phi43PlantSource) :
    ¬ phi43DegreeF κ (.planted p) < γ' := fun h =>
  absurd (lt_of_lt_of_le h hγ) (not_lt.2 (phi43DegreeF_planted_ge κ p))

/-- Below the planted symbols the `Π`-differences of compatible enlarged models are those of the
old models. -/
theorem EnlargedCompat.piDiffBoundOn_diff (hC₁ : EnlargedCompat κ M₁ M₁')
    (hC₂ : EnlargedCompat κ M₂ M₂') {γ' C : ℝ} (hγ : γ' ≤ 3 / 2 - 5 * κ.1)
    {S : Set ParabolicSpace} (h : M₁.PiDiffBoundOn M₂ γ' C S) :
    M₁'.PiDiffBoundOn M₂' γ' C S := by
  intro j hj t ht x hx
  cases j with
  | planted p => exact absurd hj (not_lt_planted_diff hγ p)
  | old τ =>
      rw [hC₁.regPi_single, hC₂.regPi_single]
      exact h τ hj t ht x hx

/-- Below the planted symbols the near-pair `Γ`-differences of compatible enlarged models are
those of the old models. -/
theorem EnlargedCompat.gammaDiffBoundNearOn_diff (hC₁ : EnlargedCompat κ M₁ M₁')
    (hC₂ : EnlargedCompat κ M₂ M₂') {γ' C R : ℝ} (hγ : γ' ≤ 3 / 2 - 5 * κ.1)
    {S : Set ParabolicSpace} (h : M₁.GammaDiffBoundNearOn M₂ γ' C R S) :
    M₁'.GammaDiffBoundNearOn M₂' γ' C R S := by
  intro i j hi hji x hx y hy hxy
  cases i with
  | planted p => exact absurd hi (not_lt_planted_diff hγ p)
  | old τ =>
      cases j with
      | planted p => exact absurd (hji.trans hi) (not_lt_planted_diff hγ p)
      | old σ =>
          rw [hC₁.gammaMap_single_old, hC₂.gammaMap_single_old]
          exact h τ σ hi hji x hx y hy hxy

end Compat

end RegularityStructures.Phi43.Restart

end

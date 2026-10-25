/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Slab
public import Phi43.Restart.NearBridge
public import Phi43.FixedPointF.WindowNear
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The quantitative per-model hypotheses of `phi43FixedPointF_window_nearOne` at a restart

`restart_quantitative`: let `Z` satisfy `IsRenormalisedCanonicalModel N κ noise C` with
`phi43Size κ η T Z ψ ≤ ofReal B`, `s ∈ [0, T]`, and let `M'` be a model of the *enlarged*
structure that is compatible (`EnlargedCompat`, interface item (C)) with the time translate by
`(s, 0)` of the renormalised canonical model of `noise` (the translation and the spatial
periodicity (P) are used on the old model, `Restart.Periodic`), realises the kernel for
`phi43IntegrationF` on the `Ξ`-free block at level `κ` (R) and has a qualitative growth model (G).
Then, with constants depending only on `(κ, N, B)` (`CPi = CGam₁ = B`,
`CΓ₁ = restartGammaConst c B`):

* `Π`-bound at level `κ` on `hairerTimeWindow` (constant `B`),
* near-`1` `Γ`-bound at level `κ` on `hairerTimeWindow` (constant `B`),
* near-`1` `Γ`-bounds on `timeSlab T'`, `T' ≤ 1`, at the levels `gamma κ`, `gamma κ + α`,
  `gamma κ + α + α + 2` (constant `restartGammaConst c B`).

Together with the explicit hypotheses (realising, growth, joint measurability) these are exactly
the per-model hypotheses of `phi43FixedPointF_window_nearOne`.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Restart

open RegularityStructures.Phi43.LiftBounds

/-- The constant of the Hairer estimate `(5.18)` for the integrals of the sources. -/
@[expose] def extConst (c B : ℝ) : ℝ :=
  c * (1 + B * max (gammaChainConst (Fintype.card SymbolF) B 16) 1) *
    max (gammaChainConst (Fintype.card SymbolF) B 16) 1

/-- The near-`1` `Γ`-constant `CΓ₁` on the slab. -/
@[expose] def restartGammaConst (c B : ℝ) : ℝ :=
  max (oldGammaConst (max 1 (extConst c B))) (extConst c B)

theorem gamma_add_alpha_add_alpha (κ : Kappa) : gamma κ + phi43Alpha κ + phi43Alpha κ = κ.1 := by
  simp only [gamma, phi43Alpha]; ring

theorem extConst_nonneg {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) : 0 ≤ extConst c B := by
  unfold extConst
  have h1 : 1 ≤ max (gammaChainConst (Fintype.card SymbolF) B 16) 1 := le_max_right _ _
  exact mul_nonneg (mul_nonneg hc (add_nonneg zero_le_one (mul_nonneg hB (zero_le_one.trans h1))))
    (zero_le_one.trans h1)

variable {κ : Kappa}

/-- The conclusion of `restart_quantitative`: the quantitative per-model hypotheses of
`phi43FixedPointF_window_nearOne` with `CPi = CGam₁ = B` and `CΓ₁ = restartGammaConst c B`. -/
@[expose] def RestartConclusion (κ : Kappa) (c B : ℝ)
    (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup) : Prop :=
  M'.PiBoundOn (gamma κ + phi43Alpha κ + phi43Alpha κ) B hairerTimeWindow ∧
  M'.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) B 1 hairerTimeWindow ∧
  ∀ {T' : ℝ}, T' ≤ 1 →
    M'.GammaBoundNearOn (gamma κ) (restartGammaConst c B) 1 (timeSlab T') ∧
    M'.GammaBoundNearOn (gamma κ + phi43Alpha κ) (restartGammaConst c B) 1 (timeSlab T') ∧
    M'.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ + 2)
      (restartGammaConst c B) 1 (timeSlab T')

/-- The qualitative model hypotheses (R) realising and (G) growth of the enlarged model at level
`κ`. -/
@[expose] def RestartQualitative (κ : Kappa) (N : ℕ)
    (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup) : Prop :=
  M'.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
    (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF) ∧
  ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
    M'.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q

theorem restart_quantitative (N : ℕ) (hN : 3 ≤ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ}, 0 ≤ B → ∀ {η T s : ℝ} {ψ : ℝ → C(Torus3, ℝ)}
      {noise : CanonicalNoise} {Cg : ℝ} {q : ℕ}
      {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
      {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup},
      Statements.IsRenormalisedCanonicalModel N κ noise C Z → s ∈ Icc (0 : ℝ) T →
      Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
      ∀ (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup),
      EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s))
        M' → RestartQualitative κ N M' → RestartConclusion κ c B M' := by
  obtain ⟨c, hc0, hc⟩ := exists_extGamma_const (κ := κ) N
  refine ⟨c, hc0, fun {B} hB η T s ψ noise Cg q hg C Z hZ hs hsize M' hC hQ => ?_⟩
  obtain ⟨hreal, hgr⟩ := hQ
  unfold RestartConclusion
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  rw [gamma_add_alpha_add_alpha] at hreal hgr ⊢
  have hlev : κ.1 ≤ 3 / 2 - 5 * κ.1 := by linarith
  have hPi : M'.PiBoundOn κ.1 B hairerTimeWindow :=
    hC.piBoundOn hlev (restart_canonical_piBoundOn_window hZ hB hs hsize)
  have hGam : M'.GammaBoundNearOn κ.1 B 1 hairerTimeWindow :=
    hC.gammaBoundNearOn hlev (Model.GammaBoundNearOn.mono_degree
      (restart_canonical_gammaBoundNearOn_window hZ hB hs hsize) (by simp only [gamma]; linarith))
  have S := extSetting hN hreal hgr hB hPi hGam
  have hE : 0 ≤ extConst c B := extConst_nonneg hc0 hB
  have hslab := fun {T' : ℝ} (hT' : T' ≤ 1) =>
    gammaBoundNearOn_kappa_add_two (E := extConst c B) hE hC
      (fun i hi x y hx hy hxy j hj => hc M' S i hi hx hy hxy j hj) hT'
  refine ⟨hPi, hGam, fun {T'} hT' => ?_⟩
  have h2 := hslab hT'
  have hmono : ∀ γ : ℝ, γ ≤ κ.1 + 2 →
      M'.GammaBoundNearOn γ (restartGammaConst c B) 1 (timeSlab T') := fun γ hγ =>
    Model.GammaBoundNearOn.mono_degree h2 hγ
  refine ⟨hmono _ ?_, hmono _ ?_, ?_⟩
  · simp only [gamma]; linarith
  · simp only [gamma, phi43Alpha]; linarith
  · exact h2

end RegularityStructures.Phi43.Restart

end

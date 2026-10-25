/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Persistence.Realising
public import Phi43.Reconstruction.Setting
public import Phi43.Composition.Consts

/-!
# The bundle `Phi43NearHyp` of the enlarged restarted model

`nearHyp_of_restart`: for a lift `Z` of size `phi43Size ≤ B`, a restart time `s ∈ [0, T]` and an
enlarged model `M'` that is `EnlargedCompat` with the time translate of the renormalised canonical
model, realises the kernel at level `κ`, has a growth model and is jointly measurable, the
per-model hypotheses `Phi43NearHyp` of the identification at a restart hold, with
`CPi = CGam₁ = B` and `CΓ₁ = restartGammaConst c B` (the constant `c` of
`Restart.restart_quantitative`), on every slab `timeSlab T'`, `0 < T' ≤ 1`.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Persistence

open RegularityStructures.Phi43.Restart

theorem nearHyp_of_restart {κ : Kappa} (N : ℕ) (hN : 3 ≤ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ}, 0 ≤ B → ∀ {η T s : ℝ} {ψ : ℝ → C(Torus3, ℝ)}
      {noise : CanonicalNoise} {Cg : ℝ} {q : ℕ}
      {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
      {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup},
      Statements.IsRenormalisedCanonicalModel N κ noise C Z → s ∈ Icc (0 : ℝ) T →
      Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
      ∀ {T' : ℝ}, 0 < T' → T' ≤ 1 →
      ∀ (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup),
      EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
        (LiftBounds.restartPoint s)) M' → RestartQualitative κ N M' → M'.IsJointMeasurable →
      Phi43NearHyp κ N M' B (gammaChainConst (Fintype.card SymbolF) B 16)
        (gammaChainConst (Fintype.card SymbolF) (restartGammaConst c B) 16) B
        (restartGammaConst c B) T' := by
  obtain ⟨c, hc0, hc⟩ := restart_quantitative (κ := κ) N hN
  refine ⟨c, hc0, fun {B} hB {η T s ψ noise Cg q hg C Z} hZ hs hsize {T'} hT0 hT1 M' hC hQ hJ => ?_⟩
  obtain ⟨hPi, hGam, hslab⟩ := hc hB hZ hs hsize M' hC hQ
  obtain ⟨g0, g1, gK⟩ := hslab hT1
  exact
    { pi := hPi
      gam := hGam
      chain := le_rfl
      growth := hQ.2
      cPi := hB
      joint := hJ
      real := hQ.1
      gamBase := g0
      gamShift := g1
      gK := gK
      chainΓ := le_rfl
      cΓ := Composition.gammaChainConst_nonneg' _ _ _
      hT0 := hT0
      hT1 := hT1 }

end RegularityStructures.Phi43.Persistence

end

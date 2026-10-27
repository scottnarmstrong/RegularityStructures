module

public import GlobalPhi43.Attachment.ModelTestBoundReal
public import GlobalPhi43.Attachment.Realisation
public import Phi43.Structure.CanonicalSmoothGrowth
public import Phi43.BPHZ.CanonicalBridgeConvolution

/-! Compact-test estimates for the actual J of a smooth growing
noise and its moderate model. Constants precede every realisation datum. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 MeasureTheory Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probe_C4_sup_le {φ : ParabolicSpace → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ A) :
    (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ : ENNReal).toReal ≤ A := by
  have hh : (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ : ENNReal) ≤
      ENNReal.ofReal A := by
    refine iSup₂_le fun k hk => iSup_le fun z => ?_
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hb k (by
      have := Finset.mem_range.mp hk
      omega) z)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hA)

theorem probeJ_polyBounded {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) :
    PolyBounded (fun z => treeJ N f (spaceTimeProj z)) := by
  obtain ⟨noise, hn, _⟩ := hZ
  obtain ⟨Cg, q, hgr⟩ := hg
  have he : noise.zeta = fun z => f (spaceTimeProj z) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z)^q := by
    rw [he]
    exact hgr
  have hp : PolyBounded (fun z => f (spaceTimeProj z)) := by
    rw [← he]
    exact canonicalNoise_polyBounded_of_derivatives noise Cg q hg'
  have hh := polyBounded_hairerConvolution N hf hp
  have hj : hairerConvolution N (fun z => f (spaceTimeProj z)) =
      fun z => treeJ N f (spaceTimeProj z) := by
    funext z
    exact hairerConvolution_comp_proj_eq N (IsSmoothOnSpaceTime.continuous hf) z
  change PolyBounded (hairerConvolution N (fun z => f (spaceTimeProj z))) at hh
  rwa [hj] at hh

/-- An explicit derivative allowance replaces the literal supremum, but the
field, its growth, and its model realisation are all proved from source data. -/
theorem probeJ_compact_test (N : ℕ) (κ : Kappa) : ∃ c : ℝ, 0 < c ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S → ∀ z ∈ S, ∀ T ∈ Ioc (0 : ℝ) 1,
    ∀ φ : ParabolicSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {v | Local.pdist 0 v ≤ 1} →
    ∀ A : ℝ, 0 ≤ A → (∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k φ v‖ ≤ A) →
    |∫ w, treeJ N f (spaceTimeProj w) * rescaledTestFunction φ T z w| ≤
      c*A*(1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, Local.pdist z y ≤ 3}).toReal)^3 *
        T^homogeneity κ .psi := by
  obtain ⟨c, hc, hb⟩ := modelTestBound_real N κ
  refine ⟨c, hc, ?_⟩
  intro f C Z hf hg hZ S hS z hz T hT φ hφ hφc hφs A hA ha
  obtain ⟨_, Cg, q, hgr⟩ := probeJ_polyBounded hf hg hZ
  have hη : homogeneity κ .psi < 0 := by
    simp only [homogeneity]
    linarith [kappa_pos κ]
  have hh := hb f C Z hZ hg S hS z hz T hT φ hφ hφc hφs .psi hη
    (fun w => treeJ N f (spaceTimeProj w))
    ((continuous_treeJ hf).comp continuous_spaceTimeProj) ⟨Cg, q, hgr⟩
    (fun u hu y => (realise hf hg hZ z hu y).2.1)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (probe_C4_sup_le hA ha) hc.le)
      (by positivity)) (Real.rpow_nonneg hT.1.le _))

end GlobalPhi43.Attachment

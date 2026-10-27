module

public import GlobalPhi43.Attachment.ModelTestBoundReal

/-! The model test bound in extended-norm arithmetic. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local
open scoped NNReal ENNReal

open scoped ContDiff in
/-- Uniform C4 conversion in extended-norm form, with the noise-growth hypothesis. -/
theorem model_test_bound (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ≥0, ∃ m₀ : ℕ,
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f₀ C Z → Statements.HasPhi43NoiseGrowth f₀ →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ x ∈ S, ∀ T ∈ Set.Ioc (0 : ℝ) 1,
    ∀ φ : ParabolicSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {z | pdist 0 z ≤ 1} →
    ∀ τ : Symbol, homogeneity κ τ < 0 →
    ∀ f : ParabolicSpace → ℝ, Continuous f →
      (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) →
      (∀ r, 0 < r → ∀ y, Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r f y) →
      ENNReal.ofReal |∫ y, f y * rescaledTestFunction φ T x y| ≤
        (c : ENNReal) * (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ) *
          (1 + Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}) ^ m₀ *
            ENNReal.ofReal (T ^ homogeneity κ τ) := by
  obtain ⟨c, hc, hbound⟩ := modelTestBound_real N κ
  refine ⟨⟨c, hc.le⟩, 3, ?_⟩
  intro f₀ C Z hZ hg S hS x hx T hT φ hφ hφc hφs τ hτ f hf hfg hreal
  have h := ENNReal.ofReal_le_ofReal
    (hbound f₀ C Z hZ hg S hS x hx T hT φ hφ hφc hφs τ hτ f hf hfg hreal)
  have hA := (four_derivative_supremum_bound hφ hφc).1
  have hM : Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3} ≠ ⊤ := by
    obtain ⟨noise, hn, hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement hS (by norm_num : (0 : ℝ) ≤ 3))
  rw [ENNReal.ofReal_mul' (Real.rpow_nonneg hT.1.le _),
    ENNReal.ofReal_mul' (pow_nonneg (by positivity) 3), ENNReal.ofReal_mul hc.le,
    ENNReal.ofReal_toReal hA, ENNReal.ofReal_pow (by positivity) 3,
    ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_toReal hM] at h
  have hc' : ENNReal.ofReal c = ENNReal.ofNNReal ⟨c, hc.le⟩ := by
    exact ENNReal.ofReal_eq_coe_nnreal hc.le
  rwa [hc'] at h

end GlobalPhi43.Attachment

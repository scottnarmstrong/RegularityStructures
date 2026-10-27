module

public import GlobalPhi43.Attachment.ModelTestBound
public import GlobalPhi43.Attachment.RescaleFormula
public import GlobalPhi43.MW20.Setting.ParabolicRescale
public import GlobalPhi43.MW20.Setting.ParabolicClosedNbhd
public import GlobalPhi43.MW20.Setting.C4Norm

/-! Model bounds tested against smooth functions, in expanded and rescaled notation. -/

public section

namespace GlobalPhi43

section Expanded

open MeasureTheory RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local
open scoped NNReal ENNReal ContDiff

/-- Test-function conversion in expanded form, with radius three and a uniform polynomial bound. -/
theorem modelTestBound_expanded :
    ∀ (N : ℕ) (κ : Kappa), ∃ (c : ℝ≥0) (m₀ : ℕ),
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f₀ C Z → Statements.HasPhi43NoiseGrowth f₀ →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ x ∈ S, ∀ T ∈ Set.Ioc (0 : ℝ) 1,
    ∀ φ : ParabolicSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {y | ∃ z ∈ ({0} : Set ParabolicSpace), pdist z y ≤ 1} →
    ∀ τ : Symbol, (phi43RegularityStructure κ).deg τ < 0 →
    ∀ f : ParabolicSpace → ℝ, Continuous f →
      (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) →
      (∀ r, 0 < r → ∀ y, Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r f y) →
      ENNReal.ofReal |∫ y, f y *
        (T ^ (-5 : ℤ) * φ ((y - x).1 / T ^ 2, T⁻¹ • (y - x).2))| ≤
        (c : ENNReal) * (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ) *
          (1 + Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}) ^ m₀ *
            ENNReal.ofReal (T ^ (phi43RegularityStructure κ).deg τ) := by
  intro N κ
  obtain ⟨c, m₀, h⟩ := Attachment.model_test_bound N κ
  refine ⟨c, m₀, ?_⟩
  intro f₀ C Z hZ hg S hS x hx T hT φ hφ hφc hφs τ hτ f hf hfg hreal
  have hs : tsupport φ ⊆ {z | pdist 0 z ≤ 1} := by simpa only [Set.mem_singleton_iff,
    exists_eq_left, Set.mem_ofPred_eq] using hφs
  simpa only [Attachment.rescaledTestFunction_formula, phi43RegularityStructure_deg] using
    h f₀ C Z hZ hg S hS x hx T hT φ hφ hφc hs τ hτ f hf hfg hreal

end Expanded

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff
open RegularityStructures RegularityStructures.Phi43

/-- Test-function conversion using `parabolicClosedNbhd`, `parabolicRescale` and `c4Norm`.
This is definitionally the expanded form `modelTestBound_expanded`. -/
theorem modelTestBound :
    ∀ (N : ℕ) (κ : Kappa), ∃ (c : ℝ≥0) (m₀ : ℕ),
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ f₀ C Z →
      RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f₀ →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ x ∈ S, ∀ T ∈ Ioc (0 : ℝ) 1,
    ∀ φ : ParabolicSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ parabolicClosedNbhd {0} 1 →
    ∀ (τ : Symbol), (phi43RegularityStructure κ).deg τ < 0 →
    ∀ f : ParabolicSpace → ℝ, Continuous f →
      (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) →
      (∀ r : ℝ, 0 < r → ∀ y, Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r f y) →
      ENNReal.ofReal |∫ y, f y * parabolicRescale φ T (y - x)| ≤
        (c : ℝ≥0∞) * c4Norm φ * (1 + Z.normOn (RegularityStructures.Phi43.gamma κ)
            (parabolicClosedNbhd S 3)) ^ m₀ *
          ENNReal.ofReal (T ^ (phi43RegularityStructure κ).deg τ) :=
  modelTestBound_expanded

end GlobalPhi43

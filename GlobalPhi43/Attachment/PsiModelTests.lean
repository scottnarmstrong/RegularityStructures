module

public import GlobalPhi43.Attachment.PsiProfile
public import GlobalPhi43.Attachment.ModelTestBoundReal

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20
open scoped ContDiff

/-- The actual infinite-kernel test of every negative model realisation, over
all source scales with one constant chosen before model/noise/domain data. -/
theorem psi_model_test_bound (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f₀ C Z → Statements.HasPhi43NoiseGrowth f₀ →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ x ∈ S, ∀ (T : ℝ) (hT : T ∈ Set.Ioc (0 : ℝ) 1),
    ∀ τ : Symbol, homogeneity κ τ < 0 →
    ∀ f : ParabolicSpace → ℝ, Continuous f → PolyBounded f →
      (∀ r, 0 < r → ∀ y, Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r f y) →
      |infinitePastSmooth Φ hΦ T hT.1 f x| ≤
        K * (1 + (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal)^3 *
          T ^ homogeneity κ τ := by
  obtain ⟨c,hc,hbound⟩ := modelTestBound_real N κ
  let A := (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k (psiProfile Φ hΦ) z‖ₑ : ENNReal).toReal
  refine ⟨c*(A+1),mul_pos hc (by dsimp [A]; positivity),?_⟩
  intro f₀ C Z hZ hg S hS x hx T hT τ hτ f hf hfg hreal
  obtain ⟨_,B,q,hgrowth⟩ := hfg
  have hb := hbound f₀ C Z hZ hg S hS x hx T hT (psiProfile Φ hΦ)
    (psiProfile_contDiff Φ hΦ) (psiProfile_hasCompactSupport Φ hΦ)
    (fun z hz => (psiProfile_tsupport Φ hΦ hz).2) τ hτ f hf ⟨B,q,hgrowth⟩ hreal
  rw [infinitePastSmooth_eq_profile_test Φ hΦ hT.1 hT.2]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT.1.le _)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) 3)
  exact mul_le_mul_of_nonneg_left (by change A ≤ A+1; linarith) hc.le

end GlobalPhi43.Attachment

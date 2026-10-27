module

public import GlobalPhi43.Attachment.PsiModelTests
public import GlobalPhi43.MW20.KernelNegativeSeminorms

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- From actual model realisations to the actual extended MW20 testing
supremum. The exponent cancels exactly at every positive source scale. -/
theorem psi_test_seminorm (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f₀ C Z → Statements.HasPhi43NoiseGrowth f₀ →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ (I : Set ℝ), I ⊆ Ioc 0 1 →
    ∀ τ : Symbol, homogeneity κ τ < 0 →
    ∀ G : ParabolicSpace → ParabolicSpace → ℝ,
      (∀ x ∈ S, Continuous (G x) ∧ PolyBounded (G x)) →
      (∀ x ∈ S, ∀ r, 0 < r → ∀ y,
        Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r (G x) y) →
      localTestSeminorm (mw20TestingKernel Φ hΦ) S I (homogeneity κ τ) G ≤
        ENNReal.ofReal (K * (1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal)^3) := by
  obtain ⟨K,hK,hbound⟩ := psi_model_test_bound N κ Φ hΦ
  refine ⟨K,hK,?_⟩
  intro f₀ C Z hZ hg S hS I hI τ hτ G hG hreal
  apply (localTestSeminorm_le_iff _ _ _ _ _ (by positivity)).mpr
  intro x hx t htI
  have ht := hI htI
  rw [mw20TestingKernel_pos Φ hΦ ht.1,
    reconstruction_pastSmooth_eq_density Φ hΦ ht.1 ht.2]
  have hb := hbound f₀ C Z hZ hg S hS x hx t ht τ hτ (G x)
    (hG x hx).1 (hG x hx).2 (hreal x hx)
  have hi : t ^ (-homogeneity κ τ) * t ^ homogeneity κ τ = 1 := by
    rw [← Real.rpow_add ht.1, neg_add_cancel, Real.rpow_zero]
  calc
    _ ≤ t ^ (-homogeneity κ τ) *
        (K*(1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal)^3 *
          t ^ homogeneity κ τ) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.1.le _)
    _ = (K*(1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal)^3) *
        (t ^ (-homogeneity κ τ) * t ^ homogeneity κ τ) := by ring
    _ = _ := by rw [hi, mul_one]

end GlobalPhi43.Attachment

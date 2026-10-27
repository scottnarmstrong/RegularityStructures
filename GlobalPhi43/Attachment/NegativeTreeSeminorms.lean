module

public import GlobalPhi43.Attachment.PsiTestSeminorms
public import GlobalPhi43.Attachment.SourceTreeRegularity

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- Source seminorm bounds for all scalar negative tree realisations.
The literal tree formulas and their polynomial growth are discharged internally. -/
theorem source_negative_tree_seminorm (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ (I : Set ℝ), I ⊆ Ioc 0 1 →
    ∀ τ : Symbol, τ ∈ fMinus → (∀ i, τ ≠ .psiSqX i) →
      localTestSeminorm (mw20TestingKernel Φ hΦ) S I (homogeneity κ τ)
        (fun x y => hairerTreeField N (fun _ : Unit => f) (C₁ C) (C₂ C)
          (spaceTimeProj x) () τ (spaceTimeProj y)) ≤
        ENNReal.ofReal K * (1+Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3})^3 := by
  obtain ⟨K,hK,hbound⟩ := psi_test_seminorm N κ Φ hΦ
  refine ⟨K,hK,?_⟩
  intro f C Z hf hg hZ S hS I hI τ hτ hX
  have hneg : homogeneity κ τ < 0 :=
    (homogeneity_neg_iff_isFMinus κ τ).mpr ((mem_fMinus_iff_isFMinus τ).mp hτ)
  have hh := hbound f C Z hZ hg S hS I hI τ hneg _
    (fun x _ => source_tree_regular hf hg hZ τ hτ hX x) (by
      intro x _ r hr y
      obtain ⟨noise,hn,_,hreal⟩ := regPi_fMinus hZ
      rw [hreal τ hτ x r hr y,
        CanonicalData.hairerCanonicalData_renormalisedPi_basis_eq_treeField
          (ξ := fun _ : Unit => f) (ω := ()) C x (noise_zeta_eq hn) hf hτ hX])
  have hfin : Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3} ≠ ⊤ := by
    obtain ⟨noise,hn,hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement hS (by norm_num : (0 : ℝ) ≤ 3))
  convert hh using 1
  rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hfin]

end GlobalPhi43.Attachment

module

public import GlobalPhi43.Attachment.DefectFields

/-! Derivative bounds for the three actual source defects. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity GlobalPhi43.Local
open scoped ContDiff

private theorem ddA_neg_fun (l : List (Fin 4)) (f : ParabolicSpace → ℝ) :
    ddA l (-f) = -ddA l f := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change ddv j (ddA l (-f)) = -ddv j (ddA l f)
    rw [ih]
    funext z
    simp [ddv, fderiv_neg]

/-- Every derivative word of every source defect is controlled by the compact model norm.
The constant precedes all noise, constants, models, sets, base points and defect indices. -/
theorem defect_derivative_bound (N : ℕ) (κ : Kappa) (l : List (Fin 4)) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S → ∀ x ∈ S, ∀ i : Fin 3,
      |ddA l (defectField N f C i) x| ≤
        c * (1 + (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal) ^ 3 := by
  obtain ⟨c, hc, h⟩ := remainder_derivative_bound N κ l
  refine ⟨c, hc, ?_⟩
  intro f C Z hf hg hZ S hS x hx i
  obtain ⟨hcont, _, B, q, hb⟩ := defectInput_regular hf hg hZ i
  have hτ : homogeneity κ (![Symbol.noise, .psiSq, .psiCube] i) < 0 := by
    have hp := κ.2.1
    fin_cases i <;> norm_num [homogeneity] <;> linarith
  have he := h f C Z hZ hg S hS x hx (![Symbol.noise, .psiSq, .psiCube] i) hτ
    (defectInput N f C i) hcont ⟨B, q, hb⟩
    (fun u hu y => defectInput_realise hf hg hZ i x hu y)
  simpa only [defectField, ddA_neg_fun, Pi.neg_apply, abs_neg] using he

end GlobalPhi43.Attachment

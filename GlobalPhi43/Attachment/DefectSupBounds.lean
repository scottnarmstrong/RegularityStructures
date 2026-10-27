module

public import GlobalPhi43.Attachment.DefectNorms
public import GlobalPhi43.MW20.ScalarSupNorm

/-! Attach the exact sup-norm defect entries to the proved C1 bound. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Local MW20
open RegularityStructures.Inhomogeneity

/-- The source functional uses only the scalar sup part of the proved C1 norm. -/
theorem scalarSup_le_defectC1ENorm (e : ParabolicSpace → ℝ) (S : Set ParabolicSpace) :
    localScalarSup e S ≤ defectC1ENorm e S := by
  apply iSup₂_le
  intro x hx
  exact le_iSup₂_of_le x hx (ENNReal.ofReal_le_ofReal (by
    have ht := abs_nonneg (ddv 0 e x)
    have hx := norm_nonneg (fun j : Fin 3 => ddv j.succ e x)
    linarith only [ht, hx]))

/-- Uniform actual defect sup bounds, with the constant before all source data. -/
theorem defect_sup_bounds (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S → ∀ i : Fin 3,
      localScalarSup (defectField N f C i) S ≤ ENNReal.ofReal (c * (1 +
        (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 4}).toReal) ^ 3) := by
  obtain ⟨c, hc, h⟩ := defect_norms N κ
  refine ⟨c, hc, ?_⟩
  intro f C Z hf hg hZ S hS i
  exact (scalarSup_le_defectC1ENorm _ _).trans
    ((Finset.single_le_sum (f := fun i : Fin 3 => defectC1ENorm (defectField N f C i) S)
      (fun _ _ => bot_le) (Finset.mem_univ i)).trans (h f C Z hf hg hZ S hS))

end GlobalPhi43.Attachment

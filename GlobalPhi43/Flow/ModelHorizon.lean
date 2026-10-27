module

public import GlobalPhi43.Flow.DyadicLiftData

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- Horizon inclusion for the literal model boxes. -/
theorem phi43Box_mono {T U : ℝ} (hTU : T ≤ U) :
    Statements.phi43Box T ⊆ Statements.phi43Box U := by
  rintro z ⟨ht, hx⟩
  exact ⟨⟨ht.1, by linarith [ht.2]⟩, hx⟩

theorem phi43NoiseSize_mono_horizon (η : ℝ) {T U : ℝ} (hTU : T ≤ U)
    (ψ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseSize η T ψ ≤ Statements.phi43NoiseSize η U ψ := by
  refine iSup₂_le fun r hr => ?_
  exact le_iSup₂_of_le r ⟨hr.1, by linarith [hr.2]⟩ le_rfl

theorem phi43NoiseDist_mono_horizon (η : ℝ) {T U : ℝ} (hTU : T ≤ U)
    (ψ χ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseDist η T ψ χ ≤ Statements.phi43NoiseDist η U ψ χ := by
  refine iSup₂_le fun r hr => ?_
  exact le_iSup₂_of_le r ⟨hr.1, by linarith [hr.2]⟩ le_rfl

/-- Monotonicity retains the full model-plus-potential size and its exact horizon. -/
theorem phi43Size_mono_horizon (κ : Kappa) (η : ℝ) {T U : ℝ} (hTU : T ≤ U)
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup) (ψ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43Size κ η T Z ψ ≤ Statements.phi43Size κ η U Z ψ :=
  add_le_add (model_normOn_mono Z _ (phi43Box_mono (by linarith : T + 1 ≤ U + 1)))
    (phi43NoiseSize_mono_horizon η hTU ψ)

/-- Monotonicity retains the literal full model-plus-potential distance. -/
theorem phi43Dist_mono_horizon (κ : Kappa) (η : ℝ) {T U : ℝ} (hTU : T ≤ U)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ χ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43Dist κ η T Z Z' ψ χ ≤ Statements.phi43Dist κ η U Z Z' ψ χ :=
  add_le_add (Model.diffNormOn_mono_set (phi43Box_mono (by linarith : T + 1 ≤ U + 1)))
    (phi43NoiseDist_mono_horizon η hTU ψ χ)

/-- Integer-horizon information on the fixed event controls every real horizon on the same
reference dyadic tail. No new event, allowance or Cauchy premise is introduced. -/
theorem modelConvergenceEvent_realHorizon {Ω : Type*} {κ : Kappa} (α : ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) {ω : Ω}
    (hω : ω ∈ modelConvergenceEvent α Z ψ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ n, Statements.phi43Size κ α R (Z (dyadicTailScale n) ω)
        (ψ (dyadicTailScale n) ω) ≤ ENNReal.ofReal B) ∧
      ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        Statements.phi43Dist κ α R (Z (dyadicTailScale n) ω) (Z (dyadicTailScale m) ω)
          (ψ (dyadicTailScale n) ω) (ψ (dyadicTailScale m) ω) ≤ ENNReal.ofReal δ := by
  obtain ⟨H, hH⟩ := exists_nat_ge R
  have hRH : R ≤ (H : ℝ) := hH
  have hH1 : 1 ≤ H := by exact_mod_cast hR.trans hH
  obtain ⟨hC, B, hB⟩ := hω H hH1
  refine ⟨max 1 B, le_max_left _ _, ?_, ?_⟩
  · intro n
    rw [dyadicTailScale_eq]
    exact (phi43Size_mono_horizon κ α hRH _ _).trans
      ((hB (n + 1)).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
  · intro δ hδ
    obtain ⟨n₀, hn₀⟩ := hC δ hδ
    refine ⟨n₀, fun n hn m hm => ?_⟩
    rw [dyadicTailScale_eq, dyadicTailScale_eq]
    exact (phi43Dist_mono_horizon κ α hRH _ _ _ _).trans
      (hn₀ (n + 1) (by omega) (m + 1) (by omega))

end GlobalPhi43.Flow

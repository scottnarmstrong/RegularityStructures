module

public import GlobalPhi43.Flow.LocalAssembly

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Actual smooth deterministic lift data. No solution or convergence property is a field. -/
structure LiftData (N : ℕ) (κ : Kappa) where
  forcing : SpaceTime → ℝ
  constants : RenormalisationConstants
  model : Model (phi43RegularityStructure κ) parabolicSemigroup
  potential : ℝ → C(Torus3, ℝ)
  moderate : Statements.IsModeratePhi43Lift N κ forcing constants model potential

theorem LiftData.shiftSmooth {N : ℕ} {κ : Kappa} (a : LiftData N κ) (s : ℝ) :
    IsSmoothOnSpaceTime (shiftForcing s a.forcing) :=
  smooth_of_moderateLift (moderateLift_time_translate a.moderate s)

/-- A local chart for one lift and one start, with its actual classical agreement. -/
structure LocalChart {N : ℕ} {κ : Kappa} (η : NegExponent) (L τ : ℝ) (K : ℝ≥0)
    (a : LiftData N κ) (s : ℝ) where
  path : StateBall η L → C(Icc (0 : ℝ) τ, HolderBesov η)
  lipschitz : LipschitzWith K path
  smooth_agreement : ∀ x : smoothBall η L, path x.val =
    curveOnSmooth τ (3 * a.constants.1 - 9 * a.constants.2)
      (shiftForcing s a.forcing) (a.shiftSmooth s) x

theorem LocalChart.initial {N : ℕ} {κ : Kappa} {η : NegExponent} {L τ s : ℝ}
    {K : ℝ≥0} {a : LiftData N κ} (u : LocalChart η L τ K a s) (hτ : 0 ≤ τ) :
    ∀ x : StateBall η L, u.path x ⟨0, le_rfl, hτ⟩ = x.val :=
  ballExtension_initial hτ _ _ u.path u.lipschitz.continuous u.smooth_agreement

end GlobalPhi43.Flow

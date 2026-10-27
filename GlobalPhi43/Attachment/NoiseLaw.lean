module

public import GlobalPhi43.Attachment.GaussianLaw
public import GlobalPhi43.Attachment.NoiseTranslation
public import Phi43.Constants.Finite
public import Phi43.BPHZ.PsiGaussianVector

/-! Finite-dimensional law uniqueness and time stationarity of the regularised noise. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43

/-- White noises on different spaces have the same law on every finite L2 test family. -/
theorem whiteNoise_finite_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {W' : (SpaceTime → ℝ) → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {n : ℕ} (h : Fin n → SpaceTime → ℝ) (hh : ∀ i, MemLp (h i) 2) :
    P.map (fun ω i => W (h i) ω) = P'.map (fun ω i => W' (h i) ω) :=
  centredGaussianVector_map_eq (hW.2 n h hh) (hW'.2 n h hh)

end GlobalPhi43.Attachment

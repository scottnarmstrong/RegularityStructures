module

public import GlobalPhi43.Flow.WindowGeometry
public import Phi43.BPHZ.GModelsConvergenceAssembly
public import Phi43.BPHZ.BphzCauchyMoments
public import Phi43.BPHZ.ShiftedInputsAssembly
public import Phi43.Steps.RenormalisedCanonicalModel
public import Phi43.Steps.NoiseCauchy
public import Phi43.Stochastic.ConstantsComparisonLimits
public import RegularityStructures.Probability.ModelKolmogorov

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
  (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
  (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ))
  (hlift : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
    Statements.IsModeratePhi43Lift N κ (ξ ε ω)
      (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0) (Z ε ω) (ψ ε ω))

include W hW hκE N hN ρ hρ a ξ hξ hlift

/-- Compact-window moments at the renormalisation shift (a/3,0).
The stochastic estimates and positive shift rate follow from the model bounds.
The probability space and the reference families precede the existential constants. -/
theorem window_moments (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (k : ℝ) (hk : 18 ≤ k) :
    ∃ θ C Cs : ℝ, 0 < θ ∧ 0 ≤ C ∧ 0 ≤ Cs ∧
      SizeMoment P (fun ε ω => (Z ε ω).normOn (gamma κ) (windowSet k) +
        Statements.phi43NoiseSize η k (ψ ε ω)) Cs ∧
      MomentBound P (fun ε ε' ω =>
        (Z ε ω).diffNormOn (Z ε' ω) (gamma κ) (windowSet k) +
        Statements.phi43NoiseDist η k (ψ ε ω) (ψ ε' ω)) θ C ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).normOn (gamma κ) (windowSet k)) P ∧
        AEMeasurable (fun ω => Statements.phi43NoiseSize η k (ψ ε ω)) P) := by
  obtain ⟨L, C₀, θ', hθ', hr⟩ :=
    gModelsShift_rate_of_constantDifferencePowerRate constantDifferencePowerRate_holds N hρ (a / 3, 0)
  obtain ⟨Bc, hBc, -, -, -⟩ := gModels_constants constantsComparison_limits N hρ hρ (a / 3, 0)
  have hψ : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, IsMassivePotential (ξ ε ω) (ψ ε ω) :=
    fun ε hε => (hlift ε hε).mono fun _ hω => hω.2.2
  obtain ⟨θ₁, C₁, hθ₁, hC₁, hA, hE⟩ := gModels_bphzCauchy_moments
    renormalisedCanonicalModel_existsUnique kolmogorov_modelNorm phi43Noise_cauchy
    (shiftedBphzInputs_of_bphzCauchyMoments bphzCauchyMoments_holds)
    κ hκE N hN ρ ρ hρ hρ (a / 3, 0) hBc hBc (windowSet k) (isCompact_windowSet k)
    P W hW ξ ξ hξ hξ Z Z ψ ψ hlift hlift
  obtain ⟨θ₂, C₂, hθ₂, hC₂, hNs, hNd⟩ := gModels_noiseCauchy_moments
    phi43Noise_cauchy η hη ρ ρ hρ hρ k (by linarith) P W hW ξ ξ hξ hξ ψ ψ hψ hψ
  have hMB := momentBound_of_shiftRate hθ' hC₁ hr hE
  have hC₀ : 0 ≤ C₀ := by
    have h := hr 1 ⟨one_pos, le_rfl⟩
    rw [Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hCm : 0 ≤ C₁ * (1 + 2 * C₀) := by positivity
  exact ⟨min (min θ₁ θ') θ₂, C₁ * (1 + 2 * C₀) + C₂, C₁ + C₂,
    lt_min (lt_min hθ₁ hθ') hθ₂, add_nonneg hCm hC₂, add_nonneg hC₁ hC₂,
    hA.add hNs hC₁ hC₂, hMB.add hNd hCm hC₂,
    fun ε hε => ⟨(hA ε hε.1 hε.2).1, (hNs ε hε.1 hε.2).1⟩⟩

end GlobalPhi43.Flow

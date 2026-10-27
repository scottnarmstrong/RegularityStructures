module

public import GlobalPhi43.Flow.TranslatedInputs

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- The literal translated unit potential window in the every-start majorant. -/
def unitPotentialSize (η r : ℝ) (ψ : ℝ → C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ t ∈ Icc r (r + 1), holderBesovENorm η (ψ t)

/-- The polynomial right-hand side, kept extended-valued until finiteness is proved. -/
def windowMajorantRhs (c : ℝ) (κ : Kappa)
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → C(Torus3, ℝ)) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal c * (1 + Z.normOn (gamma κ) (majorantRegion r) +
    unitPotentialSize (lossExponent κ) r ψ) ^ 7

/-- A finite real envelope, with an explicit zero fallback outside literal E_win. -/
def windowMajorantEnvelope {Ω : Type*} (c : ℝ) {κ : Kappa}
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) (k : ℕ) (ω : Ω) : ℝ := by
  classical
  exact if ω ∈ windowEvent (lossExponent κ) Z ψ then
    c * (1 + (⨆ n : ℕ, (Z ((2⁻¹ : ℝ) ^ n) ω).normOn (gamma κ) (windowSet k)).toReal +
      (⨆ n : ℕ, potentialWindowSize (lossExponent κ) k (ψ ((2⁻¹ : ℝ) ^ n) ω)).toReal) ^ 7
    else 0

/-- One finite envelope controls every index and every real restart in the window. -/
theorem windowMajorantRhs_le_envelope {Ω : Type*} {κ : Kappa} (c : ℝ) (hc : 0 ≤ c)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) (k : ℕ) (hk : 18 ≤ k) {ω : Ω}
    (hω : ω ∈ windowEvent (lossExponent κ) Z ψ) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hrk : r ≤ k - 18) :
    windowMajorantRhs c κ (Z ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ n) ω) r ≤
      ENNReal.ofReal (windowMajorantEnvelope c Z ψ k ω) := by
  classical
  let X := ⨆ n : ℕ, (Z ((2⁻¹ : ℝ) ^ n) ω).normOn (gamma κ) (windowSet k)
  let Y := ⨆ n : ℕ, potentialWindowSize (lossExponent κ) k (ψ ((2⁻¹ : ℝ) ^ n) ω)
  have hX : X ≠ ⊤ := (hω k hk).1.ne
  have hY : Y ≠ ⊤ := (hω k hk).2.ne
  have hx : (Z ((2⁻¹ : ℝ) ^ n) ω).normOn (gamma κ) (majorantRegion r) ≤ X :=
    (majorant_model_norm_le _ _ hr hrk).trans
      (le_iSup (fun m : ℕ => (Z ((2⁻¹ : ℝ) ^ m) ω).normOn (gamma κ) (windowSet k)) n)
  have hy : unitPotentialSize (lossExponent κ) r (ψ ((2⁻¹ : ℝ) ^ n) ω) ≤ Y := by
    have hu : unitPotentialSize (lossExponent κ) r (ψ ((2⁻¹ : ℝ) ^ n) ω) ≤
        potentialWindowSize (lossExponent κ) k (ψ ((2⁻¹ : ℝ) ^ n) ω) :=
      iSup₂_le fun t ht => restart_potential_le _ _ _ hr hrk ht
    exact hu.trans (le_iSup (fun m : ℕ => potentialWindowSize (lossExponent κ) k
      (ψ ((2⁻¹ : ℝ) ^ m) ω)) n)
  have he : ENNReal.ofReal (c * (1 + X.toReal + Y.toReal) ^ 7) =
      ENNReal.ofReal c * (1 + X + Y) ^ 7 := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow,
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_toReal hX, ENNReal.ofReal_toReal hY]
    all_goals positivity
  rw [windowMajorantEnvelope, ite_eq_left hω]
  change ENNReal.ofReal c * (1 + _ + _) ^ 7 ≤ ENNReal.ofReal (c * (1 + X.toReal + Y.toReal) ^ 7)
  rw [he]
  gcongr

end GlobalPhi43.Flow

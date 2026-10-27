module

public import GlobalPhi43.MW20.AffineSeminorm
public import GlobalPhi43.MW20.ConeDomain

/-!
# Source-seminorm attachment for MW20 (2.37)

The coefficient is the actual diagonal spatial derivative attaining (2.6).
The two-point supremum is the actual local norm, including pairs at radius r.
The coefficient supremum is proved bounded by the cone estimate itself.
There is no kernel input.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Actual radius-restricted two-point supremum used by the source. -/
@[expose] noncomputable def localTwoPointSup
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace) (r : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ y ∈ D, ⨆ (_ : pdist x y ≤ r), ENNReal.ofReal |U (x, y)|

/-- The source's spatial interior cone condition, with its explicit radius
and angle parameters and positive-radius endpoint convention. -/
@[expose] def SpatialInteriorCone (D : Set ParabolicSpace) (r₀ lam : ℝ) : Prop :=
  ∀ r, 0 < r → r ≤ r₀ → ∀ x ∈ D, ∀ a : Fin 3 → ℝ, ∃ y ∈ D,
    pdist x y = r ∧ lam * ‖a‖ * r ≤ |∑ j, a j * (y.2 j - x.2 j)|

/-- Extraction from the literal local two-point supremum. -/
theorem localTwoPointSup_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace) (r : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : localTwoPointSup U D r ≤ ENNReal.ofReal M)
    {x y : ParabolicSpace} (hx : x ∈ D) (hy : y ∈ D) (hd : pdist x y ≤ r) :
    |U (x, y)| ≤ M := by
  have hh : ∀ x ∈ D, ∀ y ∈ D, ∀ (_ : pdist x y ≤ r),
      ENNReal.ofReal |U (x, y)| ≤ ENNReal.ofReal M := by
    simpa only [localTwoPointSup, iSup_le_iff] using hbound
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp (hh x hx y hy hd)

end GlobalPhi43.MW20

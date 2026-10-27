module

public import GlobalPhi43.Local.AffineTransport
public import GlobalPhi43.MW20.SourceAffineCoefficient

public section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set

/-- C1 scales by ℓ², so V keeps exactly its original counterterm. -/
theorem scaled_V_eq (J : ParabolicSpace → ℝ) (C₁ : ℝ) (b : ParabolicSpace) (ℓ : ℝ) :
    (fun z => parabolicPullback ℓ J b ℓ z ^ 2-ℓ^2*C₁) =
      parabolicPullback (ℓ^2) (fun z => J z^2-C₁) b ℓ := by
  funext z
  simp only [parabolicPullback]
  ring

/-- The same scaled C1 gives amplitude three to the corrected cubic W. -/
theorem scaled_W_eq (J : ParabolicSpace → ℝ) (C₁ : ℝ) (b : ParabolicSpace) (ℓ : ℝ) :
    (fun z => parabolicPullback ℓ J b ℓ z ^ 3-
      3*(ℓ^2*C₁)*parabolicPullback ℓ J b ℓ z) =
      parabolicPullback (ℓ^3) (fun z => J z^3-3*C₁*J z) b ℓ := by
  funext z
  simp only [parabolicPullback]
  ring

/-- Defect suprema retain amplitudes three, two, three on the actual image domain. -/
theorem defect_sup_scaling (e₁ e₂ e₃ : ParabolicSpace → ℝ) (b : ParabolicSpace)
    {ℓ : ℝ} (hℓ : 0<ℓ) (D : Set ParabolicSpace) :
    localScalarSup (parabolicPullback (ℓ^3) e₁ b ℓ) D =
      ENNReal.ofReal (ℓ^3)*localScalarSup e₁ (parabolicMap b ℓ '' D) ∧
    localScalarSup (parabolicPullback (ℓ^2) e₂ b ℓ) D =
      ENNReal.ofReal (ℓ^2)*localScalarSup e₂ (parabolicMap b ℓ '' D) ∧
    localScalarSup (parabolicPullback (ℓ^3) e₃ b ℓ) D =
      ENNReal.ofReal (ℓ^3)*localScalarSup e₃ (parabolicMap b ℓ '' D) := by
  have hs (a : ℝ) (ha : 0≤a) (e : ParabolicSpace → ℝ) :
      localScalarSup (parabolicPullback a e b ℓ) D =
        ENNReal.ofReal a*localScalarSup e (parabolicMap b ℓ '' D) := by
    have hh := localScalarSup_parabolicPullback a e b ℓ D
    rwa [abs_of_nonneg ha] at hh
  exact ⟨hs _ (by positivity) e₁,hs _ (by positivity) e₂,hs _ (by positivity) e₃⟩

end GlobalPhi43.Local

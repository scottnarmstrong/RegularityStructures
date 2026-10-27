module

public import GlobalPhi43.MW20.CoefficientNormBridges

/-!
# Full affine testing norms restricted from the actual radius-local source norm
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- A literal remainder estimate bounds the full sup-inf-sup source norm. -/
theorem localAffineSeminorm_le_of_remainder_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (ν : ParabolicSpace → Fin 3 → ℝ) (γ A : ℝ)
    (hb : ∀ x ∈ D, ∀ y ∈ D, y ≠ x →
      |U (x, y) - ∑ j, ν x j * (y.2 j - x.2 j)| ≤ A * Local.pdist x y ^ γ) :
    localAffineSeminorm U D γ ≤ ENNReal.ofReal A := by
  simp only [localAffineSeminorm, iSup_le_iff]
  intro x hx
  apply (iInf_le (fun a => affineRemainderSeminorm U D γ x a) (ν x)).trans
  simp only [affineRemainderSeminorm, iSup_le_iff]
  intro y hy hne
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) γ)).2 (hb x hx y hy hne)

/-- The full affine norm on any testing set of diameter at most L is bounded
by the actual radius-L norm on its open ambient source domain. This does
not infer an unrestricted source affine norm from the truncated one. -/
theorem localAffineSeminorm_le_radius_on_testing_domain
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    {D E : Set ParabolicSpace} (hD : IsOpen D) (hED : E ⊆ D)
    {γ L : ℝ} (hγ : 1 < γ) (hL : 0 < L)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, Local.pdist x y ≤ L) :
    localAffineSeminorm U E γ ≤ radiusAffineSeminorm U D γ L := by
  by_cases hn : radiusAffineSeminorm U D γ L = ⊤
  · rw [hn]
    exact le_top
  let A := (radiusAffineSeminorm U D γ L).toReal
  have hA : radiusAffineSeminorm U D γ L ≤ ENNReal.ofReal A := by
    dsimp only [A]
    rw [ENNReal.ofReal_toReal hn]
  have he := localAffineSeminorm_le_of_remainder_bound U E (diagonalSpatialCoefficient U) γ A
    (fun x hx y hy hne => radiusAffineSeminorm_remainder_bound U hU D hD hγ hL
      ENNReal.toReal_nonneg hA (hED hx) (hED hy) (hdiam x hx y hy) hne)
  simpa only [A, ENNReal.ofReal_toReal hn] using he

end GlobalPhi43.MW20

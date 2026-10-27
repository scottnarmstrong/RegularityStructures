module

public import Phi43.LiftBounds.Norm
public import RegularityStructures.Abstract.QFamilyModelBound
import Mathlib.Tactic.Linarith

/-! The Gamma coefficient estimate in recentering, retaining the diagonal term. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures MeasureTheory Set

/-- Uniform coefficient control by 1+M, including the diagonal coefficient one. This is the
factor which raises the local M(1+M) allowance to at most (1+M)^3. -/
theorem gamma_single_le_norm_radius {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} (Z : Model 𝒯 parabolicSemigroup)
    {γ : ℝ} {S : Set ParabolicSpace} (hfin : Z.normOn γ S ≠ ⊤)
    {τ : ι} (hτ : 𝒯.deg τ < γ) {x w : ParabolicSpace} (hx : x ∈ S) (hw : w ∈ S)
    {R : ℝ} (hR : parabolicNorm (w - x) ≤ R) (σ : ι) :
    let M := (Z.normOn γ S).toReal
    |Z.gammaMap w x (Pi.single τ 1) σ| ≤ (1 + M) * R ^ (𝒯.deg τ - 𝒯.deg σ) := by
  let M := (Z.normOn γ S).toReal
  change |Z.gammaMap w x (Pi.single τ 1) σ| ≤ (1 + M) * R ^ (𝒯.deg τ - 𝒯.deg σ)
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hb : Z.normOn γ S ≤ ENNReal.ofReal M := by rw [ENNReal.ofReal_toReal hfin]
  have hG := Phi43.LiftBounds.gammaBoundOn_of_normOn_le Z hM hb
  by_cases he : σ = τ
  · subst σ
    rw [Z.gammaMap_single_apply_self, abs_one, sub_self, Real.rpow_zero, mul_one]
    linarith
  · by_cases hlt : 𝒯.deg σ < 𝒯.deg τ
    · have h := hG τ σ hτ hlt x hx w hw
      have hpow := Real.rpow_le_rpow (parabolicNorm_nonneg _) hR (sub_nonneg.mpr hlt.le)
      calc _ ≤ M * parabolicNorm (w - x) ^ (𝒯.deg τ - 𝒯.deg σ) := h
        _ ≤ M * R ^ (𝒯.deg τ - 𝒯.deg σ) := mul_le_mul_of_nonneg_left hpow hM
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg ((parabolicNorm_nonneg _).trans hR) _)
    · rw [Z.gammaMap_single_apply_of_le x w he (le_of_not_gt hlt), abs_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg ((parabolicNorm_nonneg _).trans hR) _)

end GlobalPhi43.Attachment

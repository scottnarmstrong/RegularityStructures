module

public import GlobalPhi43.Attachment.LocalOrder
public import Phi43.LiftBounds.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Local order with the single finite model norm as constant. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures

/-- The model-norm polynomial for the local homogeneity bound, for any common domain. -/
theorem regPi_single_le_normOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup)
    {γ : ℝ} {S : Set ParabolicSpace} (hfin : M.normOn γ S ≠ ⊤)
    {i : ι} (hi : 𝒯.deg i < γ) {x y : ParabolicSpace} (hx : x ∈ S) (hy : y ∈ S)
    {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    let N := (M.normOn γ S).toReal
    |M.regPi x (Pi.single i 1) u y| ≤
      Fintype.card ι * N * (1 + N) *
        ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i),
          u ^ (a / 4) * parabolicNorm (y - x) ^ (𝒯.deg i - a) := by
  let N := (M.normOn γ S).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hbound : M.normOn γ S ≤ ENNReal.ofReal N := by
    rw [ENNReal.ofReal_toReal hfin]
  have hPi := Phi43.LiftBounds.piBoundOn_of_normOn_le M hN hbound
  have hGamma := Phi43.LiftBounds.gammaBoundOn_of_normOn_le M hN hbound
  have h := regPi_single_le_on M hPi hGamma hN hi hx hy hu
  have hmax : max N 1 ≤ 1 + N := max_le (by linarith) (by linarith)
  have hcoef : (Fintype.card ι : ℝ) * (max N 1 * N) ≤ Fintype.card ι * N * (1 + N) := by
    calc _ ≤ (Fintype.card ι : ℝ) * ((1 + N) * N) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax hN) (Nat.cast_nonneg _)
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hcoef
    (Finset.sum_nonneg fun a _ => mul_nonneg (Real.rpow_nonneg hu.1.le _)
      (Real.rpow_nonneg (parabolicNorm_nonneg _) _)))

end GlobalPhi43.Attachment

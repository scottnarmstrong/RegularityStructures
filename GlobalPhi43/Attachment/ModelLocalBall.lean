module

public import GlobalPhi43.Attachment.LocalOrderNorm
public import GlobalPhi43.Attachment.KernelIntegrability
public import GlobalPhi43.Attachment.Pairing
public import GlobalPhi43.Attachment.OrderCheck

/-! The actual moderate model supplies every field of the small-scale LocalBall input. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43

/-- The local-order exponent set automatically obeys the order-four integrability threshold. -/
theorem model_degreesAtMost_gt_neg_four (κ : Kappa) (τ : Symbol) :
    ∀ a ∈ (phi43RegularityStructure κ).degreesAtMost (homogeneity κ τ), -(4 : ℝ) < a := by
  intro a ha
  obtain ⟨σ, _, rfl⟩ := ((phi43RegularityStructure κ).mem_degreesAtMost).mp ha
  exact homogeneity_gt_neg_four κ σ

/-- The complete small-scale local ball, with no assumed kernel-integrability field. -/
theorem model_localBall {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    {τ : Symbol} (hτ : IsPinnedSymbol τ) (hdeg : homogeneity κ τ < gamma κ)
    {S : Set ParabolicSpace} (hfin : Z.normOn (gamma κ) S ≠ ⊤)
    {x : ParabolicSpace} (hx : x ∈ S) {lam : ℝ} (hlam : lam ≤ 1)
    (hS : ∀ y, parabolicNorm (y - x) ≤ lam → y ∈ S) :
    let M := (Z.normOn (gamma κ) S).toReal
    parabolicSemigroup.LocalBall (fun u y => Z.regPi x (Pi.single τ 1) u y)
      x (homogeneity κ τ) ((phi43RegularityStructure κ).degreesAtMost (homogeneity κ τ))
      (Fintype.card Symbol * M * (1 + M)) lam := by
  let M := (Z.normOn (gamma κ) S).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hcoef : 0 ≤ (Fintype.card Symbol : ℝ) * M * (1 + M) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (add_nonneg zero_le_one hM)
  have hle : ∀ a ∈ (phi43RegularityStructure κ).degreesAtMost (homogeneity κ τ),
      a ≤ homogeneity κ τ := by
    intro a ha
    obtain ⟨σ, hσ, rfl⟩ := ((phi43RegularityStructure κ).mem_degreesAtMost).mp ha
    exact hσ
  apply localBall_of_model Z x τ hcoef hle
  · intro u hu y hy
    have hy' : parabolicNorm (y - x) ≤ lam := hy
    have h := regPi_single_le_normOn Z hfin hdeg hx (hS y hy') hu
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) hcoef)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (parabolicNorm_nonneg _) hy' (sub_nonneg.mpr (hle a ha)))
      (Real.rpow_nonneg hu.1.le _)
  · intro s hs h₀
    obtain ⟨W, hW⟩ := model_kernel_int hg hZ hτ x hs h₀
    exact ⟨W, fun v hv y hy => hW v hv y (hy.trans hlam)⟩

end GlobalPhi43.Attachment

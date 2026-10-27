module

public import GlobalPhi43.Attachment.MassiveWeightedIdentity
public import RegularityStructures.PDE.Duhamel

/-! The exact massive potential in ordinary heat/Duhamel form after exponential reweighting. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.PDE Set

/-- Translation of the actual compact time integral, without an integrability hypothesis. -/
theorem attachment_integral_Ioc_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (a r : ℝ) (hr : 0 ≤ r) :
    (∫ u in Ioc a (a+r), F u) = ∫ u in Ioc 0 r, F (a+u) := by
  rw [← intervalIntegral.integral_of_le (by linarith : a ≤ a+r),
    ← intervalIntegral.integral_of_le hr]
  simpa only [add_zero, add_comm r a] using
    (intervalIntegral.integral_comp_add_left (a := 0) (b := r) F a).symm

/-- Weighted forcing path at an arbitrary source start time. -/
@[expose] noncomputable def massiveWeightedForcing {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) (a r : ℝ) : C(Torus3, ℝ) :=
  Real.exp (a+r) • potSlice (attachment_potForcing hf hg).cont (a+r)

/-- The exact ordinary Duhamel identity for the exponential reweighting of any actual potential. -/
theorem massivePotential_shifted_weighted_identity {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ)
    (a r : ℝ) (hr : 0 ≤ r) :
    Real.exp (a+r) • ψ (a+r) = heatOp r (Real.exp a • ψ a) +
      duhamel (massiveWeightedForcing hf hg a) r := by
  have h := massivePotential_weighted_identity hf hg hψ (s := a) (t := a+r) (by linarith)
  rw [add_sub_cancel_left] at h
  rw [heatOp_smul]
  rw [h]
  congr 1
  rw [attachment_integral_Ioc_translate _ a r hr, duhamel,
    intervalIntegral.integral_of_le hr]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u _
  simp only [massiveWeightedForcing, heatOp_smul]
  congr 2
  ring

end GlobalPhi43.Attachment

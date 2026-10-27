module

public import GlobalPhi43.MW20.KernelNegativeSeminorms
public import GlobalPhi43.MW20.CoordinateSeminorm
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! The coordinate-tree source norm attached to the actual MW20 kernel.
Continuity and compact support supply vector integrability; it is not an
independent hypothesis on the source data. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- Actual smooth-kernel coordinate testing is integrable for continuous V. -/
theorem mw20_coordinateTree_integrable (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (hV : Continuous V) (x : ParabolicSpace)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    Integrable (fun z => V (x + z) • z.2) (mw20TestingKernel Φ hΦ t) := by
  rw [mw20TestingKernel_pos Φ hΦ ht]
  apply integrable_pi_iff.2
  intro i
  have hc : Continuous (fun y : ParabolicSpace => V y * (y.2 i - x.2 i)) := by fun_prop
  have hi := reconstruction_kernel_section_integrable Φ hΦ ht ht₁ _ hc x
  simpa only [Prod.snd_add, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, smul_eq_mul] using hi

end GlobalPhi43.MW20

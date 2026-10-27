/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitHeatSource
public import GlobalPhi43.Local.GaussianFundamentalIdentity
public import Mathlib.MeasureTheory.Integral.Prod

/-! Fixed finite past-source restriction and physical time integration. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MeasureTheory

 theorem compact_source_time_integral {F : ParabolicSpace → ℝ}
    (hF : Continuous F) (hcF : HasCompactSupport F) {t : ℝ} (ht : -1 ≤ t)
    (hsource : ∀ q ∉ unitHeatSourceDomain, F q = 0)
    (htime : ∀ r ∉ Ioc (-1 : ℝ) t, ∀ z : Fin 3 → ℝ, F (r, z) = 0) :
    Integrable (fun r : ℝ => ∫ z : Fin 3 → ℝ, F (r, z)) ∧
      (∫ q, F q ∂unitHeatSourceMeasure) = ∫ r in (-1 : ℝ)..t, ∫ z : Fin 3 → ℝ, F (r, z) := by
  have hi : Integrable F (volume : Measure ParabolicSpace) := hF.integrable_of_hasCompactSupport hcF
  have hip : Integrable F ((volume : Measure ℝ).prod (volume : Measure (Fin 3 → ℝ))) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  refine ⟨hip.integral_prod_left, ?_⟩
  change (∫ q in unitHeatSourceDomain, F q) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsource]
  rw [Measure.volume_eq_prod, integral_prod F hip, intervalIntegral.integral_of_le ht]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (htime r hr)

end GlobalPhi43.Local

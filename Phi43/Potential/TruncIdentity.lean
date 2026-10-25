/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.SlicePotential

/-!
# The truncated massive-potential identity

For `s' ≤ s`:  `∫_{s'}^{s} e^{-(s-r)} P_{s-r} f_r dr = ψ(s) - e^{-(s-s')} P_{s-s'} ψ(s')` in `C(T³)`
(`integral_potF_Ioc`).  Proof: split `ψ(s) = ∫_{r ≤ s'} + ∫_{s' < r ≤ s}` and use the semigroup property
`F_s(r) = e^{-(s-s')} P_{s-s'} F_{s'}(r)` for `r ≤ s'`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.Potential

open RegularityStructures

theorem potF_eq_comp {f : SpaceTime → ℝ} (hf : Continuous f) {s s' r : ℝ} (hs : s' ≤ s)
    (hr : r ≤ s') :
    potF hf s r = Real.exp (-(s - s')) • PDE.heatOp (s - s') (potF hf s' r) := by
  unfold potF
  rw [PDE.heatOp_smul, PDE.heatOp_heatOp (by linarith) (by linarith), smul_smul, ← Real.exp_add]
  congr 3 <;> ring

/-- **The truncated potential identity.** -/
theorem integral_potF_Ioc {f : SpaceTime → ℝ} (hF : PotForcing f)
    {ψ : ℝ → C(Torus3, ℝ)} (hψ : IsMassivePotential f ψ) {s s' : ℝ} (hs : s' ≤ s) :
    ∫ r in Ioc s' s, potF hF.cont s r =
      ψ s - Real.exp (-(s - s')) • PDE.heatOp (s - s') (ψ s') := by
  have hsplit : ∫ r in Iic s, potF hF.cont s r =
      (∫ r in Iic s', potF hF.cont s r) + ∫ r in Ioc s' s, potF hF.cont s r := by
    have hu : Iic s = Iic s' ∪ Ioc s' s := (Iic_union_Ioc_eq_Iic hs).symm
    rw [hu]
    exact setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      ((integrableOn_potF hF s).mono_set (Iic_subset_Iic.2 hs))
      ((integrableOn_potF hF s).mono_set (Ioc_subset_Iic_self.trans le_rfl))
  have hL : ∫ r in Iic s', potF hF.cont s r =
      Real.exp (-(s - s')) • PDE.heatOp (s - s') (∫ r in Iic s', potF hF.cont s' r) := by
    have hCLM := (Real.exp (-(s - s')) • PDE.heatOpCLM (E := ℝ) (s - s')).integral_comp_comm
      (integrableOn_potF hF s')
    have e : ∀ g : C(Torus3, ℝ), (Real.exp (-(s - s')) • PDE.heatOpCLM (E := ℝ) (s - s')) g =
        Real.exp (-(s - s')) • PDE.heatOp (s - s') g := fun g => rfl
    simp only [e] at hCLM
    rw [← hCLM]
    exact setIntegral_congr_fun measurableSet_Iic fun r hr => potF_eq_comp hF.cont hs hr
  rw [← potential_eq_integral_potF hF hψ] at hsplit hL
  rw [hL] at hsplit
  rw [hsplit]
  abel

end RegularityStructures.Potential

end

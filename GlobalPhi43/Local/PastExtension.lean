/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastBudget
public import GlobalPhi43.MW20.AffineSeminorm

/-! The actual Q_- enlargement from the small-past budget in the coefficient estimate. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set

/-- The explicit coefficient allowance; eta=epsilon/32. -/
def largePairBudget (η γ B Q : ℝ) : ℝ :=
  B / (2 * η) ^ γ + 3 * ((B + Q * η ^ γ) / η) / (2 * η) ^ (γ - 1)

/-- Small past pairs use Q directly; all remaining past pairs use the
coefficient probes and the SAME original radius-local U budget. -/
theorem past_extension_bound
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d d₀ η γ B Q : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (hγ : 1 ≤ γ) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hU : ∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
      ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (2 * η * d),
      |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ pastBall x (d / 4)) :
    |affineRemainder U ν x y| ≤ max Q (largePairBudget η γ B Q) * (pdist x y / d) ^ γ := by
  by_cases hsmall : pdist x y < 2 * η * d
  · exact (hpast x hx y ⟨hsmall, hy.2⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (div_nonneg (pdist_nonneg x y) hd.le) _))
  · have hfar : 2 * η * d ≤ pdist x y := le_of_not_gt hsmall
    have hh := step5_large_past_pair U ν hd hdd₀ hη hηsmall hγ hB hQ hU hpast hx hy hfar
    have hne : y ≠ x := by intro he; subst y; exact (lt_irrefl _ hy.2)
    have hρ := pdist_pos_of_ne hne
    have hp : 0 < (pdist x y / d) ^ γ := Real.rpow_pos_of_pos (div_pos hρ hd) _
    have hb : |affineRemainder U ν x y| ≤ largePairBudget η γ B Q * (pdist x y / d) ^ γ :=
      (div_le_iff₀ hp).mp hh
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)

end GlobalPhi43.Local

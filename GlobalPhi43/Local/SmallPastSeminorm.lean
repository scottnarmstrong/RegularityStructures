/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SmoothCausalFiniteness

/-! The actual finite Q_epsilon used by the causal absorption, with
eta=epsilon/32. Its finiteness is derived, not added to the source contract. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal ContDiff

def smallPastRemainderSeminorm (U : GermPoint → ℝ)
    (ν : ParabolicSpace → Fin 3 → ℝ) (r d₀ η γ : ℝ) : ℝ≥0∞ :=
  ⨆ d ∈ Ioc (0 : ℝ) d₀, ⨆ x ∈ cylinderInterior r d,
    ⨆ y ∈ pastBall x (2 * η * d), ENNReal.ofReal
      (|affineRemainder (fun a b => U (a, b)) ν x y| / (pdist x y / d) ^ γ)

theorem smallPastRemainderSeminorm_le (U : GermPoint → ℝ)
    (ν : ParabolicSpace → Fin 3 → ℝ) {r d₀ η γ Q : ℝ}
    (hbound : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ y ∈ pastBall x (2 * η * d),
      |affineRemainder (fun a b => U (a, b)) ν x y| ≤ Q * (pdist x y / d) ^ γ) :
    smallPastRemainderSeminorm U ν r d₀ η γ ≤ ENNReal.ofReal Q := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply ENNReal.ofReal_le_ofReal
  have hne : y ≠ x := by intro he; subst y; exact (lt_irrefl _ hy.2)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (div_pos (pdist_pos_of_ne hne) hd.1) _)).2
    (hbound d hd x hx y hy)

/-- The actual supremum supplies its exact normalized pointwise allowance. -/
theorem smallPastRemainderSeminorm_bound (U : GermPoint → ℝ)
    (ν : ParabolicSpace → Fin 3 → ℝ) {r d₀ η γ d : ℝ}
    (hfinite : smallPastRemainderSeminorm U ν r d₀ η γ ≠ ⊤)
    (hd : d ∈ Ioc (0 : ℝ) d₀) {x y : ParabolicSpace}
    (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x (2 * η * d)) :
    |affineRemainder (fun a b => U (a, b)) ν x y| ≤
      (smallPastRemainderSeminorm U ν r d₀ η γ).toReal * (pdist x y / d) ^ γ := by
  have hall : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ y ∈ pastBall x (2 * η * d), ENNReal.ofReal
        (|affineRemainder (fun a b => U (a, b)) ν x y| / (pdist x y / d) ^ γ) ≤
          smallPastRemainderSeminorm U ν r d₀ η γ := by
    simpa only [smallPastRemainderSeminorm, iSup_le_iff] using
      (le_rfl : smallPastRemainderSeminorm U ν r d₀ η γ ≤ smallPastRemainderSeminorm U ν r d₀ η γ)
  have hh := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp (hall d hd x hx y hy)
  have hne : y ≠ x := by intro he; subst y; exact (lt_irrefl _ hy.2)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (div_pos (pdist_pos_of_ne hne) hd.1) _)).mp hh

/-- Standing local smoothness implies that the actual Q_epsilon is finite. -/
theorem smallPastRemainderSeminorm_ne_top (U : GermPoint → ℝ)
    {r d₀ η γ : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hηsmall : η ≤ 1 / 16)
    (hγ : 0 ≤ γ) (hγ₂ : γ ≤ 2)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    (hdiag : ∀ x ∈ sourceCylinder r, U (x, x) = 0) :
    smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ η γ ≠ ⊤ := by
  obtain ⟨Q, _, hQ⟩ := exists_finite_small_past_bound U hr hη hηsmall hγ hγ₂ hU hdiag
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  exact smallPastRemainderSeminorm_le U _ (fun d hd => hQ d hd.1)

end GlobalPhi43.Local

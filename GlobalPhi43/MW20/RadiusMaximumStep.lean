module

public import GlobalPhi43.MW20.RadiusAlgorithm

/-!
# Turning the source maximum row into a radius step

The input is the literal maximum in MW20 (4.33), with the boundary gap
`R - M⁻¹`. At the algorithm increment `R = 4C/M`, with fixed `C ≥ 1`,
it gives the halving used in the radius iteration.
-/

public section

namespace GlobalPhi43.MW20

/-- Every full algorithm increment satisfies the source restriction `R ≥ 2/M`. -/
theorem radius_increment_admissible {C M : ℝ} (hC : 1 ≤ C) (hM : 0 < M) :
    2 / M ≤ 4 * C / M := by
  exact div_le_div_of_nonneg_right (by linarith) hM.le

/-- The boundary-gap term in (4.33) is absorbed by half the current mass. -/
theorem radius_gap_bound {C M : ℝ} (hC : 1 ≤ C) (hM : 0 < M) :
    C / (4 * C / M - 1 / M) ≤ M / 2 := by
  have hden : 0 < 4 * C / M - 1 / M := by
    rw [← sub_div]
    exact div_pos (by linarith) hM
  apply (div_le_iff₀ hden).2
  have heq : M / 2 * (4 * C / M - 1 / M) = 2 * C - 1 / 2 := by
    field_simp
    ring
  linarith

/-- The exact source maximum row at the algorithm increment implies halving. -/
theorem radius_halving_of_maximum {C M N : ℝ} (hC : 1 ≤ C) (hM : 0 < M)
    (hmax : N ≤ max (C / (4 * C / M - 1 / M)) (M / 2)) : N ≤ M / 2 := by
  exact hmax.trans (max_le (radius_gap_bound hC hM) le_rfl)

/-- Source-row formulation for the full scalar radius estimate. In addition to
the fixed smallness stopping bound, the only analytic input is (4.33) on its
licensed increment range. Endpoint and zero-mass cases are handled internally. -/
theorem radiusSequence_estimate_of_maximum (f : ℝ → ℝ) (Good : ℝ → Prop) {C L A : ℝ}
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) (hmono : AntitoneOn f (Set.Icc 0 L))
    (hmax : ∀ r ∈ Set.Icc 0 L, Good r → 0 < f r →
      ∀ R, 2 / f r ≤ R → r + R < L →
        f (r + R) ≤ max (C / (R - 1 / f r)) (f r / 2))
    (hfail : ∀ r ∈ Set.Icc 0 L, ¬ Good r → f r ≤ A) :
    ∀ R ∈ Set.Ioc 0 L, f R ≤ max (8 * C / R) A := by
  have hCpos : 0 < C := by linarith
  obtain ⟨n, _, _, hb⟩ := radiusSequence_estimate f Good hCpos hL hA hf hmono
    (fun r hr hg hm hR => radius_halving_of_maximum hC hm
      (hmax r hr hg hm _ (radius_increment_admissible hC hm) hR)) hfail
  exact hb

end GlobalPhi43.MW20

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiDiffPointwise

/-!
# The bounds for the second-difference pieces `E₁, E₂, E₃`

See `ProductPiDiffPointwise`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_neg_pq_isq' {s θ : ℝ} (hs : 0 < s) (k m : ℕ) {e : ℝ} (he : e = k + m * θ) :
    s ^ (-e) = (s ^ (-(1 : ℝ))) ^ k * (s ^ (-θ)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (s ^ (-θ)), ← Real.rpow_mul hs.le,
    ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
  congr 1
  rw [he]
  ring

private theorem rpow_two_theta_isq' {M θ : ℝ} (hM : 0 < M) : (M ^ θ) ^ 2 = M ^ (2 * θ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
  congr 1
  push_cast
  ring

variable (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)

/-- **Piece `E₁`**. -/
theorem isqDiffE1_abs_le (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x₁ x₂ : SpaceTime, 0 < torusParabolicSize x₁ → 0 < torusParabolicSize x₂ →
        |isqDiffE1 N ρ ρ' ε ε' x₁ x₂| ≤
          K * (max ε ε') ^ (2 * θ) *
            (torusParabolicSize x₁ ^ (-(2 + 2 * θ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) +
              torusParabolicSize x₁ ^ (-(2 : ℝ)) * torusParabolicSize x₂ ^ (-(1 + 2 * θ))) := by
  obtain ⟨A, hA, hT⟩ := hairerCrossTwo_tables_bd_i3Psi N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨2048 * A ^ 3, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x₁ x₂ h1 h2
  obtain ⟨u1, -, -⟩ := hT hε hε1 hε' hε'1 x₁ h1
  obtain ⟨u2, -, -⟩ := hT hε hε1 hε' hε'1 x₂ h2
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hμ : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg hM.le _
  have key := I3PsiDiffTable.abs_prod_three_le_sq hμ (Real.rpow_nonneg h1.le (-θ))
    (Real.rpow_nonneg h1.le (-θ)) (Real.rpow_nonneg h2.le (-θ)) u1 u1 u2
  dsimp only at key
  unfold isqDiffE1
  refine le_trans (le_of_eq ?_) (key.trans ?_)
  · congr 1; ring
  rw [rpow_neg_pq_isq' h1 2 2 (θ := θ) (e := 2 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq_isq' h2 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h1 2 0 (θ := θ) (e := 2) (by push_cast; ring),
    rpow_neg_pq_isq' h2 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    ← rpow_two_theta_isq' hM]
  set p₁ := torusParabolicSize x₁ ^ (-(1 : ℝ))
  set p₂ := torusParabolicSize x₂ ^ (-(1 : ℝ))
  set q₁ := torusParabolicSize x₁ ^ (-θ)
  set q₂ := torusParabolicSize x₂ ^ (-θ)
  set m := (max ε ε') ^ θ
  have hp₁ : 0 ≤ p₁ := Real.rpow_nonneg h1.le _
  have hp₂ : 0 ≤ p₂ := Real.rpow_nonneg h2.le _
  have hq₁ : 0 ≤ q₁ := Real.rpow_nonneg h1.le _
  have hq₂ : 0 ≤ q₂ := Real.rpow_nonneg h2.le _
  have hW : 0 ≤ m ^ 2 * A ^ 3 * (p₁ ^ 2 * p₂) := by positivity
  have := mul_nonneg hW (by positivity : 0 ≤ 1024 * q₂ ^ 2)
  nlinarith [this]

/-- **Piece `E₂`**. -/
theorem isqDiffE2_abs_le (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x₁ x₂ x₃ : SpaceTime, 0 < torusParabolicSize x₁ → 0 < torusParabolicSize x₂ →
        0 < torusParabolicSize x₃ →
        |isqDiffE2 N ρ ρ' ε ε' x₁ x₂ x₃| ≤
          K * (max ε ε') ^ (2 * θ) *
            (torusParabolicSize x₁ ^ (-(1 + 2 * θ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) *
                torusParabolicSize x₃ ^ (-(1 : ℝ)) +
              torusParabolicSize x₁ ^ (-(1 : ℝ)) * torusParabolicSize x₂ ^ (-(1 + 2 * θ)) *
                torusParabolicSize x₃ ^ (-(1 : ℝ)) +
              torusParabolicSize x₁ ^ (-(1 : ℝ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) *
                torusParabolicSize x₃ ^ (-(1 + 2 * θ))) := by
  obtain ⟨A, hA, hT⟩ := hairerCrossTwo_tables_bd_i3Psi N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨1024 * A ^ 3, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x₁ x₂ x₃ h1 h2 h3
  obtain ⟨u1, -, -⟩ := hT hε hε1 hε' hε'1 x₁ h1
  obtain ⟨u2, -, -⟩ := hT hε hε1 hε' hε'1 x₂ h2
  obtain ⟨u3, -, -⟩ := hT hε hε1 hε' hε'1 x₃ h3
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hμ : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg hM.le _
  have key := I3PsiDiffTable.abs_prod_three_le_sq hμ (Real.rpow_nonneg h1.le (-θ))
    (Real.rpow_nonneg h2.le (-θ)) (Real.rpow_nonneg h3.le (-θ)) u1 u2 u3
  dsimp only at key
  unfold isqDiffE2
  refine le_trans (le_of_eq ?_) (key.trans ?_)
  · congr 1
  rw [rpow_neg_pq_isq' h1 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq_isq' h2 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h3 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h1 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h2 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq_isq' h3 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    ← rpow_two_theta_isq' hM]
  set p₁ := torusParabolicSize x₁ ^ (-(1 : ℝ))
  set p₂ := torusParabolicSize x₂ ^ (-(1 : ℝ))
  set p₃ := torusParabolicSize x₃ ^ (-(1 : ℝ))
  set q₁ := torusParabolicSize x₁ ^ (-θ)
  set q₂ := torusParabolicSize x₂ ^ (-θ)
  set q₃ := torusParabolicSize x₃ ^ (-θ)
  set m := (max ε ε') ^ θ
  have hp₁ : 0 ≤ p₁ := Real.rpow_nonneg h1.le _
  have hp₂ : 0 ≤ p₂ := Real.rpow_nonneg h2.le _
  have hp₃ : 0 ≤ p₃ := Real.rpow_nonneg h3.le _
  have hq₁ : 0 ≤ q₁ := Real.rpow_nonneg h1.le _
  have hq₂ : 0 ≤ q₂ := Real.rpow_nonneg h2.le _
  have hq₃ : 0 ≤ q₃ := Real.rpow_nonneg h3.le _
  have hW : 0 ≤ m ^ 2 * A ^ 3 * (p₁ * p₂ * p₃) := by positivity
  have := mul_nonneg hW (by positivity : 0 ≤ 0 * q₁ ^ 2)
  nlinarith [this]

/-- **Piece `E₃`**. -/
theorem isqDiffE3_abs_le (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x₁ x₂ x₃ : SpaceTime, 0 < torusParabolicSize x₁ → 0 < torusParabolicSize x₂ →
        0 < torusParabolicSize x₃ →
        |isqDiffE3 N ρ ρ' ε ε' x₁ x₂ x₃| ≤
          K * (max ε ε') ^ (2 * θ) *
            (torusParabolicSize x₁ ^ (-(1 + 2 * θ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) *
                torusParabolicSize x₃ ^ (-(1 : ℝ)) +
              torusParabolicSize x₁ ^ (-(1 : ℝ)) * torusParabolicSize x₂ ^ (-(1 + 2 * θ)) *
                torusParabolicSize x₃ ^ (-(1 : ℝ)) +
              torusParabolicSize x₁ ^ (-(1 : ℝ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) *
                torusParabolicSize x₃ ^ (-(1 + 2 * θ))) := by
  obtain ⟨A, hA, hT⟩ := hairerCrossTwo_tables_bd_i3Psi N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨1024 * A ^ 3, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x₁ x₂ x₃ h1 h2 h3
  obtain ⟨-, u1, -⟩ := hT hε hε1 hε' hε'1 x₁ h1
  obtain ⟨u2, -, -⟩ := hT hε hε1 hε' hε'1 x₂ h2
  obtain ⟨-, -, u3⟩ := hT hε hε1 hε' hε'1 x₃ h3
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hμ : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg hM.le _
  have key := I3PsiDiffTable.abs_prod_three_le_sq hμ (Real.rpow_nonneg h1.le (-θ))
    (Real.rpow_nonneg h2.le (-θ)) (Real.rpow_nonneg h3.le (-θ)) u1 u2 u3
  dsimp only at key
  unfold isqDiffE3
  refine le_trans (le_of_eq ?_) (key.trans ?_)
  · congr 1
  rw [rpow_neg_pq_isq' h1 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq_isq' h2 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h3 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h1 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq_isq' h2 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq_isq' h3 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    ← rpow_two_theta_isq' hM]
  set p₁ := torusParabolicSize x₁ ^ (-(1 : ℝ))
  set p₂ := torusParabolicSize x₂ ^ (-(1 : ℝ))
  set p₃ := torusParabolicSize x₃ ^ (-(1 : ℝ))
  set q₁ := torusParabolicSize x₁ ^ (-θ)
  set q₂ := torusParabolicSize x₂ ^ (-θ)
  set q₃ := torusParabolicSize x₃ ^ (-θ)
  set m := (max ε ε') ^ θ
  have hp₁ : 0 ≤ p₁ := Real.rpow_nonneg h1.le _
  have hp₂ : 0 ≤ p₂ := Real.rpow_nonneg h2.le _
  have hp₃ : 0 ≤ p₃ := Real.rpow_nonneg h3.le _
  have hq₁ : 0 ≤ q₁ := Real.rpow_nonneg h1.le _
  have hq₂ : 0 ≤ q₂ := Real.rpow_nonneg h2.le _
  have hq₃ : 0 ≤ q₃ := Real.rpow_nonneg h3.le _
  have hW : 0 ≤ m ^ 2 * A ^ 3 * (p₁ * p₂ * p₃) := by positivity
  have := mul_nonneg hW (by positivity : 0 ≤ 0 * q₁ ^ 2)
  nlinarith [this]

end RegularityStructures.Phi43

end

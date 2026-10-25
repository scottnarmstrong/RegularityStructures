/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceTables
public import Phi43.BPHZ.TreeI3Psi2DiagramDefs

/-!
# The second differences of the chaos-`5` and chaos-`3` kernels of `I(Ψ³)Ψ²`

For the cross covariances `Q₁₁, Q₁₂, Q₂₁, Q₂₂` of two noises, the covariance of the difference of the
two fields involves the combination `χ(Q₁₁) - χ(Q₁₂) - χ(Q₂₁) + χ(Q₂₂)` of the chaos kernels
(the `(1,1)`, `(1,2)`, `(2,1)`, `(2,2)` entries of the `2 × 2` tables).  If the three tables of
`I3Psi2TablesBd A μ θ` satisfy the bound data, then the second difference of a monomial of five
covariances is bounded by `μ²` times a sum of products of powers in which exactly one factor has its
exponent raised by `2θ`.  We prove this for the kernels `χ₅` (`i3Psi2DiffChi5`) and `χ₃`
(`i3Psi2DiffChi3`); the entries are those of `hairerI3Psi2Chaos5`, `hairerI3Psi2Chaos3` at
`(w, z, w', z') = (w, z, v, z')`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The second difference of the chaos-`5` kernel in terms of the entries `c₀₂, c₀₃, c₁₂, c₁₃`. -/
def i3Psi2DiffChi5 (Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ) (x₀₂ x₀₃ x₁₂ x₁₃ : SpaceTime) : ℝ :=
  i3Psi2Kernel5 (Q₁₁ x₀₂) (Q₁₁ x₀₃) (Q₁₁ x₁₂) (Q₁₁ x₁₃) -
    i3Psi2Kernel5 (Q₁₂ x₀₂) (Q₁₂ x₀₃) (Q₁₂ x₁₂) (Q₁₂ x₁₃) -
    i3Psi2Kernel5 (Q₂₁ x₀₂) (Q₂₁ x₀₃) (Q₂₁ x₁₂) (Q₂₁ x₁₃) +
    i3Psi2Kernel5 (Q₂₂ x₀₂) (Q₂₂ x₀₃) (Q₂₂ x₁₂) (Q₂₂ x₁₃)

/-- The second difference of the chaos-`3` kernel in terms of the entries
`c₀₁, c₂₃, c₀₂, c₀₃, c₁₂, c₁₃`: `c₀₁` is the covariance of the first scale with itself, `c₂₃` that
of the second scale with itself, the other entries are cross covariances. -/
def i3Psi2DiffChi3 (Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ)
    (x₀₁ x₂₃ x₀₂ x₀₃ x₁₂ x₁₃ : SpaceTime) : ℝ :=
  i3Psi2Kernel3 (Q₁₁ x₀₁) (Q₁₁ x₂₃) (Q₁₁ x₀₂) (Q₁₁ x₀₃) (Q₁₁ x₁₂) (Q₁₁ x₁₃) -
    i3Psi2Kernel3 (Q₁₁ x₀₁) (Q₂₂ x₂₃) (Q₁₂ x₀₂) (Q₁₂ x₀₃) (Q₁₂ x₁₂) (Q₁₂ x₁₃) -
    i3Psi2Kernel3 (Q₂₂ x₀₁) (Q₁₁ x₂₃) (Q₂₁ x₀₂) (Q₂₁ x₀₃) (Q₂₁ x₁₂) (Q₂₁ x₁₃) +
    i3Psi2Kernel3 (Q₂₂ x₀₁) (Q₂₂ x₂₃) (Q₂₂ x₀₂) (Q₂₂ x₀₃) (Q₂₂ x₁₂) (Q₂₂ x₁₃)

/-- The majorant `T₁` of the second difference of `12 c₀₂³ c₁₃²`. -/
def i3Psi2DiffT1 (θ : ℝ) (x₀₂ x₁₃ : SpaceTime) : ℝ :=
  torusParabolicSize x₀₂ ^ (-(3 + 2 * θ)) * torusParabolicSize x₁₃ ^ (-(2 : ℝ)) +
    torusParabolicSize x₀₂ ^ (-(3 : ℝ)) * torusParabolicSize x₁₃ ^ (-(2 + 2 * θ))

/-- The majorant `T₂` of the second difference of `72 c₀₂² c₀₃ c₁₂ c₁₃`. -/
def i3Psi2DiffT2 (θ : ℝ) (x₀₂ x₀₃ x₁₂ x₁₃ : SpaceTime) : ℝ :=
  torusParabolicSize x₀₂ ^ (-(2 + 2 * θ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) * torusParabolicSize x₁₃ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₂ ^ (-(2 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 + 2 * θ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) * torusParabolicSize x₁₃ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₂ ^ (-(2 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 + 2 * θ)) * torusParabolicSize x₁₃ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₂ ^ (-(2 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) * torusParabolicSize x₁₃ ^ (-(1 + 2 * θ))

/-- The majorant `T₃` of the second difference of `36 c₀₂ c₀₃² c₁₂²`. -/
def i3Psi2DiffT3 (θ : ℝ) (x₀₂ x₀₃ x₁₂ : SpaceTime) : ℝ :=
  torusParabolicSize x₀₂ ^ (-(1 + 2 * θ)) * torusParabolicSize x₀₃ ^ (-(2 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(2 : ℝ)) +
    torusParabolicSize x₀₂ ^ (-(1 : ℝ)) * torusParabolicSize x₀₃ ^ (-(2 + 2 * θ)) *
      torusParabolicSize x₁₂ ^ (-(2 : ℝ)) +
    torusParabolicSize x₀₂ ^ (-(1 : ℝ)) * torusParabolicSize x₀₃ ^ (-(2 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(2 + 2 * θ))

/-- The majorant `T₄` of the second difference of `72 c₀₁ c₀₂² c₁₃ c₂₃`. -/
def i3Psi2DiffT4 (θ : ℝ) (x₀₁ x₀₂ x₁₃ x₂₃ : SpaceTime) : ℝ :=
  torusParabolicSize x₀₁ ^ (-(1 + 2 * θ)) * torusParabolicSize x₀₂ ^ (-(2 : ℝ)) *
      torusParabolicSize x₁₃ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₂ ^ (-(2 + 2 * θ)) *
      torusParabolicSize x₁₃ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₂ ^ (-(2 : ℝ)) *
      torusParabolicSize x₁₃ ^ (-(1 + 2 * θ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₂ ^ (-(2 : ℝ)) *
      torusParabolicSize x₁₃ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 + 2 * θ))

/-- The majorant `T₅` of the second difference of `144 c₀₁ c₀₂ c₀₃ c₁₂ c₂₃`. -/
def i3Psi2DiffT5 (θ : ℝ) (x₀₁ x₀₃ x₀₂ x₂₃ x₁₂ : SpaceTime) : ℝ :=
  torusParabolicSize x₀₁ ^ (-(1 + 2 * θ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₀₂ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 + 2 * θ)) *
      torusParabolicSize x₀₂ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₀₂ ^ (-(1 + 2 * θ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₀₂ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 + 2 * θ)) *
      torusParabolicSize x₁₂ ^ (-(1 : ℝ)) +
    torusParabolicSize x₀₁ ^ (-(1 : ℝ)) * torusParabolicSize x₀₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₀₂ ^ (-(1 : ℝ)) * torusParabolicSize x₂₃ ^ (-(1 : ℝ)) *
      torusParabolicSize x₁₂ ^ (-(1 + 2 * θ))

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_neg_pq {s θ : ℝ} (hs : 0 < s) (k m : ℕ) {e : ℝ} (he : e = k + m * θ) :
    s ^ (-e) = (s ^ (-(1 : ℝ))) ^ k * (s ^ (-θ)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (s ^ (-θ)), ← Real.rpow_mul hs.le,
    ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
  congr 1
  rw [he]
  ring

/-- The second difference of a product of five tables, in terms of `p = s^(-1)`, `q = s^(-θ)`. -/
private theorem diff5_le {μ A θ : ℝ} (hμ : 0 ≤ μ) {t₁ t₂ t₃ t₄ t₅ : I3PsiDiffTable}
    {s₁ s₂ s₃ s₄ s₅ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (h₃ : 0 < s₃) (h₄ : 0 < s₄) (h₅ : 0 < s₅)
    (b₁ : I3PsiDiffTable.Bd μ (A * s₁ ^ (-(1 : ℝ))) (s₁ ^ (-θ)) t₁)
    (b₂ : I3PsiDiffTable.Bd μ (A * s₂ ^ (-(1 : ℝ))) (s₂ ^ (-θ)) t₂)
    (b₃ : I3PsiDiffTable.Bd μ (A * s₃ ^ (-(1 : ℝ))) (s₃ ^ (-θ)) t₃)
    (b₄ : I3PsiDiffTable.Bd μ (A * s₄ ^ (-(1 : ℝ))) (s₄ ^ (-θ)) t₄)
    (b₅ : I3PsiDiffTable.Bd μ (A * s₅ ^ (-(1 : ℝ))) (s₅ ^ (-θ)) t₅) :
    |t₁.a * t₂.a * t₃.a * t₄.a * t₅.a - t₁.b * t₂.b * t₃.b * t₄.b * t₅.b -
        t₁.c * t₂.c * t₃.c * t₄.c * t₅.c + t₁.d * t₂.d * t₃.d * t₄.d * t₅.d| ≤
      5120 * A ^ 5 * μ ^ 2 * (s₁ ^ (-(1 : ℝ)) * s₂ ^ (-(1 : ℝ)) * s₃ ^ (-(1 : ℝ)) *
        s₄ ^ (-(1 : ℝ)) * s₅ ^ (-(1 : ℝ))) *
      ((s₁ ^ (-θ)) ^ 2 + (s₂ ^ (-θ)) ^ 2 + (s₃ ^ (-θ)) ^ 2 + (s₄ ^ (-θ)) ^ 2 +
        (s₅ ^ (-θ)) ^ 2) := by
  refine (I3PsiDiffTable.abs_prod_five_le_sq hμ (Real.rpow_nonneg h₁.le _)
    (Real.rpow_nonneg h₂.le _) (Real.rpow_nonneg h₃.le _) (Real.rpow_nonneg h₄.le _)
    (Real.rpow_nonneg h₅.le _) b₁ b₂ b₃ b₄ b₅).trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem abs_const_mul_eq {c a b : ℝ} (hc : 0 < c) (h : a = b) : |c * a| = c * |b| := by
  rw [h, abs_mul, abs_of_pos hc]

/-- `12 c₀₂³ c₁₃²`. -/
private theorem mono1_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A) {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x₀₂ x₁₃ : SpaceTime}
    (h₀₂ : 0 < torusParabolicSize x₀₂) (h₁₃ : 0 < torusParabolicSize x₁₃) :
    |12 * (Q₁₁ x₀₂ ^ 3 * Q₁₁ x₁₃ ^ 2 - Q₁₂ x₀₂ ^ 3 * Q₁₂ x₁₃ ^ 2 - Q₂₁ x₀₂ ^ 3 * Q₂₁ x₁₃ ^ 2 +
        Q₂₂ x₀₂ ^ 3 * Q₂₂ x₁₃ ^ 2)| ≤ 737280 * A ^ 5 * μ ^ 2 * i3Psi2DiffT1 θ x₀₂ x₁₃ := by
  obtain ⟨b₀₂, -, -⟩ := hT x₀₂ h₀₂
  obtain ⟨b₁₃, -, -⟩ := hT x₁₃ h₁₃
  have key := diff5_le hμ h₀₂ h₀₂ h₀₂ h₁₃ h₁₃ b₀₂ b₀₂ b₀₂ b₁₃ b₁₃
  dsimp only at key
  have hmul := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 12)
  refine le_trans (le_of_eq (abs_const_mul_eq (by norm_num) (by ring))) (hmul.trans ?_)
  unfold i3Psi2DiffT1
  rw [rpow_neg_pq h₀₂ 3 2 (θ := θ) (e := 3 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₁₃ 2 0 (θ := θ) (e := 2) (by push_cast; ring),
    rpow_neg_pq h₀₂ 3 0 (θ := θ) (e := 3) (by push_cast; ring),
    rpow_neg_pq h₁₃ 2 2 (θ := θ) (e := 2 + 2 * θ) (by push_cast; ring)]
  have n02 : 0 ≤ torusParabolicSize x₀₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₂.le _
  have n13 : 0 ≤ torusParabolicSize x₁₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₁₃.le _
  set p₀₂ := torusParabolicSize x₀₂ ^ (-(1 : ℝ))
  set p₁₃ := torusParabolicSize x₁₃ ^ (-(1 : ℝ))
  set q₀₂ := torusParabolicSize x₀₂ ^ (-θ)
  set q₁₃ := torusParabolicSize x₁₃ ^ (-θ)
  have hW : 0 ≤ A ^ 5 * μ ^ 2 * (p₀₂ ^ 3 * p₁₃ ^ 2) := by positivity
  linarith [mul_nonneg hW (sq_nonneg q₀₂), mul_nonneg hW (sq_nonneg q₁₃)]

/-- `72 c₀₂² c₀₃ c₁₂ c₁₃`. -/
private theorem mono2_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A) {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x₀₂ x₀₃ x₁₂ x₁₃ : SpaceTime}
    (h₀₂ : 0 < torusParabolicSize x₀₂) (h₀₃ : 0 < torusParabolicSize x₀₃)
    (h₁₂ : 0 < torusParabolicSize x₁₂) (h₁₃ : 0 < torusParabolicSize x₁₃) :
    |72 * (Q₁₁ x₀₂ ^ 2 * Q₁₁ x₀₃ * Q₁₁ x₁₂ * Q₁₁ x₁₃ - Q₁₂ x₀₂ ^ 2 * Q₁₂ x₀₃ * Q₁₂ x₁₂ * Q₁₂ x₁₃ -
        Q₂₁ x₀₂ ^ 2 * Q₂₁ x₀₃ * Q₂₁ x₁₂ * Q₂₁ x₁₃ + Q₂₂ x₀₂ ^ 2 * Q₂₂ x₀₃ * Q₂₂ x₁₂ * Q₂₂ x₁₃)| ≤
      737280 * A ^ 5 * μ ^ 2 * i3Psi2DiffT2 θ x₀₂ x₀₃ x₁₂ x₁₃ := by
  obtain ⟨b₀₂, -, -⟩ := hT x₀₂ h₀₂
  obtain ⟨b₀₃, -, -⟩ := hT x₀₃ h₀₃
  obtain ⟨b₁₂, -, -⟩ := hT x₁₂ h₁₂
  obtain ⟨b₁₃, -, -⟩ := hT x₁₃ h₁₃
  have key := diff5_le hμ h₀₂ h₀₂ h₀₃ h₁₂ h₁₃ b₀₂ b₀₂ b₀₃ b₁₂ b₁₃
  dsimp only at key
  have hmul := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 72)
  refine le_trans (le_of_eq (abs_const_mul_eq (by norm_num) (by ring))) (hmul.trans ?_)
  unfold i3Psi2DiffT2
  rw [rpow_neg_pq h₀₂ 2 2 (θ := θ) (e := 2 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₀₃ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₁₂ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₁₃ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₂ 2 0 (θ := θ) (e := 2) (by push_cast; ring),
    rpow_neg_pq h₀₃ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₁₂ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₁₃ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring)]
  have n02 : 0 ≤ torusParabolicSize x₀₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₂.le _
  have n03 : 0 ≤ torusParabolicSize x₀₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₃.le _
  have n12 : 0 ≤ torusParabolicSize x₁₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₁₂.le _
  have n13 : 0 ≤ torusParabolicSize x₁₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₁₃.le _
  set p₀₂ := torusParabolicSize x₀₂ ^ (-(1 : ℝ))
  set p₀₃ := torusParabolicSize x₀₃ ^ (-(1 : ℝ))
  set p₁₂ := torusParabolicSize x₁₂ ^ (-(1 : ℝ))
  set p₁₃ := torusParabolicSize x₁₃ ^ (-(1 : ℝ))
  set q₀₂ := torusParabolicSize x₀₂ ^ (-θ)
  set q₀₃ := torusParabolicSize x₀₃ ^ (-θ)
  set q₁₂ := torusParabolicSize x₁₂ ^ (-θ)
  set q₁₃ := torusParabolicSize x₁₃ ^ (-θ)
  have hW : 0 ≤ A ^ 5 * μ ^ 2 * (p₀₂ ^ 2 * p₀₃ * p₁₂ * p₁₃) := by positivity
  linarith [mul_nonneg hW (sq_nonneg q₀₂), mul_nonneg hW (sq_nonneg q₀₃),
    mul_nonneg hW (sq_nonneg q₁₂), mul_nonneg hW (sq_nonneg q₁₃)]

/-- `36 c₀₂ c₀₃² c₁₂²`. -/
private theorem mono3_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A) {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x₀₂ x₀₃ x₁₂ : SpaceTime}
    (h₀₂ : 0 < torusParabolicSize x₀₂) (h₀₃ : 0 < torusParabolicSize x₀₃)
    (h₁₂ : 0 < torusParabolicSize x₁₂) :
    |36 * (Q₁₁ x₀₂ * Q₁₁ x₀₃ ^ 2 * Q₁₁ x₁₂ ^ 2 - Q₁₂ x₀₂ * Q₁₂ x₀₃ ^ 2 * Q₁₂ x₁₂ ^ 2 -
        Q₂₁ x₀₂ * Q₂₁ x₀₃ ^ 2 * Q₂₁ x₁₂ ^ 2 + Q₂₂ x₀₂ * Q₂₂ x₀₃ ^ 2 * Q₂₂ x₁₂ ^ 2)| ≤
      737280 * A ^ 5 * μ ^ 2 * i3Psi2DiffT3 θ x₀₂ x₀₃ x₁₂ := by
  obtain ⟨b₀₂, -, -⟩ := hT x₀₂ h₀₂
  obtain ⟨b₀₃, -, -⟩ := hT x₀₃ h₀₃
  obtain ⟨b₁₂, -, -⟩ := hT x₁₂ h₁₂
  have key := diff5_le hμ h₀₂ h₀₃ h₀₃ h₁₂ h₁₂ b₀₂ b₀₃ b₀₃ b₁₂ b₁₂
  dsimp only at key
  have hmul := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 36)
  refine le_trans (le_of_eq (abs_const_mul_eq (by norm_num) (by ring))) (hmul.trans ?_)
  unfold i3Psi2DiffT3
  rw [rpow_neg_pq h₀₂ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₀₃ 2 0 (θ := θ) (e := 2) (by push_cast; ring),
    rpow_neg_pq h₁₂ 2 0 (θ := θ) (e := 2) (by push_cast; ring),
    rpow_neg_pq h₀₂ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₃ 2 2 (θ := θ) (e := 2 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₁₂ 2 2 (θ := θ) (e := 2 + 2 * θ) (by push_cast; ring)]
  have n02 : 0 ≤ torusParabolicSize x₀₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₂.le _
  have n03 : 0 ≤ torusParabolicSize x₀₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₃.le _
  have n12 : 0 ≤ torusParabolicSize x₁₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₁₂.le _
  set p₀₂ := torusParabolicSize x₀₂ ^ (-(1 : ℝ))
  set p₀₃ := torusParabolicSize x₀₃ ^ (-(1 : ℝ))
  set p₁₂ := torusParabolicSize x₁₂ ^ (-(1 : ℝ))
  set q₀₂ := torusParabolicSize x₀₂ ^ (-θ)
  set q₀₃ := torusParabolicSize x₀₃ ^ (-θ)
  set q₁₂ := torusParabolicSize x₁₂ ^ (-θ)
  have hW : 0 ≤ A ^ 5 * μ ^ 2 * (p₀₂ * p₀₃ ^ 2 * p₁₂ ^ 2) := by positivity
  linarith [mul_nonneg hW (sq_nonneg q₀₂), mul_nonneg hW (sq_nonneg q₀₃),
    mul_nonneg hW (sq_nonneg q₁₂)]

/-- **Second difference of the chaos-`5` kernel.** -/
theorem i3Psi2DiffChi5_abs_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂)
    {x₀₂ x₀₃ x₁₂ x₁₃ : SpaceTime} (h₀₂ : 0 < torusParabolicSize x₀₂)
    (h₀₃ : 0 < torusParabolicSize x₀₃) (h₁₂ : 0 < torusParabolicSize x₁₂)
    (h₁₃ : 0 < torusParabolicSize x₁₃) :
    |i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ x₀₂ x₀₃ x₁₂ x₁₃| ≤
      737280 * A ^ 5 * μ ^ 2 * (i3Psi2DiffT1 θ x₀₂ x₁₃ + i3Psi2DiffT2 θ x₀₂ x₀₃ x₁₂ x₁₃ +
        i3Psi2DiffT3 θ x₀₂ x₀₃ x₁₂) := by
  have m1 := mono1_le hμ hA hT h₀₂ h₁₃
  have m2 := mono2_le hμ hA hT h₀₂ h₀₃ h₁₂ h₁₃
  have m3 := mono3_le hμ hA hT h₀₂ h₀₃ h₁₂
  have e : i3Psi2DiffChi5 Q₁₁ Q₁₂ Q₂₁ Q₂₂ x₀₂ x₀₃ x₁₂ x₁₃ =
      12 * (Q₁₁ x₀₂ ^ 3 * Q₁₁ x₁₃ ^ 2 - Q₁₂ x₀₂ ^ 3 * Q₁₂ x₁₃ ^ 2 - Q₂₁ x₀₂ ^ 3 * Q₂₁ x₁₃ ^ 2 +
        Q₂₂ x₀₂ ^ 3 * Q₂₂ x₁₃ ^ 2) +
      72 * (Q₁₁ x₀₂ ^ 2 * Q₁₁ x₀₃ * Q₁₁ x₁₂ * Q₁₁ x₁₃ - Q₁₂ x₀₂ ^ 2 * Q₁₂ x₀₃ * Q₁₂ x₁₂ * Q₁₂ x₁₃ -
        Q₂₁ x₀₂ ^ 2 * Q₂₁ x₀₃ * Q₂₁ x₁₂ * Q₂₁ x₁₃ + Q₂₂ x₀₂ ^ 2 * Q₂₂ x₀₃ * Q₂₂ x₁₂ * Q₂₂ x₁₃) +
      36 * (Q₁₁ x₀₂ * Q₁₁ x₀₃ ^ 2 * Q₁₁ x₁₂ ^ 2 - Q₁₂ x₀₂ * Q₁₂ x₀₃ ^ 2 * Q₁₂ x₁₂ ^ 2 -
        Q₂₁ x₀₂ * Q₂₁ x₀₃ ^ 2 * Q₂₁ x₁₂ ^ 2 + Q₂₂ x₀₂ * Q₂₂ x₀₃ ^ 2 * Q₂₂ x₁₂ ^ 2) := by
    unfold i3Psi2DiffChi5 i3Psi2Kernel5
    ring
  rw [e]
  refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  linarith [m1, m2, m3]

/-- `72 c₀₁ c₀₂² c₁₃ c₂₃`. -/
private theorem mono4_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A) {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x₀₁ x₀₂ x₁₃ x₂₃ : SpaceTime}
    (h₀₁ : 0 < torusParabolicSize x₀₁) (h₀₂ : 0 < torusParabolicSize x₀₂)
    (h₁₃ : 0 < torusParabolicSize x₁₃) (h₂₃ : 0 < torusParabolicSize x₂₃) :
    |72 * (Q₁₁ x₀₁ * Q₁₁ x₀₂ ^ 2 * Q₁₁ x₁₃ * Q₁₁ x₂₃ - Q₁₁ x₀₁ * Q₁₂ x₀₂ ^ 2 * Q₁₂ x₁₃ * Q₂₂ x₂₃ -
        Q₂₂ x₀₁ * Q₂₁ x₀₂ ^ 2 * Q₂₁ x₁₃ * Q₁₁ x₂₃ + Q₂₂ x₀₁ * Q₂₂ x₀₂ ^ 2 * Q₂₂ x₁₃ * Q₂₂ x₂₃)| ≤
      737280 * A ^ 5 * μ ^ 2 * i3Psi2DiffT4 θ x₀₁ x₀₂ x₁₃ x₂₃ := by
  obtain ⟨-, b₀₁, -⟩ := hT x₀₁ h₀₁
  obtain ⟨b₀₂, -, -⟩ := hT x₀₂ h₀₂
  obtain ⟨b₁₃, -, -⟩ := hT x₁₃ h₁₃
  obtain ⟨-, -, b₂₃⟩ := hT x₂₃ h₂₃
  have key := diff5_le hμ h₀₁ h₀₂ h₀₂ h₁₃ h₂₃ b₀₁ b₀₂ b₀₂ b₁₃ b₂₃
  dsimp only at key
  have hmul := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 72)
  refine le_trans (le_of_eq (abs_const_mul_eq (by norm_num) (by ring))) (hmul.trans ?_)
  unfold i3Psi2DiffT4
  rw [rpow_neg_pq h₀₁ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₀₂ 2 0 (θ := θ) (e := 2) (by push_cast; ring),
    rpow_neg_pq h₁₃ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₂₃ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₁ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₂ 2 2 (θ := θ) (e := 2 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₁₃ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₂₃ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring)]
  have n01 : 0 ≤ torusParabolicSize x₀₁ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₁.le _
  have n02 : 0 ≤ torusParabolicSize x₀₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₂.le _
  have n13 : 0 ≤ torusParabolicSize x₁₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₁₃.le _
  have n23 : 0 ≤ torusParabolicSize x₂₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₂₃.le _
  set p₀₁ := torusParabolicSize x₀₁ ^ (-(1 : ℝ))
  set p₀₂ := torusParabolicSize x₀₂ ^ (-(1 : ℝ))
  set p₁₃ := torusParabolicSize x₁₃ ^ (-(1 : ℝ))
  set p₂₃ := torusParabolicSize x₂₃ ^ (-(1 : ℝ))
  set q₀₁ := torusParabolicSize x₀₁ ^ (-θ)
  set q₀₂ := torusParabolicSize x₀₂ ^ (-θ)
  set q₁₃ := torusParabolicSize x₁₃ ^ (-θ)
  set q₂₃ := torusParabolicSize x₂₃ ^ (-θ)
  have hW : 0 ≤ A ^ 5 * μ ^ 2 * (p₀₁ * p₀₂ ^ 2 * p₁₃ * p₂₃) := by positivity
  linarith [mul_nonneg hW (sq_nonneg q₀₁), mul_nonneg hW (sq_nonneg q₀₂),
    mul_nonneg hW (sq_nonneg q₁₃), mul_nonneg hW (sq_nonneg q₂₃)]

/-- `144 c₀₁ c₀₂ c₀₃ c₁₂ c₂₃`. -/
private theorem mono5_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A) {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x₀₁ x₀₃ x₀₂ x₂₃ x₁₂ : SpaceTime}
    (h₀₁ : 0 < torusParabolicSize x₀₁) (h₀₃ : 0 < torusParabolicSize x₀₃)
    (h₀₂ : 0 < torusParabolicSize x₀₂) (h₂₃ : 0 < torusParabolicSize x₂₃)
    (h₁₂ : 0 < torusParabolicSize x₁₂) :
    |144 * (Q₁₁ x₀₁ * Q₁₁ x₀₂ * Q₁₁ x₀₃ * Q₁₁ x₁₂ * Q₁₁ x₂₃ -
        Q₁₁ x₀₁ * Q₁₂ x₀₂ * Q₁₂ x₀₃ * Q₁₂ x₁₂ * Q₂₂ x₂₃ -
        Q₂₂ x₀₁ * Q₂₁ x₀₂ * Q₂₁ x₀₃ * Q₂₁ x₁₂ * Q₁₁ x₂₃ +
        Q₂₂ x₀₁ * Q₂₂ x₀₂ * Q₂₂ x₀₃ * Q₂₂ x₁₂ * Q₂₂ x₂₃)| ≤
      737280 * A ^ 5 * μ ^ 2 * i3Psi2DiffT5 θ x₀₁ x₀₃ x₀₂ x₂₃ x₁₂ := by
  obtain ⟨-, b₀₁, -⟩ := hT x₀₁ h₀₁
  obtain ⟨b₀₃, -, -⟩ := hT x₀₃ h₀₃
  obtain ⟨b₀₂, -, -⟩ := hT x₀₂ h₀₂
  obtain ⟨-, -, b₂₃⟩ := hT x₂₃ h₂₃
  obtain ⟨b₁₂, -, -⟩ := hT x₁₂ h₁₂
  have key := diff5_le hμ h₀₁ h₀₂ h₀₃ h₁₂ h₂₃ b₀₁ b₀₂ b₀₃ b₁₂ b₂₃
  dsimp only at key
  have hmul := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 144)
  refine le_trans (le_of_eq (abs_const_mul_eq (by norm_num) (by ring))) (hmul.trans ?_)
  unfold i3Psi2DiffT5
  rw [rpow_neg_pq h₀₁ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₀₃ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₂ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₂₃ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₁₂ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₁ 1 0 (θ := θ) (e := 1) (by push_cast; ring),
    rpow_neg_pq h₀₃ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₀₂ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₂₃ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring),
    rpow_neg_pq h₁₂ 1 2 (θ := θ) (e := 1 + 2 * θ) (by push_cast; ring)]
  have n01 : 0 ≤ torusParabolicSize x₀₁ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₁.le _
  have n03 : 0 ≤ torusParabolicSize x₀₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₃.le _
  have n02 : 0 ≤ torusParabolicSize x₀₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₀₂.le _
  have n23 : 0 ≤ torusParabolicSize x₂₃ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₂₃.le _
  have n12 : 0 ≤ torusParabolicSize x₁₂ ^ (-(1 : ℝ)) := Real.rpow_nonneg h₁₂.le _
  set p₀₁ := torusParabolicSize x₀₁ ^ (-(1 : ℝ))
  set p₀₃ := torusParabolicSize x₀₃ ^ (-(1 : ℝ))
  set p₀₂ := torusParabolicSize x₀₂ ^ (-(1 : ℝ))
  set p₂₃ := torusParabolicSize x₂₃ ^ (-(1 : ℝ))
  set p₁₂ := torusParabolicSize x₁₂ ^ (-(1 : ℝ))
  set q₀₁ := torusParabolicSize x₀₁ ^ (-θ)
  set q₀₃ := torusParabolicSize x₀₃ ^ (-θ)
  set q₀₂ := torusParabolicSize x₀₂ ^ (-θ)
  set q₂₃ := torusParabolicSize x₂₃ ^ (-θ)
  set q₁₂ := torusParabolicSize x₁₂ ^ (-θ)
  have hW : 0 ≤ A ^ 5 * μ ^ 2 * (p₀₁ * p₀₃ * p₀₂ * p₂₃ * p₁₂) := by positivity
  linarith [mul_nonneg hW (sq_nonneg q₀₁), mul_nonneg hW (sq_nonneg q₀₃),
    mul_nonneg hW (sq_nonneg q₀₂), mul_nonneg hW (sq_nonneg q₂₃), mul_nonneg hW (sq_nonneg q₁₂)]

/-- **Second difference of the chaos-`3` kernel.** -/
theorem i3Psi2DiffChi3_abs_le {A μ θ : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ} (hT : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂)
    {x₀₁ x₂₃ x₀₂ x₀₃ x₁₂ x₁₃ : SpaceTime} (h₀₁ : 0 < torusParabolicSize x₀₁)
    (h₂₃ : 0 < torusParabolicSize x₂₃) (h₀₂ : 0 < torusParabolicSize x₀₂)
    (h₀₃ : 0 < torusParabolicSize x₀₃) (h₁₂ : 0 < torusParabolicSize x₁₂)
    (h₁₃ : 0 < torusParabolicSize x₁₃) :
    |i3Psi2DiffChi3 Q₁₁ Q₁₂ Q₂₁ Q₂₂ x₀₁ x₂₃ x₀₂ x₀₃ x₁₂ x₁₃| ≤
      737280 * A ^ 5 * μ ^ 2 * (i3Psi2DiffT4 θ x₀₁ x₀₂ x₁₃ x₂₃ +
        i3Psi2DiffT5 θ x₀₁ x₀₃ x₀₂ x₂₃ x₁₂) := by
  have m4 := mono4_le hμ hA hT h₀₁ h₀₂ h₁₃ h₂₃
  have m5 := mono5_le hμ hA hT h₀₁ h₀₃ h₀₂ h₂₃ h₁₂
  have e : i3Psi2DiffChi3 Q₁₁ Q₁₂ Q₂₁ Q₂₂ x₀₁ x₂₃ x₀₂ x₀₃ x₁₂ x₁₃ =
      72 * (Q₁₁ x₀₁ * Q₁₁ x₀₂ ^ 2 * Q₁₁ x₁₃ * Q₁₁ x₂₃ - Q₁₁ x₀₁ * Q₁₂ x₀₂ ^ 2 * Q₁₂ x₁₃ * Q₂₂ x₂₃ -
        Q₂₂ x₀₁ * Q₂₁ x₀₂ ^ 2 * Q₂₁ x₁₃ * Q₁₁ x₂₃ + Q₂₂ x₀₁ * Q₂₂ x₀₂ ^ 2 * Q₂₂ x₁₃ * Q₂₂ x₂₃) +
      144 * (Q₁₁ x₀₁ * Q₁₁ x₀₂ * Q₁₁ x₀₃ * Q₁₁ x₁₂ * Q₁₁ x₂₃ -
        Q₁₁ x₀₁ * Q₁₂ x₀₂ * Q₁₂ x₀₃ * Q₁₂ x₁₂ * Q₂₂ x₂₃ -
        Q₂₂ x₀₁ * Q₂₁ x₀₂ * Q₂₁ x₀₃ * Q₂₁ x₁₂ * Q₁₁ x₂₃ +
        Q₂₂ x₀₁ * Q₂₂ x₀₂ * Q₂₂ x₀₃ * Q₂₂ x₁₂ * Q₂₂ x₂₃) := by
    unfold i3Psi2DiffChi3 i3Psi2Kernel3
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith [m4, m5]

end RegularityStructures.Phi43

end

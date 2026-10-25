/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mixed second differences of products of `2 × 2` tables

A `2 × 2` table `t = (a, b, c, d)` has entries `a = t(1,1)`, `b = t(1,2)`, `c = t(2,1)`,
`d = t(2,2)` (indexed by the two scales `(ε, ε')`).  Its Walsh coordinates are the mean
`(a + b + c + d)/4`, the two first differences `du = (a + b - c - d)/4`, `dv = (a - b + c - d)/4` and
the mixed second difference `dw = (a - b - c + d)/4`.  The entrywise product of tables multiplies the
Walsh coordinates as in the group algebra of `ℤ/2 × ℤ/2`.  If every Walsh coordinate of a table is
bounded by `P`, the first differences by `μ P Q` and the mixed difference by `μ² P Q²`, then the
product of two tables satisfies the same bounds with `(4 P₁ P₂, Q₁ + Q₂)`.  Iterating, the mixed second
difference of a product of four tables is bounded by `256 μ² P₁P₂P₃P₄ (Q₁ + Q₂ + Q₃ + Q₄)²`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- A `2 × 2` table with entries `a = t(1,1)`, `b = t(1,2)`, `c = t(2,1)`, `d = t(2,2)`. -/
structure I3PsiDiffTable where
  /-- The entry `(1,1)`. -/
  a : ℝ
  /-- The entry `(1,2)`. -/
  b : ℝ
  /-- The entry `(2,1)`. -/
  c : ℝ
  /-- The entry `(2,2)`. -/
  d : ℝ

namespace I3PsiDiffTable

/-- The entrywise product. -/
def mul (s t : I3PsiDiffTable) : I3PsiDiffTable :=
  ⟨s.a * t.a, s.b * t.b, s.c * t.c, s.d * t.d⟩

/-- The mean `(a + b + c + d)/4`. -/
def mean (t : I3PsiDiffTable) : ℝ := (t.a + t.b + t.c + t.d) / 4

/-- The first difference in the first index, `(a + b - c - d)/4`. -/
def du (t : I3PsiDiffTable) : ℝ := (t.a + t.b - t.c - t.d) / 4

/-- The first difference in the second index, `(a - b + c - d)/4`. -/
def dv (t : I3PsiDiffTable) : ℝ := (t.a - t.b + t.c - t.d) / 4

/-- The mixed second difference `(a - b - c + d)/4`. -/
def dw (t : I3PsiDiffTable) : ℝ := (t.a - t.b - t.c + t.d) / 4

/-- The bound data of a table: Walsh coordinates bounded by `P`, first differences by `μ P Q`,
the mixed difference by `μ² P Q²`. -/
def Bd (μ P Q : ℝ) (t : I3PsiDiffTable) : Prop :=
  |t.mean| ≤ P ∧ |t.du| ≤ P ∧ |t.dv| ≤ P ∧ |t.dw| ≤ P ∧ |t.du| ≤ μ * P * Q ∧
    |t.dv| ≤ μ * P * Q ∧ |t.dw| ≤ μ ^ 2 * P * Q ^ 2

end I3PsiDiffTable

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

namespace I3PsiDiffTable

private theorem abs_mul_le_mul' {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

private theorem abs_add_four_le (x y z w : ℝ) : |x + y + z + w| ≤ |x| + |y| + |z| + |w| := by
  have h1 := abs_add_le (x + y + z) w
  have h2 := abs_add_le (x + y) z
  have h3 := abs_add_le x y
  linarith

private theorem abs_four_prod_le {a1 a2 b1 b2 c1 c2 d1 d2 P1 P2 : ℝ} (ha1 : |a1| ≤ P1)
    (ha2 : |a2| ≤ P2) (hb1 : |b1| ≤ P1) (hb2 : |b2| ≤ P2) (hc1 : |c1| ≤ P1) (hc2 : |c2| ≤ P2)
    (hd1 : |d1| ≤ P1) (hd2 : |d2| ≤ P2) :
    |a1 * a2 + b1 * b2 + c1 * c2 + d1 * d2| ≤ 4 * P1 * P2 := by
  have := abs_add_four_le (a1 * a2) (b1 * b2) (c1 * c2) (d1 * d2)
  have e1 := abs_mul_le_mul' ha1 ha2
  have e2 := abs_mul_le_mul' hb1 hb2
  have e3 := abs_mul_le_mul' hc1 hc2
  have e4 := abs_mul_le_mul' hd1 hd2
  linarith

theorem mean_mul (s t : I3PsiDiffTable) :
    (s.mul t).mean = s.mean * t.mean + s.du * t.du + s.dv * t.dv + s.dw * t.dw := by
  simp only [mul, mean, du, dv, dw]; ring

theorem du_mul (s t : I3PsiDiffTable) :
    (s.mul t).du = s.mean * t.du + s.du * t.mean + s.dv * t.dw + s.dw * t.dv := by
  simp only [mul, mean, du, dv, dw]; ring

theorem dv_mul (s t : I3PsiDiffTable) :
    (s.mul t).dv = s.mean * t.dv + s.dv * t.mean + s.du * t.dw + s.dw * t.du := by
  simp only [mul, mean, du, dv, dw]; ring

theorem dw_mul (s t : I3PsiDiffTable) :
    (s.mul t).dw = s.mean * t.dw + s.dw * t.mean + s.du * t.dv + s.dv * t.du := by
  simp only [mul, mean, du, dv, dw]; ring

/-- The bound data of a product of two tables. -/
theorem Bd.mul {μ P₁ P₂ Q₁ Q₂ : ℝ} {s t : I3PsiDiffTable} (hμ : 0 ≤ μ) (hQ₁ : 0 ≤ Q₁)
    (hQ₂ : 0 ≤ Q₂) (hs : Bd μ P₁ Q₁ s) (ht : Bd μ P₂ Q₂ t) :
    Bd μ (4 * P₁ * P₂) (Q₁ + Q₂) (s.mul t) := by
  obtain ⟨sm, su, sv, sw, sug, svg, swg⟩ := hs
  obtain ⟨tm, tu, tv, tw, tug, tvg, twg⟩ := ht
  have hP₁ : 0 ≤ P₁ := (abs_nonneg _).trans sm
  have hP₂ : 0 ≤ P₂ := (abs_nonneg _).trans tm
  have hnn : 0 ≤ μ * (P₁ * P₂) * (Q₁ + Q₂) := by positivity
  have hnn2 : 0 ≤ μ ^ 2 * (P₁ * P₂) * (Q₁ + Q₂) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mean_mul]; exact abs_four_prod_le sm tm su tu sv tv sw tw
  · rw [du_mul]; exact abs_four_prod_le sm tu su tm sv tw sw tv
  · rw [dv_mul]; exact abs_four_prod_le sm tv sv tm su tw sw tu
  · rw [dw_mul]; exact abs_four_prod_le sm tw sw tm su tv sv tu
  · rw [du_mul]
    refine (abs_add_four_le _ _ _ _).trans ?_
    have e1 := abs_mul_le_mul' sm tug
    have e2 := abs_mul_le_mul' sug tm
    have e3 := abs_mul_le_mul' svg tw
    have e4 := abs_mul_le_mul' sw tvg
    nlinarith
  · rw [dv_mul]
    refine (abs_add_four_le _ _ _ _).trans ?_
    have e1 := abs_mul_le_mul' sm tvg
    have e2 := abs_mul_le_mul' svg tm
    have e3 := abs_mul_le_mul' sug tw
    have e4 := abs_mul_le_mul' sw tug
    nlinarith
  · rw [dw_mul]
    refine (abs_add_four_le _ _ _ _).trans ?_
    have e1 := abs_mul_le_mul' sm twg
    have e2 := abs_mul_le_mul' swg tm
    have e3 := abs_mul_le_mul' sug tvg
    have e4 := abs_mul_le_mul' svg tug
    nlinarith

/-- **Mixed second difference of a product of four tables.**
`|∏ aⱼ - ∏ bⱼ - ∏ cⱼ + ∏ dⱼ| ≤ 256 μ² P₁P₂P₃P₄ (Q₁ + Q₂ + Q₃ + Q₄)²`. -/
theorem abs_prod_four_le {μ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : ℝ} {t₁ t₂ t₃ t₄ : I3PsiDiffTable}
    (hμ : 0 ≤ μ) (h₁ : 0 ≤ Q₁) (h₂ : 0 ≤ Q₂) (h₃ : 0 ≤ Q₃) (h₄ : 0 ≤ Q₄)
    (b₁ : Bd μ P₁ Q₁ t₁) (b₂ : Bd μ P₂ Q₂ t₂) (b₃ : Bd μ P₃ Q₃ t₃) (b₄ : Bd μ P₄ Q₄ t₄) :
    |t₁.a * t₂.a * t₃.a * t₄.a - t₁.b * t₂.b * t₃.b * t₄.b - t₁.c * t₂.c * t₃.c * t₄.c +
        t₁.d * t₂.d * t₃.d * t₄.d| ≤
      256 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄) * (Q₁ + Q₂ + Q₃ + Q₄) ^ 2 := by
  have b12 := Bd.mul hμ h₁ h₂ b₁ b₂
  have b123 := Bd.mul hμ (add_nonneg h₁ h₂) h₃ b12 b₃
  have b1234 := Bd.mul hμ (add_nonneg (add_nonneg h₁ h₂) h₃) h₄ b123 b₄
  have hw := b1234.2.2.2.2.2.2
  have e : t₁.a * t₂.a * t₃.a * t₄.a - t₁.b * t₂.b * t₃.b * t₄.b - t₁.c * t₂.c * t₃.c * t₄.c +
      t₁.d * t₂.d * t₃.d * t₄.d = 4 * (((t₁.mul t₂).mul t₃).mul t₄).dw := by
    simp only [mul, dw]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have : 4 * (μ ^ 2 * (4 * (4 * (4 * P₁ * P₂) * P₃) * P₄) * (Q₁ + Q₂ + Q₃ + Q₄) ^ 2) =
      256 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄) * (Q₁ + Q₂ + Q₃ + Q₄) ^ 2 := by ring
  rw [← this]
  exact mul_le_mul_of_nonneg_left hw (by norm_num)

/-- **Mixed second difference of a product of four tables, quadratic form.**
`|∏ aⱼ - ∏ bⱼ - ∏ cⱼ + ∏ dⱼ| ≤ 1024 μ² P₁P₂P₃P₄ (Q₁² + Q₂² + Q₃² + Q₄²)`. -/
theorem abs_prod_four_le_sq {μ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : ℝ} {t₁ t₂ t₃ t₄ : I3PsiDiffTable}
    (hμ : 0 ≤ μ) (h₁ : 0 ≤ Q₁) (h₂ : 0 ≤ Q₂) (h₃ : 0 ≤ Q₃) (h₄ : 0 ≤ Q₄)
    (b₁ : Bd μ P₁ Q₁ t₁) (b₂ : Bd μ P₂ Q₂ t₂) (b₃ : Bd μ P₃ Q₃ t₃) (b₄ : Bd μ P₄ Q₄ t₄) :
    |t₁.a * t₂.a * t₃.a * t₄.a - t₁.b * t₂.b * t₃.b * t₄.b - t₁.c * t₂.c * t₃.c * t₄.c +
        t₁.d * t₂.d * t₃.d * t₄.d| ≤
      1024 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄) * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2 + Q₄ ^ 2) := by
  refine (abs_prod_four_le hμ h₁ h₂ h₃ h₄ b₁ b₂ b₃ b₄).trans ?_
  have hP₁ : 0 ≤ P₁ := (abs_nonneg _).trans b₁.1
  have hP₂ : 0 ≤ P₂ := (abs_nonneg _).trans b₂.1
  have hP₃ : 0 ≤ P₃ := (abs_nonneg _).trans b₃.1
  have hP₄ : 0 ≤ P₄ := (abs_nonneg _).trans b₄.1
  have hcs : (Q₁ + Q₂ + Q₃ + Q₄) ^ 2 ≤ 4 * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2 + Q₄ ^ 2) := by
    nlinarith [sq_nonneg (Q₁ - Q₂), sq_nonneg (Q₁ - Q₃), sq_nonneg (Q₁ - Q₄),
      sq_nonneg (Q₂ - Q₃), sq_nonneg (Q₂ - Q₄), sq_nonneg (Q₃ - Q₄)]
  have hc : 0 ≤ 256 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄) := by positivity
  calc 256 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄) * (Q₁ + Q₂ + Q₃ + Q₄) ^ 2
      ≤ 256 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄) * (4 * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2 + Q₄ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hc
    _ = _ := by ring

end I3PsiDiffTable

end RegularityStructures.Phi43

end

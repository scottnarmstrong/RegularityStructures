/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DifferenceTables
public import Phi43.BPHZ.TreeI3PsiDifferenceAlgebra

/-!
# The second difference of the chaos kernels of `I(Ψ²) Ψ²`: algebra

Write `T_z = (Q_{aa}(z), Q_{ab}(z), Q_{ba}(z), Q_{bb}(z))` for the table of cross covariances at a
point `z`, and `D(t₁, t₂, t₃, t₄) = ∏ tᵢ.a - ∏ tᵢ.b - ∏ tᵢ.c + ∏ tᵢ.d` for the mixed second difference
of a product of tables.  With `c₀₂ = Q(w - w')`, `c₀₃ = Q(w - y')`, `c₁₂ = Q(y - w')`,
`c₁₃ = Q(y - y')` the second difference of the chaos-`4` kernel
`4 c₀₂² c₁₃² + 4 c₀₃² c₁₂² + 16 c₀₂ c₀₃ c₁₂ c₁₃` is
`4 D(T₀₂,T₀₂,T₁₃,T₁₃) + 4 D(T₀₃,T₀₃,T₁₂,T₁₂) + 16 D(T₀₂,T₀₃,T₁₂,T₁₃)`; that of the chaos-`2` kernel
`16 c₀₁ c₂₃ (c₀₂ c₁₃ + c₀₃ c₁₂)` is `16 D(T₀₁,T₂₃,T₀₂,T₁₃) + 16 D(T₀₁,T₂₃,T₀₃,T₁₂)`
(with the tables `(a, a, d, d)` for `c₀₁` and `(a, d, a, d)` for `c₂₃`).

If the tables satisfy the bound data `Bd μ (A pᵢ) (2 qᵢ)`, the mixed second differences are bounded by
`65536 A⁴ μ²` times the sums `i2Psi2Mon4` and `i2Psi2Mon2` of eight monomials in the `pᵢ`, `qᵢ`, in
which exactly one factor `pᵢ` is replaced by `pᵢ qᵢ²`.
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- Two monomials of the chaos-`4` second difference: `p² q² p'² + p² (p'² q'²)`. -/
def i2Psi2Mon4a (p p' q q' : ℝ) : ℝ := p ^ 2 * q ^ 2 * p' ^ 2 + p ^ 2 * (p' ^ 2 * q' ^ 2)

/-- Four monomials of the chaos-`4` second difference (the cross term). -/
def i2Psi2Mon4c (p02 p03 p12 p13 q02 q03 q12 q13 : ℝ) : ℝ :=
  p03 * q03 ^ 2 * p02 * p12 * p13 + p03 * (p02 * q02 ^ 2) * p12 * p13 +
    p03 * p02 * (p12 * q12 ^ 2) * p13 + p03 * p02 * p12 * (p13 * q13 ^ 2)

/-- The eight monomials of the chaos-`4` second difference. -/
def i2Psi2Mon4 (p02 p03 p12 p13 q02 q03 q12 q13 : ℝ) : ℝ :=
  i2Psi2Mon4a p02 p13 q02 q13 + i2Psi2Mon4a p03 p12 q03 q12 +
    i2Psi2Mon4c p02 p03 p12 p13 q02 q03 q12 q13

/-- Four monomials of the chaos-`2` second difference. -/
def i2Psi2Mon2a (p01 p23 pa pb q01 q23 qa qb : ℝ) : ℝ :=
  p01 * q01 ^ 2 * pa * p23 * pb + p01 * (pa * qa ^ 2) * p23 * pb +
    p01 * pa * (p23 * q23 ^ 2) * pb + p01 * pa * p23 * (pb * qb ^ 2)

/-- The eight monomials of the chaos-`2` second difference. -/
def i2Psi2Mon2 (p01 p23 p02 p03 p12 p13 q01 q23 q02 q03 q12 q13 : ℝ) : ℝ :=
  i2Psi2Mon2a p01 p23 p02 p13 q01 q23 q02 q13 + i2Psi2Mon2a p01 p23 p03 p12 q01 q23 q03 q12

/-- The mixed second difference of a product of four tables. -/
def i2Psi2Dm (t₁ t₂ t₃ t₄ : I3PsiDiffTable) : ℝ :=
  t₁.a * t₂.a * t₃.a * t₄.a - t₁.b * t₂.b * t₃.b * t₄.b - t₁.c * t₂.c * t₃.c * t₄.c +
    t₁.d * t₂.d * t₃.d * t₄.d

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

theorem i2Psi2Mon4a_nonneg {p p' q q' : ℝ} : 0 ≤ i2Psi2Mon4a p p' q q' := by
  unfold i2Psi2Mon4a
  positivity

/-- **Chaos `4`, abstract bound.** -/
theorem abs_i2Psi2Dm_chaos4_le {μ A p02 p03 p12 p13 q02 q03 q12 q13 : ℝ}
    {T02 T03 T12 T13 : I3PsiDiffTable} (hμ : 0 ≤ μ) (g02 : 0 ≤ q02) (g03 : 0 ≤ q03)
    (g12 : 0 ≤ q12) (g13 : 0 ≤ q13) (b02 : I3PsiDiffTable.Bd μ (A * p02) (2 * q02) T02)
    (b03 : I3PsiDiffTable.Bd μ (A * p03) (2 * q03) T03)
    (b12 : I3PsiDiffTable.Bd μ (A * p12) (2 * q12) T12)
    (b13 : I3PsiDiffTable.Bd μ (A * p13) (2 * q13) T13) :
    |4 * i2Psi2Dm T02 T02 T13 T13 + 4 * i2Psi2Dm T03 T03 T12 T12 +
        16 * i2Psi2Dm T02 T03 T12 T13| ≤
      65536 * A ^ 4 * μ ^ 2 * i2Psi2Mon4 p02 p03 p12 p13 q02 q03 q12 q13 := by
  have d1 := I3PsiDiffTable.abs_prod_four_le_sq hμ (by positivity) (by positivity)
    (by positivity) (by positivity) b02 b02 b13 b13
  have d2 := I3PsiDiffTable.abs_prod_four_le_sq hμ (by positivity) (by positivity)
    (by positivity) (by positivity) b03 b03 b12 b12
  have d3 := I3PsiDiffTable.abs_prod_four_le_sq hμ (by positivity) (by positivity)
    (by positivity) (by positivity) b02 b03 b12 b13
  have d1' : |i2Psi2Dm T02 T02 T13 T13| ≤ 8192 * A ^ 4 * μ ^ 2 * i2Psi2Mon4a p02 p13 q02 q13 := by
    unfold i2Psi2Dm i2Psi2Mon4a
    exact d1.trans (le_of_eq (by ring))
  have d2' : |i2Psi2Dm T03 T03 T12 T12| ≤ 8192 * A ^ 4 * μ ^ 2 * i2Psi2Mon4a p03 p12 q03 q12 := by
    unfold i2Psi2Dm i2Psi2Mon4a
    exact d2.trans (le_of_eq (by ring))
  have d3' : |i2Psi2Dm T02 T03 T12 T13| ≤
      4096 * A ^ 4 * μ ^ 2 * i2Psi2Mon4c p02 p03 p12 p13 q02 q03 q12 q13 := by
    unfold i2Psi2Dm i2Psi2Mon4c
    exact d3.trans (le_of_eq (by ring))
  have tri := abs_add_three (4 * i2Psi2Dm T02 T02 T13 T13) (4 * i2Psi2Dm T03 T03 T12 T12)
    (16 * i2Psi2Dm T02 T03 T12 T13)
  have a4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  have a16 : |(16 : ℝ)| = 16 := abs_of_pos (by norm_num)
  rw [abs_mul, abs_mul, abs_mul, a4, a16] at tri
  have n1 : 0 ≤ A ^ 4 * μ ^ 2 * i2Psi2Mon4a p02 p13 q02 q13 :=
    mul_nonneg (by positivity) i2Psi2Mon4a_nonneg
  have n2 : 0 ≤ A ^ 4 * μ ^ 2 * i2Psi2Mon4a p03 p12 q03 q12 :=
    mul_nonneg (by positivity) i2Psi2Mon4a_nonneg
  unfold i2Psi2Mon4
  linarith [tri, d1', d2', d3', n1, n2]

/-- **Chaos `2`, abstract bound.** -/
theorem abs_i2Psi2Dm_chaos2_le {μ A p01 p23 p02 p03 p12 p13 q01 q23 q02 q03 q12 q13 : ℝ}
    {T01 T23 T02 T03 T12 T13 : I3PsiDiffTable} (hμ : 0 ≤ μ) (g01 : 0 ≤ q01) (g23 : 0 ≤ q23) (g02 : 0 ≤ q02) (g03 : 0 ≤ q03) (g12 : 0 ≤ q12)
    (g13 : 0 ≤ q13) (b01 : I3PsiDiffTable.Bd μ (A * p01) (2 * q01) T01)
    (b23 : I3PsiDiffTable.Bd μ (A * p23) (2 * q23) T23)
    (b02 : I3PsiDiffTable.Bd μ (A * p02) (2 * q02) T02)
    (b03 : I3PsiDiffTable.Bd μ (A * p03) (2 * q03) T03)
    (b12 : I3PsiDiffTable.Bd μ (A * p12) (2 * q12) T12)
    (b13 : I3PsiDiffTable.Bd μ (A * p13) (2 * q13) T13) :
    |16 * i2Psi2Dm T01 T23 T02 T13 + 16 * i2Psi2Dm T01 T23 T03 T12| ≤
      65536 * A ^ 4 * μ ^ 2 * i2Psi2Mon2 p01 p23 p02 p03 p12 p13 q01 q23 q02 q03 q12 q13 := by
  have d1 := I3PsiDiffTable.abs_prod_four_le_sq hμ (by positivity) (by positivity)
    (by positivity) (by positivity) b01 b23 b02 b13
  have d2 := I3PsiDiffTable.abs_prod_four_le_sq hμ (by positivity) (by positivity)
    (by positivity) (by positivity) b01 b23 b03 b12
  have d1' : |i2Psi2Dm T01 T23 T02 T13| ≤
      4096 * A ^ 4 * μ ^ 2 * i2Psi2Mon2a p01 p23 p02 p13 q01 q23 q02 q13 := by
    unfold i2Psi2Dm i2Psi2Mon2a
    exact d1.trans (le_of_eq (by ring))
  have d2' : |i2Psi2Dm T01 T23 T03 T12| ≤
      4096 * A ^ 4 * μ ^ 2 * i2Psi2Mon2a p01 p23 p03 p12 q01 q23 q03 q12 := by
    unfold i2Psi2Dm i2Psi2Mon2a
    exact d2.trans (le_of_eq (by ring))
  have tri := abs_add_le (16 * i2Psi2Dm T01 T23 T02 T13) (16 * i2Psi2Dm T01 T23 T03 T12)
  have a16 : |(16 : ℝ)| = 16 := abs_of_pos (by norm_num)
  rw [abs_mul, abs_mul, a16] at tri
  unfold i2Psi2Mon2
  linarith [tri, d1', d2']

end RegularityStructures.Phi43

end

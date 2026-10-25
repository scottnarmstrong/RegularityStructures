/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.Kernel1
public import Phi43.Potential.TailTest
public import RegularityStructures.Abstract.Singular.ModelPairing.Single

/-!
# The pairing of the noise coordinate with `χ (K - G^m)`

`abs_potConv_potK1_le`: for `0 ≤ z.1 ≤ 1` (near-pair `Γ` hypothesis),

  `|(ξ ⋆ potK1 N)(z)| ≤ r4ModelConst · max(1, C_Γ) C_Π ·
     (potSingConst d 2 + (c₀ + c₁ + c_b) + 432 B_T M_θ latS³)`, `d = deg o`,

where `c_i = potKernelConst` of the unit kernels and `B_T = potTailB N`.
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

/-- The decay constant of the tail kernel. -/
@[expose] noncomputable def potTailB (N : ℕ) : ℝ :=
  Classical.choose (exists_isTailKernel_potTailPhi N)

theorem isTailKernel_potTailPhi (N : ℕ) : IsTailKernel (potTailPhi N) (potTailB N) :=
  Classical.choose_spec (exists_isTailKernel_potTailPhi N)

/-- The three unit kernels `χ(1-e^{-t}) heatShell 0`, `… 1`, and `-χ(1-e^{-t}) ψ_b`. -/
@[expose] noncomputable def potUnitK (N : ℕ) : Fin 3 → ParabolicSpace → ℝ :=
  ![potUnit 0, potUnit 1, potUnitBump N]

theorem isUnitKernel_potUnitK (N : ℕ) (i : Fin 3) : IsUnitKernel (potUnitK N i) := by
  fin_cases i
  · exact isUnitKernel_potUnit 0
  · exact isUnitKernel_potUnit 1
  · exact isUnitKernel_potUnitBump N

theorem sum_potUnitK (N : ℕ) (w : ParabolicSpace) :
    ∑ i, potUnitK N i w = potUnit 0 w + potUnit 1 w + potUnitBump N w := by
  simp [Fin.sum_univ_three, potUnitK]

/-- The sum of the constants of the three unit kernels. -/
@[expose] noncomputable def potUnitConst (N : ℕ) : ℝ := ∑ i, potKernelConst (potUnitK N i)

/-- The constant of the pairing with `χ (K - G^m)` (before the model factor). -/
@[expose] noncomputable def potK1Const (N : ℕ) (d : ℝ) : ℝ :=
  potSingConst d 2 + potUnitConst N + 432 * potTailB N * potThetaConst * latS ^ 3

/-- The family of singular shells `n ≥ 2` centred at `z`. -/
@[expose] noncomputable def singFamily (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) :
    TestFamily ℕ where
  zj _ := z
  g n y := potShellKernel (n + 2) (z - y)
  R n := (2 : ℝ)⁻¹ ^ (n + 2)
  A n := potShellConst (n + 2)
  base _ := hz
  test n := isScaledTest_potShell (n + 2) z

/-- The family of the three unit kernels centred at `z`. -/
@[expose] noncomputable def unitFamily (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) :
    TestFamily (Fin 3) where
  zj _ := z
  g i y := potUnitK N i (z - y)
  R _ := 1
  A i := potKernelConst (potUnitK N i)
  base _ := hz
  test i := isScaledTest_kernel (isUnitKernel_potUnitK N i) z

/-- The family of the spatial pieces of the tail kernel. -/
@[expose] noncomputable def tailFamily (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) :
    TestFamily (Fin 3 → ℤ) where
  zj := tailBase z
  g := tailPiece (potTailPhi N) z
  R _ := 1
  A := tailConst (potTailB N) z
  base _ := hz
  test k := isScaledTest_tail (isTailKernel_potTailPhi N) z k

theorem summable_singFamily_A (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) :
    Summable fun n => (singFamily z hz).A n * (singFamily z hz).R n ^ 5 := by
  have := summable_potSing_terms (d := 0) (by norm_num) 2
  simpa [singFamily] using this

theorem summable_singFamily_term {d : ℝ} (hd : -4 < d) (z : ParabolicSpace)
    (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) (K0 : ℝ) : Summable ((singFamily z hz).term K0 d) := by
  refine ((summable_potSing_terms hd 2).mul_left K0).congr fun n => ?_
  simp only [TestFamily.term, singFamily]
  ring

theorem tsum_singFamily_term {d : ℝ} (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) (K0 : ℝ) :
    ∑' n, (singFamily z hz).term K0 d n = K0 * potSingConst d 2 := by
  unfold potSingConst
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [TestFamily.term, singFamily]
  ring

theorem summable_unitFamily_A (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) :
    Summable fun i => (unitFamily N z hz).A i * (unitFamily N z hz).R i ^ 5 :=
  (hasSum_fintype _).summable

theorem summable_unitFamily_term (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1)
    (K0 d : ℝ) : Summable ((unitFamily N z hz).term K0 d) :=
  (hasSum_fintype _).summable

theorem tsum_unitFamily_term (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1)
    (K0 d : ℝ) : ∑' i, (unitFamily N z hz).term K0 d i = K0 * potUnitConst N := by
  rw [tsum_fintype, potUnitConst, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [TestFamily.term, unitFamily]

theorem summable_tailFamily_A (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) :
    Summable fun k => (tailFamily N z hz).A k * (tailFamily N z hz).R k ^ 5 := by
  simp only [tailFamily, one_pow, mul_one]
  exact ((summable_latRem z.2).mul_left (432 * potTailB N * potThetaConst)).congr fun k => by
    unfold tailConst; ring

theorem summable_tailFamily_term (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1)
    (K0 d : ℝ) : Summable ((tailFamily N z hz).term K0 d) := by
  have := (summable_tailFamily_A N z hz).mul_left K0
  refine this.congr fun k => ?_
  simp [TestFamily.term, tailFamily]

theorem tsum_tailFamily_term_le (N : ℕ) (z : ParabolicSpace) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1) {K0 : ℝ}
    (hK0 : 0 ≤ K0) (d : ℝ) :
    ∑' k, (tailFamily N z hz).term K0 d k ≤ K0 * (432 * potTailB N * potThetaConst * latS ^ 3) := by
  have hB := (isTailKernel_potTailPhi N).pos
  calc ∑' k, (tailFamily N z hz).term K0 d k
      = K0 * (432 * potTailB N * potThetaConst) * ∑' k, latRem z.2 k := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        simp only [TestFamily.term, tailFamily, one_pow, mul_one, Real.one_rpow, tailConst]
        ring
    _ ≤ K0 * (432 * potTailB N * potThetaConst) * latS ^ 3 :=
        mul_le_mul_of_nonneg_left (tsum_latRem_le z.2) (by have := potThetaConst_pos; positivity)
    _ = _ := by ring

theorem potSingConst_nonneg (d : ℝ) (n₀ : ℕ) : 0 ≤ potSingConst d n₀ :=
  tsum_nonneg fun j => mul_nonneg (mul_nonneg (potShellConst_pos _).le (pow_nonneg (by positivity) _))
    (Real.rpow_nonneg (by positivity) _)

theorem potUnitConst_nonneg (N : ℕ) : 0 ≤ potUnitConst N :=
  Finset.sum_nonneg fun i _ => (potKernelConst_pos (isUnitKernel_potUnitK N i)).le

theorem potK1Const_nonneg (N : ℕ) (d : ℝ) : 0 ≤ potK1Const N d := by
  unfold potK1Const
  have := (isTailKernel_potTailPhi N).pos
  have := potThetaConst_pos
  have := potSingConst_nonneg d 2
  have := potUnitConst_nonneg N
  have := latS_nonneg
  positivity

end RegularityStructures.Potential

end

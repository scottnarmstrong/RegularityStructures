/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.GermSplit
public import RegularityStructures.Abstract.Integration.Commute.KConvLinear
public import RegularityStructures.Abstract.Integration.JMapCoeff
public import RegularityStructures.Abstract.Integration.Realising.Germ
public import RegularityStructures.Abstract.Integration.Realising.RealGerm

/-!
# The germ of the realised integral as `K ∗ Π_x e_i` minus a Taylor polynomial

When all homogeneities below `γ` exceed `-2`, `Π_x e_i` is `KRegular` at `x`
(`Model.kRegular_regPi_single`), so `K ∗ Π_x e_i = kConv N (Π_x e_i)` is a function, and the germ
`realGerm M N x i` of [Hai14, Remark 5.10] is this function minus the Taylor polynomial of `K ∗ Π_x e_i`
at `x` of order `deg i + 2`, with the coefficients of `J(x)` (`jCoeff`) [Hai14, (5.11), (5.14)]:

  `realGerm M N x i z = kConv N (Π_x e_i) z - ∑_{|k|_𝔰 < deg i + 2} (z - x)^k / k! · jCoeff M N x i k`

(`realGerm_eq`). Here `(z - x)^k` is `evalParabolic (monomial k 1) (z - x)` and `k!` is `multiFact k`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- `Π_x e_i` is a regular distribution (exponents `> -2`) when all degrees below `γ` exceed `-2`. -/
theorem kRegular_regPi_single (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (hPi : M.PiBoundOn γ CPi univ)
    (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi) {i : ι} (hi : 𝒯.deg i < γ)
    (x : ParabolicSpace) : KRegular (fun t z => M.regPi x (Pi.single i 1) t z) x :=
  ⟨regPi_single_mem_distributions M x i, fun _ hu => M.measurable_pi x i hu,
    𝒯.deg i, max CGam 1 * CPi * Fintype.card ι, 𝒯.degreesBelowLe γ (𝒯.deg i),
    degreesBelowLe_bounds_two hdeg i,
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _),
    M.isLocalOrder_regPi_single hPi hGam hCPi hi x⟩

end Model

/-- **Germ identity** (target 2): `realGerm = K ∗ Π_x e_i - ∑_k (z - x)^k/k! · jCoeff`. -/
theorem realGerm_eq (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {γ CPi CGam : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (hPi : M.PiBoundOn γ CPi univ)
    (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi) {i : ι} (hi : 𝒯.deg i < γ)
    (x z : ParabolicSpace) :
    realGerm M N x i z = kConv N (fun t w => M.regPi x (Pi.single i 1) t w) z -
      ∑ k ∈ taylorIdx (𝒯.deg i + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) * jCoeff M N x i k := by
  have hR := M.kRegular_regPi_single hdeg hPi hGam hCPi hi x
  have hA : ∀ a ∈ 𝒯.degreesBelowLe γ (𝒯.deg i), -4 < a ∧ a ≤ 𝒯.deg i := fun a ha =>
    ⟨by linarith [(degreesBelowLe_bounds_two hdeg i a ha).1],
      (degreesBelowLe_bounds_two hdeg i a ha).2⟩
  have hC : 0 ≤ max CGam 1 * CPi * Fintype.card ι :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _)
  have hterm : ∀ n : ℕ, parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
      (taylorKernel (annKernel0 N) n (𝒯.deg i + 2) x z) =
      parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
        (fun w => annShell N n (z - w)) -
      ∑ k ∈ taylorIdx (𝒯.deg i + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
          parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
            (fun w => lineIter (multiDirs k) (annShell N n) (x - w)) := fun n =>
    pairing_taylorKernel_eq (regPi_single_mem_distributions M x i)
      (fun _ hu => M.measurable_pi x i hu) (contDiff_annKernel0 N)
      (fun _ hz => annKernel0_eq_zero N hz) hA hC (M.isLocalOrder_regPi_single hPi hGam hCPi hi x)
      (𝒯.deg i + 2) n
  unfold realGerm kConv
  simp only [hterm]
  have hs1 := hR.summable_pairing N z
  have hsk : ∀ k ∈ taylorIdx (𝒯.deg i + 2), Summable fun n : ℕ =>
      (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
        parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
          (fun w => lineIter (multiDirs k) (annShell N n) (x - w)) := fun k hk =>
    (summable_jCoeff_terms M N x i k hPi hGam hCPi hi
      (fun j hj => by linarith [hdeg j hj]) ((mem_taylorIdx_iff k).1 hk)).mul_left _
  rw [Summable.tsum_sub hs1 (summable_sum hsk), Summable.tsum_finsetSum hsk]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left]
  rfl

end RegularityStructures

end

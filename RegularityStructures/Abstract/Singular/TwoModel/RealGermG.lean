/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.TaylorTendstoG
public import RegularityStructures.Abstract.Profile.Growth
public import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.SectorLocal
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Abstract.Profile.RealGerm
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The germ of a realised integral under weighted bounds

Weighted versions of `exists_abs_realGermP_le_in`, `polyBounded_realGermP_in` for a model with
`Model.GrowthModel` bounds (no global bounds):

* `summable_pairing_taylorKernel_growthP`: the series defining `realGermP M h x i y`
  converges (for `e_i ∈ V`, `deg i < γ`);
* `polyBounded_monomial_div`: `w ↦ (w - x)^k / m` has polynomial growth;
* `polyBounded_realGermP_growth`: `realGermP M h x i` has polynomial growth.
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

/-- `w ↦ (w - x)^k / m` has polynomial growth. -/
theorem polyBounded_monomial_div (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) (m : ℝ) :
    PolyBounded fun w => evalParabolic (MvPolynomial.monomial k 1) (w - x) / m := by
  set e : ℕ := 2 * k 0 + k 1 + k 2 + k 3 with he
  refine ⟨((continuous_evalParabolic _).comp (continuous_id.sub continuous_const)).measurable.div_const m,
    |m⁻¹| * (1 + parabolicNorm x) ^ e, e, fun w => ?_⟩
  have hz := parabolicNorm_nonneg w
  have hx := parabolicNorm_nonneg x
  have hzx := parabolicNorm_nonneg (w - x)
  have h1 : 1 + parabolicNorm (w - x) ≤ (1 + parabolicNorm x) * (1 + parabolicNorm w) := by
    have h := parabolicNorm_add_le w (-x)
    rw [parabolicNorm_neg, ← sub_eq_add_neg] at h
    have := mul_nonneg hx hz
    linarith [mul_add (1 + parabolicNorm x) 1 (parabolicNorm w)]
  have h2 : |evalParabolic (MvPolynomial.monomial k 1) (w - x)| ≤
      (1 + parabolicNorm x) ^ e * (1 + parabolicNorm w) ^ e := by
    refine (abs_evalParabolic_monomial_le _ _).trans ?_
    calc parabolicNorm (w - x) ^ e ≤ (1 + parabolicNorm (w - x)) ^ e :=
          pow_le_pow_left₀ hzx (by linarith) _
      _ ≤ ((1 + parabolicNorm x) * (1 + parabolicNorm w)) ^ e :=
          pow_le_pow_left₀ (by linarith) h1 e
      _ = _ := mul_pow _ _ _
  beta_reduce
  rw [div_eq_mul_inv, abs_mul, mul_comm, mul_assoc]
  calc |m⁻¹| * |evalParabolic (MvPolynomial.monomial k 1) (w - x)|
      ≤ |m⁻¹| * ((1 + parabolicNorm x) ^ e * (1 + parabolicNorm w) ^ e) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = _ := by ring

namespace Model

variable {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- The series defining the germ `realGermP M h x i y` converges, under weighted bounds. -/
theorem summable_pairing_taylorKernel_growthP (M : Model 𝒯 parabolicSemigroup)
    (hh : ShellProfile h N) (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ) (x y : ParabolicSpace) :
    Summable fun n : ℕ => parabolicSemigroup.pairing
      (fun t z => M.regPi x (Pi.single i 1) t z) (taylorKernel h n (𝒯.deg i + 2) x y) := by
  have hR := G.kRegularG_regPi_single hV hVb hdeg hVi hi x
  have hdeg4 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j :=
    fun j hjV hj => by linarith [hdeg j hjV hj]
  have hloc := G.localGrowth_regPi hV hVb hdeg4 hVi hi x
  have hA : ∀ a ∈ 𝒯.degreesBelowLeIn V γ (𝒯.deg i), -4 < a ∧ a ≤ 𝒯.deg i := fun a ha =>
    ⟨by linarith [(degreesBelowLeIn_bounds_two hdeg i a ha).1],
      (degreesBelowLeIn_bounds_two hdeg i a ha).2⟩
  have hterm : ∀ n : ℕ, parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
      (taylorKernel h n (𝒯.deg i + 2) x y) =
      parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
        (fun w => scaledShell h n (y - w)) -
      ∑ k ∈ taylorIdx (𝒯.deg i + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
          parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
            (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w)) := fun n =>
    pairing_taylorKernel_eq_growth (regPi_single_mem_distributions M x i)
      (fun _ hu => M.measurable_pi x i hu) hh.contDiff
      hh.eq_zero hA hloc.nonneg hloc.nonneg_exp hloc.loc (𝒯.deg i + 2) n
  have hs1 := hR.summable_pairing_growthP hh y
  have hsk : ∀ k ∈ taylorIdx (𝒯.deg i + 2), Summable fun n : ℕ =>
      (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
        parabolicSemigroup.pairing (fun t w => M.regPi x (Pi.single i 1) t w)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w)) := fun k hk =>
    (summable_jCoeff_terms_growthP M hh G x i k hV hVb hVi hi hdeg4
      ((mem_taylorIdx_iff k).1 hk)).mul_left _
  simp only [hterm]
  exact hs1.sub (summable_sum hsk)

/-- The germ `realGermP M h x i` of a model with weighted bounds has polynomial growth. -/
theorem polyBounded_realGermP_growth (M : Model 𝒯 parabolicSemigroup) (hh : ShellProfile h N)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ) (x : ParabolicSpace) :
    PolyBounded (realGermP M h x i) := by
  have hR := G.kRegularG_regPi_single hV hVb hdeg hVi hi x
  have hK := hR.polyBounded_kConv_growthP hh
  have hS : PolyBounded fun w => ∑ k ∈ taylorIdx (𝒯.deg i + 2),
      jCoeffP M h x i k * (evalParabolic (MvPolynomial.monomial k 1) (w - x) / multiFact k) :=
    PolyBounded.finsetSum _ (fun k => jCoeffP M h x i k) _
      fun k _ => polyBounded_monomial_div x k _
  have e : realGermP M h x i = fun w => kConvP h (fun t w => M.regPi x (Pi.single i 1) t w) w -
      ∑ k ∈ taylorIdx (𝒯.deg i + 2),
        jCoeffP M h x i k * (evalParabolic (MvPolynomial.monomial k 1) (w - x) / multiFact k) := by
    funext w
    rw [realGerm_eq_growthP M hh G hV hVb hdeg hVi hi x w]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e]
  exact hK.sub hS

end Model

end RegularityStructures

end

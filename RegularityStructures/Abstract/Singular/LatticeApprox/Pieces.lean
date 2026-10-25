/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.Defs
public import RegularityStructures.Abstract.Singular.ModelPairing.Single

/-!
# Lattice pieces as scaled test functions

* `exists_isScaledTest`: a smooth function supported in `B(z, R)`, `0 < R ≤ 1`, is a scaled test
  function for some constant.
* explicit constants for the pieces `φ^λ_x χ_{n,k}` and `φ^λ_x χ_{n+1,k} χ_{n,l}` appearing in the
  telescoping of the lattice approximations: they are scaled at the lattice point with radius
  `8 · 2^{-n}` and constant `C (λ⁵)⁻¹`, `C` absolute.
-/

public section

open Filter
open scoped ContDiff

namespace RegularityStructures

/-- A smooth function supported in `B(z, R)`, `0 < R ≤ 1`, is a scaled test function. -/
theorem exists_isScaledTest {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) {z : ParabolicSpace}
    {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hsupp : ∀ w, R < parabolicNorm (w - z) → g w = 0) :
    ∃ A, IsScaledTest g z R A := by
  have hh : ContDiff ℝ ∞ (fun v => g (z + parabolicDilate R v)) :=
    hg.comp (contDiff_const.add (parabolicDilateCLM R).contDiff)
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hcs : HasCompactSupport (fun v => g (z + parabolicDilate R v)) := by
    refine HasCompactSupport.intro hK fun v hv => ?_
    apply hsupp
    rw [add_sub_cancel_left, parabolicNorm_parabolicDilate hR.le]
    have : 1 < parabolicNorm v := by
      by_contra hn
      push Not at hn
      refine hv ⟨?_, fun i _ => ?_⟩
      · have h1 : Real.sqrt |v.1| ≤ 1 := by
          have : 0 ≤ ∑ i, |v.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
          unfold parabolicNorm at hn; linarith
        have := (Real.sqrt_le_iff.1 h1).2
        rw [one_pow] at this
        exact abs_le.1 this
      · have h1 : |v.2 i| ≤ ∑ j, |v.2 j| :=
          Finset.single_le_sum (f := fun j => |v.2 j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        have h2 : 0 ≤ Real.sqrt |v.1| := Real.sqrt_nonneg _
        unfold parabolicNorm at hn
        exact abs_le.1 (by linarith)
    nlinarith
  obtain ⟨C, hC0, hC⟩ := hcs.exists_bound_iteratedFDeriv hh 4
  exact ⟨C + 1, hg.of_le (by exact_mod_cast le_top), hR, hR1, by linarith, hsupp,
    fun k hk v => (hC k hk v).trans (by linarith)⟩

private theorem norm_parabolicDilateCLM_le_sixtyFour {c : ℝ} (h0 : 0 ≤ c) (h8 : c ≤ 8) :
    ‖parabolicDilateCLM c‖ ≤ 64 := by
  by_cases h1 : c ≤ 1
  · exact (norm_parabolicDilateCLM_le_one h0 h1).trans (by norm_num)
  · have := norm_parabolicDilateCLM_le (not_le.1 h1).le
    nlinarith

/-- Affine parabolic dilations by `0 ≤ c ≤ 8` multiply scaled derivative bounds of order `≤ 4`
by at most `64⁴`. -/
private theorem norm_iteratedFDeriv_comp_parabolicDilate_le_eight {h : ParabolicSpace → ℝ}
    (hh : ContDiff ℝ ∞ h) {A : ℝ} (hA : ∀ k ≤ 4, ∀ u, ‖iteratedFDeriv ℝ k h u‖ ≤ A) {c : ℝ}
    (h0 : 0 ≤ c) (h8 : c ≤ 8) (a : ParabolicSpace) {k : ℕ} (hk : k ≤ 4) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v => h (a + parabolicDilate c v)) v‖ ≤ A * 64 ^ 4 := by
  have hh' : ContDiff ℝ ∞ (fun u => h (a + u)) := hh.comp (contDiff_const.add contDiff_id)
  have e : (fun v => h (a + parabolicDilate c v)) =
      (fun u => h (a + u)) ∘ (parabolicDilateCLM c) := by
    funext v; simp
  rw [e]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) _
    (hh'.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn := norm_parabolicDilateCLM_le_sixtyFour h0 h8
  have hp : ∏ _i : Fin k, ‖parabolicDilateCLM c‖ ≤ 64 ^ 4 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (pow_le_pow_left₀ (norm_nonneg _) hn k).trans
      (pow_le_pow_right₀ (by norm_num) hk)
  have hd : ‖iteratedFDeriv ℝ k (fun u => h (a + u)) (parabolicDilateCLM c v)‖ ≤ A := by
    rw [iteratedFDeriv_comp_add_left]
    exact hA k hk _
  exact mul_le_mul hd hp (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    ((norm_nonneg _).trans hd)

/-- Scaled derivative bounds of a lattice cell in coordinates `v ↦ a + S^R v`, `2^m R ≤ 8`. -/
private theorem exists_bound_latticeCell_scaled :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (m : ℕ) (l : LatticeIndex) (a : ParabolicSpace) (R : ℝ), 0 < R →
      (2 : ℝ) ^ m * R ≤ 8 → ∀ k ≤ 4, ∀ v,
        ‖iteratedFDeriv ℝ k (fun v => latticeCell m l (a + parabolicDilate R v)) v‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_iteratedFDeriv_latticeBump4 4
  refine ⟨(C + 1) * 64 ^ 4, ?_, fun m l a R hR hmR k hk v => ?_⟩
  · have : (1 : ℝ) ≤ 64 ^ 4 := one_le_pow₀ (by norm_num)
    nlinarith
  · have e : (fun v => latticeCell m l (a + parabolicDilate R v)) =
        fun v => latticeBump4 ((parabolicDilate ((2 : ℝ) ^ m) a - latticeCoe l) +
          parabolicDilate ((2 : ℝ) ^ m * R) v) := by
      funext v
      rw [latticeCell_add_parabolicDilate, add_comm]
    rw [e]
    refine (norm_iteratedFDeriv_comp_parabolicDilate_le_eight contDiff_latticeBump4
      (A := C + 1) (fun k hk u => (hC k hk u).trans (by linarith))
      (by positivity) hmR _ hk v).trans le_rfl

private theorem contDiff_cell_scaled (m : ℕ) (l : LatticeIndex) (a : ParabolicSpace) (R : ℝ) :
    ContDiff ℝ ∞ (fun v => latticeCell m l (a + parabolicDilate R v)) :=
  (contDiff_latticeCell m l).comp (contDiff_const.add (parabolicDilateCLM R).contDiff)

private theorem contDiff_rescaled_scaled {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (lam : ℝ) (x z : ParabolicSpace) (R : ℝ) :
    ContDiff ℝ ∞ (fun v => rescaledTestFunction φ lam x (z + parabolicDilate R v)) :=
  (contDiff_rescaledTestFunction hφ lam x).comp
    (contDiff_const.add (parabolicDilateCLM R).contDiff)

private theorem two_pow_mul_eight_inv (n : ℕ) : (2 : ℝ) ^ n * (8 * ((2 : ℝ) ^ n)⁻¹) = 8 := by
  field_simp

private theorem radius_facts {lam : ℝ} {n : ℕ} (hl1 : lam ≤ 1) (hn : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam) :
    0 < 8 * ((2 : ℝ) ^ n)⁻¹ ∧ 8 * ((2 : ℝ) ^ n)⁻¹ ≤ 1 :=
  ⟨by positivity, hn.trans hl1⟩

/-- Pieces `φ^λ_x χ_{n,k}` are scaled test functions at `z_{n,k}` with radius `8 · 2^{-n}` and
constant `C (λ⁵)⁻¹`, with `C` absolute. -/
theorem exists_isScaledTest_rescaledTestFunction_mul_latticeCell :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 → ∀ {lam : ℝ},
      0 < lam → lam ≤ 1 → ∀ (x : ParabolicSpace) (n : ℕ), 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam →
      ∀ k : LatticeIndex,
      IsScaledTest (fun w => rescaledTestFunction φ lam x w * latticeCell n k w)
        (latticePoint n k) (8 * ((2 : ℝ) ^ n)⁻¹) (C * (lam ^ 5)⁻¹) := by
  obtain ⟨B, hB1, hB⟩ := exists_bound_latticeCell_scaled
  refine ⟨256 * B ^ 2, by positivity, fun {φ} hφ lam hl hl1 x n hn k => ?_⟩
  obtain ⟨hρ, hρ1⟩ := radius_facts hl1 hn
  have hA : 0 ≤ (lam ^ 5)⁻¹ := by positivity
  refine ⟨(contDiff_rescaledTestFunction hφ.1 lam x).mul (contDiff_latticeCell n k), hρ, hρ1,
    by positivity, fun w hw => ?_, fun k' hk' v => ?_⟩
  · by_contra h
    exact absurd (parabolicNorm_sub_latticePoint_le (right_ne_zero_of_mul h)) (not_le.2 hw)
  · have := norm_iteratedFDeriv_mul_le_of_le (r := 4)
      (contDiff_rescaled_scaled hφ.1 lam x (latticePoint n k) _)
      (contDiff_cell_scaled n k (latticePoint n k) _) (A := (lam ^ 5)⁻¹) (B := B)
      (fun j hj u => norm_iteratedFDeriv_rescaledTestFunction_scaled_le hφ hρ hn x _ hj u)
      (fun j hj u => hB n k _ _ hρ (two_pow_mul_eight_inv n).le j hj u) hk' v
    refine this.trans ?_
    have h2 : 2 ^ 4 * (lam ^ 5)⁻¹ * B ≤ 256 * B ^ 2 * (lam ^ 5)⁻¹ := by
      nlinarith [mul_nonneg hA (sub_nonneg.2 hB1), mul_nonneg hA (sq_nonneg (B - 1))]
    exact h2

/-- Pieces `φ^λ_x χ_{n+1,k} χ_{n,l}` are scaled test functions at `z_{n+1,k}` with radius
`8 · 2^{-(n+1)}` and constant `C (λ⁵)⁻¹`, with `C` absolute. -/
theorem exists_isScaledTest_rescaledTestFunction_mul_latticeCell_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 → ∀ {lam : ℝ},
      0 < lam → lam ≤ 1 → ∀ (x : ParabolicSpace) (n : ℕ), 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam →
      ∀ k l : LatticeIndex,
      IsScaledTest
        (fun w => rescaledTestFunction φ lam x w * latticeCell (n + 1) k w * latticeCell n l w)
        (latticePoint (n + 1) k) (8 * ((2 : ℝ) ^ (n + 1))⁻¹) (C * (lam ^ 5)⁻¹) := by
  obtain ⟨B, hB1, hB⟩ := exists_bound_latticeCell_scaled
  refine ⟨256 * B ^ 2, by positivity, fun {φ} hφ lam hl hl1 x n hn k l => ?_⟩
  have hn' : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ ≤ lam := by
    refine le_trans ?_ hn
    rw [pow_succ, mul_inv, ← mul_assoc, mul_comm 8, mul_assoc]
    have : 0 ≤ 8 * ((2 : ℝ) ^ n)⁻¹ := by positivity
    nlinarith
  obtain ⟨hρ, hρ1⟩ := radius_facts hl1 hn'
  have hA : 0 ≤ (lam ^ 5)⁻¹ := by positivity
  have h2n : (2 : ℝ) ^ n * (8 * ((2 : ℝ) ^ (n + 1))⁻¹) ≤ 8 := by
    rw [pow_succ]; field_simp; norm_num
  have hcont : ContDiff ℝ ∞ fun w => rescaledTestFunction φ lam x w * latticeCell (n + 1) k w :=
    (contDiff_rescaledTestFunction hφ.1 lam x).mul (contDiff_latticeCell _ k)
  refine ⟨hcont.mul (contDiff_latticeCell n l), hρ, hρ1, by positivity, fun w hw => ?_,
    fun k' hk' v => ?_⟩
  · by_contra h
    exact absurd (parabolicNorm_sub_latticePoint_le
      (right_ne_zero_of_mul (left_ne_zero_of_mul h))) (not_le.2 hw)
  · have h1 : ∀ j ≤ 4, ∀ u, ‖iteratedFDeriv ℝ j (fun u => rescaledTestFunction φ lam x
        (latticePoint (n + 1) k + parabolicDilate (8 * ((2 : ℝ) ^ (n + 1))⁻¹) u) *
        latticeCell (n + 1) k (latticePoint (n + 1) k +
          parabolicDilate (8 * ((2 : ℝ) ^ (n + 1))⁻¹) u)) u‖ ≤ 2 ^ 4 * (lam ^ 5)⁻¹ * B :=
      fun j hj u => norm_iteratedFDeriv_mul_le_of_le (r := 4)
        (contDiff_rescaled_scaled hφ.1 lam x (latticePoint (n + 1) k) _)
        (contDiff_cell_scaled (n + 1) k (latticePoint (n + 1) k) _) (A := (lam ^ 5)⁻¹) (B := B)
        (fun j hj u => norm_iteratedFDeriv_rescaledTestFunction_scaled_le hφ hρ hn' x _ hj u)
        (fun j hj u => hB (n + 1) k _ _ hρ (two_pow_mul_eight_inv (n + 1)).le j hj u) hj u
    have := norm_iteratedFDeriv_mul_le_of_le (r := 4)
      (hcont.comp (contDiff_const.add (parabolicDilateCLM _).contDiff))
      (contDiff_cell_scaled n l (latticePoint (n + 1) k) _) (A := 2 ^ 4 * (lam ^ 5)⁻¹ * B)
      (B := B) h1
      (fun j hj u => hB n l _ _ hρ h2n j hj u) hk' v
    refine this.trans ?_
    have h3 : 2 ^ 4 * (2 ^ 4 * (lam ^ 5)⁻¹ * B) * B ≤ 256 * B ^ 2 * (lam ^ 5)⁻¹ := by
      nlinarith
    exact h3

theorem eight_mul_two_pow_inv_le_one {n : ℕ} (hn : 3 ≤ n) : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
  have : (2 : ℝ) ^ 3 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  linarith

/-- A smooth function vanishing outside the support of the cell `χ_{m,l}` (`m ≥ 3`) is a scaled
test function at `z_{m,l}` with radius `8 · 2^{-m}`, for some constant. -/
theorem exists_isScaledTest_of_latticeCell {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    {m : ℕ} (hm : 3 ≤ m) {l : LatticeIndex} (hsupp : ∀ w, g w ≠ 0 → latticeCell m l w ≠ 0) :
    ∃ A, IsScaledTest g (latticePoint m l) (8 * ((2 : ℝ) ^ m)⁻¹) A :=
  exists_isScaledTest hg (by positivity) (eight_mul_two_pow_inv_le_one hm) fun w hw => by
    by_contra h
    exact absurd (parabolicNorm_sub_latticePoint_le (hsupp w h)) (not_le.2 hw)

/-- Partition of unity, localised: `u = ∑_{l ∈ s} u χ_{n,l}(w)` when `u` vanishes where `ψ w = 0`
and `s` contains every `l` with `ψ w χ_{n,l}(w) ≠ 0`. -/
theorem eq_sum_latticeCell_mul {ψ : ParabolicSpace → ℝ} {n : ℕ} {s : Finset LatticeIndex}
    (hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ s) (w : ParabolicSpace) (u : ℝ)
    (hu : ψ w = 0 → u = 0) : u = ∑ l ∈ s, u * latticeCell n l w := by
  by_cases hψ : ψ w = 0
  · simp [hu hψ]
  · rw [← Finset.mul_sum, sum_latticeCell_eq_one (fun l hl => hs l w (mul_ne_zero hψ hl)), mul_one]

end RegularityStructures

end

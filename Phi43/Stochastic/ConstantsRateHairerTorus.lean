/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateHairerR4
public import Phi43.Stochastic.ConstantsRateLift
public import Phi43.Stochastic.ConstantsComparisonDefinitions

/-!
# Increments of the periodised Hairer kernel

The periodised kernel `hairerKernelTorus N` is, at a torus point with centred lift `y`, the
lattice sum `∑ₖ K(t, y + k)`.  Only a bounded box of lattice points contributes, and each term is
estimated by `constantsRate_hairerKernel_increment`.
-/

@[expose] public noncomputable section

open Set

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem hairerKernel_eq_zero_of_one_lt (N : ℕ) {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : hairerKernel N z = 0 := by
  unfold hairerKernel
  have hzero : ∀ n, annShellC N n z = 0 := by
    intro n
    apply annShellC_eq_zero
    exact lt_of_le_of_lt (pow_le_one₀ (by positivity) (by norm_num)) hz
  rw [tsum_eq_sum (s := (∅ : Finset ℕ)) (fun n _ => hzero n)]
  simp

private theorem abs_coord_le_parabolicNorm {z : ParabolicSpace} (i : Fin 3) :
    |z.2 i| ≤ parabolicNorm z := by
  unfold parabolicNorm
  have h1 : |z.2 i| ≤ ∑ j, |z.2 j| :=
    Finset.single_le_sum (f := fun j => |z.2 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith [Real.sqrt_nonneg |z.1|]

theorem constantsRate_hairerKernelTorus_increment (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z h : SpaceTime, 0 < torusParabolicSize z →
      16 * torusParabolicSize h ≤ torusParabolicSize z →
      |hairerKernelTorus N (z - h) - hairerKernelTorus N z| ≤
        B * torusParabolicSize h * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨B₄, hB₄0, hB₄⟩ := constantsRate_hairerKernel_increment N
  classical
  let S : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2)
  refine ⟨2 * (S.card * B₄), by positivity, ?_⟩
  intro z h hz hzh
  set r : ℝ := torusParabolicSize h with hr
  set s0 : ℝ := torusParabolicSize z with hs0
  let y : Fin 3 → ℝ := torusCenteredRep z.2
  let g : Fin 3 → ℝ := torusCenteredRep h.2
  let η : ParabolicSpace := (h.1, g)
  let w : (Fin 3 → ℤ) → ParabolicSpace := fun k => (z.1, y + fun i => (k i : ℝ))
  have hp : parabolicNorm η ≤ 2 * r := constantsRate_parabolicNorm_centered_le h
  have hr0 : 0 ≤ r := torusParabolicSize_nonneg h
  have hwnorm : ∀ k, s0 ≤ parabolicNorm (w k) := fun k => constantsRate_size_le_centered_lift z k
  -- lifts
  have hz1 : hairerKernelTorus N z = ∑' k : Fin 3 → ℤ, hairerKernel N (w k) := by
    unfold hairerKernelTorus
    exact constantsRate_tsum_lift (fun v => hairerKernel N (z.1, v)) z.2 y
      (torusProj_torusCenteredRep z.2)
  have hz2 : hairerKernelTorus N (z - h) = ∑' k : Fin 3 → ℤ, hairerKernel N (w k - η) := by
    unfold hairerKernelTorus
    have hproj : torusProj (y - g) = (z - h).2 := by
      rw [RegularityStructures.PDE.torusProj_sub, torusProj_torusCenteredRep,
        torusProj_torusCenteredRep]
      rfl
    have h1 := constantsRate_tsum_lift (fun v => hairerKernel N ((z - h).1, v)) (z - h).2
      (y - g) hproj
    rw [h1]
    apply tsum_congr
    intro k
    congr 1
    apply Prod.ext
    · rfl
    · funext i
      simp [w, η]
      ring
  -- finite support
  have hsupp1 : ∀ k ∉ S, hairerKernel N (w k) = 0 := by
    intro k hk
    by_contra hne
    apply hk
    have hle : parabolicNorm (w k) ≤ 1 := by
      by_contra hlt
      exact hne (hairerKernel_eq_zero_of_one_lt N (lt_of_not_ge hlt))
    simp only [S, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := abs_coord_le_parabolicNorm (z := w k) i
    have h2 := abs_le.mp (h1.trans hle)
    have h3 := torusCenteredRep_mem_Icc z.2 i
    have h4 : (w k).2 i = y i + (k i : ℝ) := rfl
    rw [h4] at h2
    have h5 : (-2 : ℝ) ≤ (k i : ℝ) ∧ (k i : ℝ) ≤ 2 := by
      constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
    exact ⟨by exact_mod_cast h5.1, by exact_mod_cast h5.2⟩
  have hsupp2 : ∀ k ∉ S, hairerKernel N (w k - η) = 0 := by
    intro k hk
    by_contra hne
    apply hk
    have hle : parabolicNorm (w k - η) ≤ 1 := by
      by_contra hlt
      exact hne (hairerKernel_eq_zero_of_one_lt N (lt_of_not_ge hlt))
    simp only [S, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := abs_coord_le_parabolicNorm (z := w k - η) i
    have h2 := abs_le.mp (h1.trans hle)
    have h3 := torusCenteredRep_mem_Icc z.2 i
    have h3' := torusCenteredRep_mem_Icc h.2 i
    have h4 : (w k - η).2 i = y i + (k i : ℝ) - g i := rfl
    rw [h4] at h2
    have h5 : (-2 : ℝ) ≤ (k i : ℝ) ∧ (k i : ℝ) ≤ 2 := by
      constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h3'.1, h3'.2]
    exact ⟨by exact_mod_cast h5.1, by exact_mod_cast h5.2⟩
  rw [hz1, hz2, tsum_eq_sum hsupp1, tsum_eq_sum hsupp2, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ S, |hairerKernel N (w k - η) - hairerKernel N (w k)| ≤
      B₄ * (2 * r) * s0 ^ (-(4 : ℝ)) := by
    intro k _
    have hpos : 0 < parabolicNorm (w k) := lt_of_lt_of_le hz (hwnorm k)
    have h8 : 8 * parabolicNorm η ≤ parabolicNorm (w k) := by
      have := hwnorm k
      linarith
    have h1 := hB₄ (w k) η hpos h8
    have h2 : parabolicNorm (w k) ^ (-(4 : ℝ)) ≤ s0 ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hz (hwnorm k) (by norm_num)
    calc
      _ ≤ B₄ * parabolicNorm η * parabolicNorm (w k) ^ (-(4 : ℝ)) := h1
      _ ≤ B₄ * (2 * r) * s0 ^ (-(4 : ℝ)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp hB₄0
        · exact h2
        · exact Real.rpow_nonneg hpos.le _
        · positivity
  calc
    |∑ k ∈ S, (hairerKernel N (w k - η) - hairerKernel N (w k))| ≤
        ∑ k ∈ S, |hairerKernel N (w k - η) - hairerKernel N (w k)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le S (fun k => hairerKernel N (w k - η) - hairerKernel N (w k))
    _ ≤ ∑ k ∈ S, B₄ * (2 * r) * s0 ^ (-(4 : ℝ)) := Finset.sum_le_sum hterm
    _ = 2 * (S.card * B₄) * r * s0 ^ (-(4 : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end RegularityStructures.Phi43

end

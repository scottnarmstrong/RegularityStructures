/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionCompactGrowth
public import Phi43.Structure.RenormalisedExtensionLocalBounds
import RegularityStructures.Analysis.Kernel.GeneratorLip

/-!
# Local cancellation with whole-space polynomial tails

The positive sector in Hairer [Hai14, Proposition 8.27, Theorem 8.44] has its prescribed
power near its base point. The second power below controls the far field
in the polynomially weighted framework [Hos25, Definition 2.1].
-/

public noncomputable section

namespace RegularityStructures.Phi43

private theorem small_norm {v : ParabolicSpace} (hv : parabolicNorm v ≤ 1) :
    ‖v‖ ≤ parabolicNorm v := by
  have hs : Real.sqrt |v.1| ≤ parabolicNorm v := by
    unfold parabolicNorm
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have ht : |v.1| ≤ 1 := by
    have hsq := Real.sq_sqrt (abs_nonneg v.1)
    have hsn := Real.sqrt_nonneg |v.1|
    nlinarith
  exact RegularityStructures.norm_le_parabolicNorm ht

private theorem positive_degree_le_one (κ : Kappa) (τ : Symbol)
    (hτ : homogeneity κ τ < gamma κ) : homogeneity κ τ ≤ 1 := by
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  cases τ <;> simp only [homogeneity, gamma] at hτ ⊢ <;> linarith

/-- On compact base-point sets, local homogeneity cancellation and a higher
polynomial power together dominate the actual canonical function everywhere. -/
theorem renormalisedExtensionPi_positive_two_power_bound (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (hf : PolyBounded noise.zeta) (C : RenormalisationConstants) (τ : Symbol)
    (hτ0 : 0 < homogeneity κ τ) (hτγ : homogeneity κ τ < gamma κ)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∃ n : ℕ, homogeneity κ τ ≤ n ∧
      ∀ x ∈ S, ∀ y,
        |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y| ≤
          A * parabolicNorm (y - x) ^ homogeneity κ τ +
            B * parabolicNorm (y - x) ^ (n : ℝ) := by
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
  let R' := max R 0 + 2
  have hRx (x : ParabolicSpace) (hx : x ∈ S) : ‖x‖ ≤ max R 0 :=
    (hR x hx).trans (le_max_left _ _)
  obtain ⟨A, hA0, hA⟩ := renormalisedExtensionPi_positive_local_bound N κ noise C
    (isCompact_closedBall (0 : ParabolicSpace) R')
  obtain ⟨D, hD0, p, hD⟩ := renormalisedExtensionPi_compact_growth N κ noise hf C τ hS
  obtain ⟨L, hL⟩ := hS.exists_bound_of_continuousOn continuous_parabolicNorm.continuousOn
  let E := 1 + max L 0
  have hE : 0 ≤ E := by dsimp [E]; linarith [le_max_right L 0]
  let B := D * E ^ p * 2 ^ p
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hD0 (pow_nonneg hE _)) (by positivity)
  refine ⟨A, B, hA0, hB0, p + 1,
    (positive_degree_le_one κ τ hτγ).trans (by exact_mod_cast Nat.le_add_left 1 p), ?_⟩
  intro x hx y
  have hd0 := parabolicNorm_nonneg (y - x)
  by_cases hd : parabolicNorm (y - x) ≤ 1
  · have hx' : x ∈ Metric.closedBall (0 : ParabolicSpace) R' := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hRx x hx).trans (by dsimp [R']; linarith)
    have hy' : y ∈ Metric.closedBall (0 : ParabolicSpace) R' := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hn := norm_add_le (y - x) x
      rw [sub_add_cancel] at hn
      have hs := small_norm hd
      have hr := hRx x hx
      dsimp [R']
      linarith
    exact (hA τ hτ0 hτγ x hx' y hy' hd).trans
      (le_add_of_nonneg_right (mul_nonneg hB0 (Real.rpow_nonneg hd0 _)))
  · have hd1 : 1 ≤ parabolicNorm (y - x) := (lt_of_not_ge hd).le
    have hxabs : |parabolicNorm x| ≤ L := by
      simpa only [Real.norm_eq_abs] using hL x hx
    have hxL : parabolicNorm x ≤ max L 0 :=
      (le_abs_self _).trans (hxabs.trans (le_max_left _ _))
    have hbase : 1 + parabolicNorm y ≤ E * (1 + parabolicNorm (y - x)) := by
      have hn := parabolicNorm_add_le (y - x) x
      rw [sub_add_cancel] at hn
      have hm := mul_nonneg (le_max_right L 0) hd0
      dsimp [E]
      nlinarith
    have hp : (1 + parabolicNorm y) ^ p ≤
        E ^ p * (2 ^ p * parabolicNorm (y - x) ^ p) := by
      calc
        _ ≤ (E * (1 + parabolicNorm (y - x))) ^ p :=
          pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg y]) hbase p
        _ = E ^ p * (1 + parabolicNorm (y - x)) ^ p := mul_pow _ _ _
        _ ≤ E ^ p * (2 * parabolicNorm (y - x)) ^ p :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) p) (pow_nonneg hE _)
        _ = _ := by rw [mul_pow]
    have hpow : parabolicNorm (y - x) ^ p ≤ parabolicNorm (y - x) ^ (p + 1) :=
      pow_le_pow_right₀ hd1 (Nat.le_succ p)
    have hfar : |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y| ≤
        B * parabolicNorm (y - x) ^ (p + 1) := by
      calc
        _ ≤ D * (1 + parabolicNorm y) ^ p := hD x hx y
        _ ≤ D * (E ^ p * (2 ^ p * parabolicNorm (y - x) ^ p)) :=
          mul_le_mul_of_nonneg_left hp hD0
        _ = B * parabolicNorm (y - x) ^ p := by dsimp [B]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hB0
    rw [Real.rpow_natCast]
    exact hfar.trans (le_add_of_nonneg_left
      (mul_nonneg hA0 (Real.rpow_nonneg hd0 _)))

end RegularityStructures.Phi43

end


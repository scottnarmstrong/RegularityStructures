/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalCharacterGrowth
public import Phi43.Structure.CanonicalModel

/-!
# Common polynomial envelopes for finite tree families

Finite-dimensional ingredients for Hairer [Hai14, Proposition 8.27] in
the weighted framework [Hos25, Definition 2.1].
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- Finitely many proved polynomial bounds have a common nonnegative
constant and exponent. No model estimates are postulated. -/
theorem canonicalPolyBounded_finite_envelope {ι : Type*} [Fintype ι]
    (f : ι → ParabolicSpace → ℝ) (hf : ∀ i, PolyBounded (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i z, |f i z| ≤ C * (1 + parabolicNorm z) ^ p := by
  classical
  have hb (i : ι) := (hf i).2
  choose B p hp using hb
  have hB (i : ι) : 0 ≤ B i := nonneg_of_bound (hp i)
  refine ⟨∑ i, B i, Finset.sum_nonneg (fun i _ => hB i), ∑ i, p i, fun i z => ?_⟩
  have hn : p i ≤ ∑ j, p j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hC : B i ≤ ∑ j, B j :=
    Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
  have hpow := pow_le_pow_right₀ (show 1 ≤ 1 + parabolicNorm z by
    linarith [parabolicNorm_nonneg z]) hn
  exact (hp i z).trans ((mul_le_mul_of_nonneg_left hpow (hB i)).trans
    (mul_le_mul_of_nonneg_right hC (pow_nonneg (by linarith [parabolicNorm_nonneg z]) _)))

/-- The actual canonical function is the finite global-tree expansion. -/
theorem canonicalPi_eq_global_sum (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (x y : ParabolicSpace) (τ : Symbol) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis τ) y =
      ∑ σ : Symbol, structureGroupMap
        ((hairerCanonicalData (κ := κ) N noise).canonicalCharacter x) (basis τ) σ *
          (hairerCanonicalData (κ := κ) N noise).globalPiBasis σ y := by
  rw [CanonicalData.canonicalPi_character_bridge, LinearMap.comp_apply,
    CanonicalData.globalPi, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

end RegularityStructures.Phi43

end

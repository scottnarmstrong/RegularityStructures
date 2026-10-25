/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.ZetaBound
public import Phi43.Potential.Slice
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import Phi43.ClassicalSolution.ExistenceCutoff
public import Phi43.Inhomogeneity.DuhamelField
public import RegularityStructures.Abstract.Polynomial.Model.Growth

/-!
# Bounds for a smooth periodic noise

* `exists_bound_strip`: a continuous spatially periodic function is bounded on every time strip;
* `polyBounded_of_growth`, `potForcing_of_growth`: the explicit growth `HasPhi43NoiseGrowth f` gives
  `PolyBounded noise.zeta` and `PotForcing f` (polynomial growth in time, uniformly on `T³`).
-/

public section

open Set

namespace RegularityStructures.Phi43.Potential

open RegularityStructures RegularityStructures.Potential RegularityStructures.Inhomogeneity

theorem torusProj_intCast (n : Fin 3 → ℤ) : torusProj (fun i => (n i : ℝ)) = 0 := by
  funext i
  simp only [torusProj, Pi.zero_apply]
  exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2 ⟨n i, by simp⟩

theorem exists_bound_strip {ζ : ParabolicSpace → ℝ} (hζ : PerSmooth ζ) (a b : ℝ) :
    ∃ B : ℝ, ∀ y : ParabolicSpace, a ≤ y.1 → y.1 ≤ b → |ζ y| ≤ B := by
  have hK : IsCompact (Icc a b ×ˢ Set.pi univ (fun _ : Fin 3 => Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hζ.smooth.continuous.continuousOn
  refine ⟨B, fun y h1 h2 => ?_⟩
  set n : Fin 3 → ℤ := fun i => ⌊y.2 i⌋ with hn
  have hmem : ((y.1, y.2 - fun i => (n i : ℝ)) : ParabolicSpace) ∈
      Icc a b ×ˢ Set.pi univ (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
    refine ⟨⟨h1, h2⟩, fun i _ => ⟨?_, ?_⟩⟩
    · show 0 ≤ y.2 i - (⌊y.2 i⌋ : ℝ)
      linarith [Int.floor_le (y.2 i)]
    · show y.2 i - (⌊y.2 i⌋ : ℝ) ≤ 1
      linarith [Int.lt_floor_add_one (y.2 i)]
  have hper := hζ.periodic ((y.1, y.2 - fun i => (n i : ℝ)) : ParabolicSpace)
    (fun i => (n i : ℝ)) (torusProj_intCast n)
  have e : ((y.1, y.2 - fun i => (n i : ℝ)) : ParabolicSpace).1 = y.1 := rfl
  have e2 : (y.1, (y.2 - fun i => (n i : ℝ)) + fun i => (n i : ℝ)) = y := by
    ext <;> simp
  have := hB _ hmem
  rw [Real.norm_eq_abs] at this
  have h3 : ζ y = ζ (y.1, y.2 - fun i => (n i : ℝ)) := by
    rw [← hper]; congr 1; ext <;> simp
  rw [h3]
  exact this

theorem abs_le_of_growth {f : SpaceTime → ℝ} (hg : Statements.HasPhi43NoiseGrowth f) :
    ∃ (Cg : ℝ) (q : ℕ), ∀ z : ParabolicSpace, |f (z.1, torusProj z.2)| ≤
      Cg * (1 + parabolicNorm z) ^ q := by
  obtain ⟨Cg, q, h⟩ := hg
  refine ⟨Cg, q, fun z => ?_⟩
  have := h 0 (by norm_num) z
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

theorem polyBounded_zeta {f : SpaceTime → ℝ} {noise : CanonicalNoise}
    (hfz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    (hg : Statements.HasPhi43NoiseGrowth f) : PolyBounded noise.zeta := by
  obtain ⟨Cg, q, h⟩ := abs_le_of_growth hg
  exact ⟨noise.smooth.continuous.measurable, Cg, q, fun u => by rw [hfz]; exact h u⟩

theorem isSmoothOnSpaceTime_of_noise {f : SpaceTime → ℝ} {noise : CanonicalNoise}
    (hfz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2)) :
    IsSmoothOnSpaceTime f := by
  have : (fun p : ℝ × (Fin 3 → ℝ) => f (p.1, torusProj p.2)) = noise.zeta := by
    funext z; exact (hfz z).symm
  unfold IsSmoothOnSpaceTime
  rw [this]
  exact noise.smooth

theorem potForcing_of_growth {f : SpaceTime → ℝ} {noise : CanonicalNoise}
    (hfz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    (hg : Statements.HasPhi43NoiseGrowth f) : PotForcing f := by
  refine ⟨continuous_of_isSmoothOnSpaceTime (isSmoothOnSpaceTime_of_noise hfz), ?_⟩
  obtain ⟨Cg, q, h⟩ := abs_le_of_growth hg
  refine ⟨|Cg| * 5 ^ q, q, by positivity, fun r y => ?_⟩
  have h1 := h (r, torusRep y)
  simp only [PDE.torusProj_torusRep] at h1
  have hrep : ∀ i, 0 ≤ torusRep y i ∧ torusRep y i < 1 := fun i => by
    have := (AddCircle.equivIco (1 : ℝ) 0 (y i)).property
    simpa [torusRep] using this
  have hsq : Real.sqrt |r| ≤ 1 + |r| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg r]
  have hnorm : 1 + parabolicNorm ((r, torusRep y) : ParabolicSpace) ≤ 5 * (1 + |r|) := by
    unfold parabolicNorm
    have : ∑ i, |torusRep y i| ≤ 3 := by
      calc ∑ i, |torusRep y i| ≤ ∑ _i : Fin 3, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_of_nonneg (hrep i).1]; exact (hrep i).2.le
        _ = 3 := by simp
    simp only
    nlinarith [abs_nonneg r]
  calc |f (r, y)| ≤ Cg * (1 + parabolicNorm ((r, torusRep y) : ParabolicSpace)) ^ q := h1
    _ ≤ |Cg| * (1 + parabolicNorm ((r, torusRep y) : ParabolicSpace)) ^ q :=
        mul_le_mul_of_nonneg_right (le_abs_self _)
          (pow_nonneg (by linarith [parabolicNorm_nonneg ((r, torusRep y) : ParabolicSpace)]) _)
    _ ≤ |Cg| * (5 * (1 + |r|)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (by linarith [parabolicNorm_nonneg ((r, torusRep y) : ParabolicSpace)]) hnorm q)
          (abs_nonneg _)
    _ = |Cg| * 5 ^ q * (1 + |r|) ^ q := by rw [mul_pow]; ring

end RegularityStructures.Phi43.Potential

end

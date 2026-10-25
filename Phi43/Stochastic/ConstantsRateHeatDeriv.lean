/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsParabolicDerivative
public import RegularityStructures.Torus.KernelBoundsLargeTime
public import RegularityStructures.Torus.HeatKernelIntegral
public import RegularityStructures.Torus.KernelBoundsGeometry

/-!
# Derivatives of the lifted torus heat kernel at arbitrary lifts

The existing derivative bounds for `heatKernelLift` are stated at centred points.  By periodicity
they hold at every point of `ℝ³`, with the centred norm `ν y = torusSpatialNorm (torusProj y)`
replacing `|y|`.  For `0 < τ ≤ 1` the bounds are the sharp parabolic ones; for `τ ≥ 1/2` they are
bounded by a constant, by termwise domination of the Gaussian lattice sum by the heat kernel at
time `2τ`.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

/-- The centred distance of a point of `ℝ³` to the lattice `ℤ³`. -/
def heatLiftNu (y : Fin 3 → ℝ) : ℝ := torusSpatialNorm (torusProj y)

theorem heatLiftNu_nonneg (y : Fin 3 → ℝ) : 0 ≤ heatLiftNu y := torusSpatialNorm_nonneg _

theorem exists_int_lift_centered (y : Fin 3 → ℝ) :
    ∃ n : Fin 3 → ℤ, y = torusCenteredRep (torusProj y) + fun i => (n i : ℝ) := by
  have hcoord : ∀ i, ∃ m : ℤ, y i = torusCenteredRep (torusProj y) i + (m : ℝ) := by
    intro i
    have hi : ((torusCenteredRep (torusProj y) i : ℝ) : UnitAddCircle) = (y i : UnitAddCircle) := by
      have := congrFun (torusProj_torusCenteredRep (torusProj y)) i
      exact this
    have himem : torusCenteredRep (torusProj y) i - y i ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem.mp hi)
    rcases AddSubgroup.mem_zmultiples_iff.mp himem with ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    have hm' : (m : ℝ) = torusCenteredRep (torusProj y) i - y i := by simpa using hm
    rw [Int.cast_neg]
    linarith
  choose m hm using hcoord
  exact ⟨m, funext fun i => hm i⟩

theorem heatKernelLift_eq_centered (τ : ℝ) (y : Fin 3 → ℝ) :
    heatKernelLift τ y = heatKernelLift τ (torusCenteredRep (torusProj y)) := by
  obtain ⟨n, hn⟩ := exists_int_lift_centered y
  conv_lhs => rw [hn]
  exact heatKernelLift_add_integer n _

theorem centered_mem_Icc (y : Fin 3 → ℝ) (j : Fin 3) :
    torusCenteredRep (torusProj y) j ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
  torusCenteredRep_mem_Icc _ j

theorem sqrt_sqNorm3_centered (y : Fin 3 → ℝ) :
    √(sqNorm3 (torusCenteredRep (torusProj y))) = heatLiftNu y := rfl

/-- A periodic reduction of the line functions to centred points. -/
theorem heatKernelLift_update_eq (τ : ℝ) (y : Fin 3 → ℝ) (i : Fin 3) (n : Fin 3 → ℤ)
    (hn : y = torusCenteredRep (torusProj y) + fun j => (n j : ℝ)) (s : ℝ) :
    heatKernelLift τ (Function.update y i s) =
      heatKernelLift τ (Function.update (torusCenteredRep (torusProj y)) i (s - n i)) := by
  have h : Function.update y i s =
      Function.update (torusCenteredRep (torusProj y)) i (s - n i) + fun j => (n j : ℝ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp only [Function.update_of_ne hj, Pi.add_apply]
      exact congrFun hn j
  rw [h, heatKernelLift_add_integer]

theorem heatLift_space_hasDerivAt_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ (y : Fin 3 → ℝ) (i : Fin 3),
      ∃ d : ℝ, HasDerivAt (fun s => heatKernelLift τ (Function.update y i s)) d (y i) ∧
        |d| ≤ C * (√τ + heatLiftNu y) ^ (-(4 : ℝ)) := by
  obtain ⟨C₀, hC₀, hpar⟩ := firstSpatialDerivativeCoefficient_parabolic_bound
  refine ⟨C₀ * gaussianProductMajorantSum, mul_nonneg hC₀ nonneg_gaussianProductMajorantSum, ?_⟩
  intro τ hτ hτ1 y i
  obtain ⟨n, hn⟩ := exists_int_lift_centered y
  set c : Fin 3 → ℝ := torusCenteredRep (torusProj y) with hc
  have hcI : ∀ j, c j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j
    have := torusCenteredRep_mem_Icc (torusProj y) j
    simpa [neg_div] using this
  have hcI' : ∀ j, c j ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := centered_mem_Icc y
  have hder := hasDerivAt_heatKernelLift_spaceLine hτ i c hcI
  have hyi : y i - (n i : ℝ) = c i := by
    have := congrFun hn i
    simp only [Pi.add_apply] at this
    linarith
  refine ⟨gaussKernelSpaceLine_first_deriv_tsum τ i c, ?_, ?_⟩
  · have hfun : (fun s => heatKernelLift τ (Function.update y i s)) =
        fun s => heatKernelLift τ (Function.update c i (s - n i)) := by
      funext s
      exact heatKernelLift_update_eq τ y i n hn s
    rw [hfun]
    have hd2 : HasDerivAt (fun s => heatKernelLift τ (Function.update c i s))
        (gaussKernelSpaceLine_first_deriv_tsum τ i c) (y i - n i) := by
      rw [hyi]
      exact hder
    exact hd2.comp_sub_const (y i) (n i)
  · have hb := heatKernelLift_first_spatial_deriv_tsum_bound hτ hτ1 i c hcI
    have hs0 : 0 ≤ sqNorm3 c := Finset.sum_nonneg fun j _ => sq_nonneg (c j)
    have hq : 0 < √τ + heatLiftNu y := by
      have := heatLiftNu_nonneg y
      have : 0 < √τ := Real.sqrt_pos.mpr hτ
      linarith
    have hpow := hpar τ hτ (sqNorm3 c) hs0
    have hroot : √(sqNorm3 c) = heatLiftNu y := sqrt_sqNorm3_centered y
    rw [hroot] at hpow
    have hX := singular_bound_of_power_mul_le (m := 4) hq
      (A := firstSpatialDerivativeCoefficient τ * exp (-firstSpatialDerivativeScale τ * sqNorm3 c))
      (C := C₀) (by simpa using hpow)
    calc
      |gaussKernelSpaceLine_first_deriv_tsum τ i c| ≤
          firstSpatialDerivativeCoefficient τ *
            exp (-firstSpatialDerivativeScale τ * sqNorm3 c) * gaussianProductMajorantSum := hb
      _ ≤ C₀ * (√τ + heatLiftNu y) ^ (-((4 : ℕ) : ℝ)) * gaussianProductMajorantSum :=
        mul_le_mul_of_nonneg_right hX nonneg_gaussianProductMajorantSum
      _ = C₀ * gaussianProductMajorantSum * (√τ + heatLiftNu y) ^ (-(4 : ℝ)) := by
        push_cast
        ring

theorem heatLift_time_hasDerivAt_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ y : Fin 3 → ℝ,
      ∃ d : ℝ, HasDerivAt (fun σ => heatKernelLift σ y) d τ ∧
        |d| ≤ C * (√τ + heatLiftNu y) ^ (-(5 : ℝ)) := by
  obtain ⟨C₀, hC₀, hpar⟩ := secondSpatialDerivativeCoefficient_parabolic_bound
  refine ⟨3 * C₀ * gaussianProductMajorantSum,
    by have := nonneg_gaussianProductMajorantSum; positivity, ?_⟩
  intro τ hτ hτ1 y
  set c : Fin 3 → ℝ := torusCenteredRep (torusProj y) with hc
  have hcI : ∀ j, c j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j
    have := torusCenteredRep_mem_Icc (torusProj y) j
    simpa [neg_div] using this
  have hder := hasDerivAt_heatKernelLift_time hτ c hcI
  refine ⟨gaussKernelTimeDerivativeTsum τ c, ?_, ?_⟩
  · have hfun : (fun σ => heatKernelLift σ y) = fun σ => heatKernelLift σ c := by
      funext σ
      exact heatKernelLift_eq_centered σ y
    rw [hfun]
    exact hder
  · have hb := heatKernelLift_time_deriv_tsum_bound hτ hτ1 c hcI
    have hs0 : 0 ≤ sqNorm3 c := Finset.sum_nonneg fun j _ => sq_nonneg (c j)
    have hq : 0 < √τ + heatLiftNu y := by
      have := heatLiftNu_nonneg y
      have : 0 < √τ := Real.sqrt_pos.mpr hτ
      linarith
    have hpow := hpar τ hτ (sqNorm3 c) hs0
    have hroot : √(sqNorm3 c) = heatLiftNu y := sqrt_sqNorm3_centered y
    rw [hroot] at hpow
    have hX := singular_bound_of_power_mul_le (m := 5) hq
      (A := secondSpatialDerivativeCoefficient τ *
        exp (-(((4 * τ)⁻¹) / 2) * sqNorm3 c))
      (C := C₀) (by simpa using hpow)
    have hb' : |gaussKernelTimeDerivativeTsum τ c| ≤
        3 * (secondSpatialDerivativeCoefficient τ *
          exp (-(((4 * τ)⁻¹) / 2) * sqNorm3 c)) * gaussianProductMajorantSum := by
      simpa [secondSpatialDerivativeCoefficient, mul_assoc] using hb
    calc
      |gaussKernelTimeDerivativeTsum τ c| ≤
          3 * (secondSpatialDerivativeCoefficient τ *
            exp (-(((4 * τ)⁻¹) / 2) * sqNorm3 c)) * gaussianProductMajorantSum := hb'
      _ ≤ 3 * (C₀ * (√τ + heatLiftNu y) ^ (-((5 : ℕ) : ℝ))) * gaussianProductMajorantSum := by
        have hG := nonneg_gaussianProductMajorantSum
        gcongr
      _ = 3 * C₀ * gaussianProductMajorantSum * (√τ + heatLiftNu y) ^ (-(5 : ℝ)) := by
        push_cast
        ring

end RegularityStructures

end

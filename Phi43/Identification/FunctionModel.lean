/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.BaseFunctions
public import RegularityStructures.Abstract.Singular.Ident.FunctionModel
public import Phi43.Structure.CanonicalGrowthPremise
public import RegularityStructures.Abstract.Polynomial.Model.Unit
public import RegularityStructures.Abstract.Polynomial.Model.Reg

/-!
# The renormalised canonical model is a smooth function model below `κ`

For `Z` with `Statements.IsRenormalisedCanonicalModel N κ noise C Z` and the noise growth premise,
`Z.IsSmoothFunctionModelBelow (phi43BaseFunctions N κ noise C) κ`
(`isSmoothFunctionModelBelow_phi43BaseFunctions`).  The unit is realised by the constant `1`
(clause 1, polynomial compatibility); `F₋` by `Π^M_x τ` (clause 2); the growth along the diagonal
comes from `Π^M_y τ (y) = (Π_y M τ)(y)` (`renormalisedPi_at_base`) and the global envelope of
the canonical `Π`.

Source: [Hai14, Remark 3.15, (8.34)].
-/

public section

namespace RegularityStructures.Phi43

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants)

private theorem canonicalPi_diag_bound {Cg : ℝ} {q : ℕ}
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q) (v : T) :
    ∃ (B : ℝ) (n : ℕ), ∀ y : ParabolicSpace,
      |(hairerCanonicalData (κ := κ) N noise).canonicalPi y v y| ≤ B * (1 + parabolicNorm y) ^ n := by
  obtain ⟨B, hB0, a, b, hB⟩ := canonicalPi_global_polynomial_envelope N κ noise Cg q hg
  refine ⟨(∑ σ : Symbol, |phi43CoordinateEquiv v σ|) * B, a + b, fun y => ?_⟩
  have hv : v = phi43CoordinateEquiv.symm (phi43CoordinateEquiv v) := by simp
  conv_lhs => rw [hv, canonicalPi_coord_sum]
  have hP : 0 ≤ 1 + parabolicNorm y := by linarith [parabolicNorm_nonneg y]
  calc _ ≤ ∑ σ : Symbol, |phi43CoordinateEquiv v σ * (hairerCanonicalData (κ := κ) N noise).canonicalPi
          y (basis σ) y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Symbol, |phi43CoordinateEquiv v σ| * (B * (1 + parabolicNorm y) ^ (a + b)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := hB σ y y
        rwa [mul_assoc, ← pow_add] at this
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Polynomial growth along the diagonal of every base function. -/
theorem phi43BaseFunctions_diag_polyBounded {Cg : ℝ} {q : ℕ}
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q) (τ : Symbol) :
    PolyBounded (fun y => phi43BaseFunctions N κ noise C y τ y) := by
  have hm : Measurable (fun y => phi43BaseFunctions N κ noise C y τ y) :=
    ((phi43BaseFunctions_continuous N κ noise C τ).comp
      (continuous_id.prodMk continuous_id)).measurable
  refine ⟨hm, ?_⟩
  by_cases h1 : τ ∈ fMinus
  · obtain ⟨B, n, hB⟩ := canonicalPi_diag_bound N κ noise hg (M C (basis τ))
    refine ⟨B, n, fun y => ?_⟩
    have : phi43BaseFunctions N κ noise C y τ y =
        (hairerCanonicalData (κ := κ) N noise).canonicalPi y (M C (basis τ)) y := by
      simp only [phi43BaseFunctions, h1, ite_true]
      exact (hairerCanonicalData (κ := κ) N noise).renormalisedPi_at_base C y (basis τ)
    beta_reduce
    rw [this]
    exact hB y
  · by_cases h2 : τ = .one
    · subst h2
      exact ⟨1, 0, fun y => by simp [phi43BaseFunctions_one]⟩
    · exact ⟨0, 0, fun y => by simp [phi43BaseFunctions_other N κ noise C h1 h2]⟩

/-- **The renormalised canonical model is a smooth function model below `κ`**: its realisation on
the symbols of degree `< κ` (`F₋ ∪ {1}`) is given by the continuous functions of polynomial growth
`phi43BaseFunctions`. -/
theorem isSmoothFunctionModelBelow_phi43BaseFunctions {Cg : ℝ} {q : ℕ}
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) :
    Z.IsSmoothFunctionModelBelow (phi43BaseFunctions N κ noise C) (κ : ℝ) := by
  have hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  refine ⟨?_, fun i _ => phi43BaseFunctions_continuous N κ noise C i, ?_, ?_⟩
  · intro x i hi t ht y
    have hi' := (homogeneity_lt_kappa_iff κ i).1 hi
    by_cases h1 : i ∈ fMinus
    · rw [hZ.2.1 i h1 x t ht y]
      simp [phi43BaseFunctions, h1]
    · have h2 : i = .one := hi'.resolve_left h1
      subst h2
      let k : PolyIndex 2 := ⟨0, by simp [weight_parabolicWeight]⟩
      have hp := hZ.1.poly x k t y
      have he : (phi43PolynomialSector κ).emb k = .one := by
        rw [phi43PolynomialSector_emb]
        exact phi43PolyEmb_eq_one rfl
      rw [he] at hp
      rw [hp, polyReg_of_pos x _ ht, phi43BaseFunctions_one]
      congr 1
      funext w
      rw [polyEval_single]
      simp [k, evalParabolic]
  · intro x i _
    obtain ⟨_, B, n, hB⟩ := phi43BaseFunctions_polyBounded N κ noise hf C x i
    exact ⟨B, n, hB⟩
  · obtain ⟨B, hB0, n, hB⟩ := canonicalPolyBounded_finite_envelope
      (fun (τ : Symbol) y => phi43BaseFunctions N κ noise C y τ y)
      (phi43BaseFunctions_diag_polyBounded N κ noise C hg)
    exact ⟨B, n, fun y i _ => hB i y⟩

end RegularityStructures.Phi43

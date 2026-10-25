/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsApprox
public import RegularityStructures.BPHZ.ChaosLimitMomentsCylinder

/-!
# Riemann-type approximations of tested polynomial fields

For a random field `ψ`, kernel `k`, test function `g` and polynomials `P₁, P₂, P₃` put
`X(ω) = ∫ (∫ k(y, w) P₁(ψ(ω, w)) dw · P₂(ψ(ω, y)) + P₃(ψ(ω, y))) g(y) dy`.
Replacing `ψ(ω, ·)` by `ψ(ω, π ·)` for a finitely-valued measurable sampling map `π` gives
`chaosIntegral`, which is a polynomial of total degree at most
`max (deg P₁ + deg P₂) (deg P₃)` in the finitely many values `ψ(ω, b)`, `b ∈ range π`, with
deterministic coefficients (`exists_mvPolynomial_chaosIntegral`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*}

/-- The inner integral `∫ k(y, w) Q(ψ(ω, π w)) dw`. -/
def chaosInner (ψ : Ω → SpaceTime → ℝ) (k : SpaceTime → SpaceTime → ℝ) (Q : Polynomial ℝ)
    (π : SpaceTime → SpaceTime) (ω : Ω) (y : SpaceTime) : ℝ :=
  ∫ w, k y w * Q.eval (ψ ω (π w))

/-- The integrand `(∫ k(y,w) P₁(ψ(π w)) dw · P₂(ψ(π y)) + P₃(ψ(π y))) g(y)`. -/
def chaosIntegrand (ψ : Ω → SpaceTime → ℝ) (k : SpaceTime → SpaceTime → ℝ)
    (P₁ P₂ P₃ : Polynomial ℝ) (g : SpaceTime → ℝ) (π : SpaceTime → SpaceTime) (ω : Ω)
    (y : SpaceTime) : ℝ :=
  (chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y)) + P₃.eval (ψ ω (π y))) * g y

/-- The tested polynomial field `∫ chaosIntegrand dy` (with sampling map `π`). -/
def chaosIntegral (ψ : Ω → SpaceTime → ℝ) (k : SpaceTime → SpaceTime → ℝ)
    (P₁ P₂ P₃ : Polynomial ℝ) (g : SpaceTime → ℝ) (π : SpaceTime → SpaceTime) (ω : Ω) : ℝ :=
  ∫ y, chaosIntegrand ψ k P₁ P₂ P₃ g π ω y

end RegularityStructures

end

public section

open MeasureTheory MvPolynomial

namespace RegularityStructures

variable {Ω : Type*}

/-- **Finitely sampled tested fields are polynomials of the sampled values.** -/
theorem exists_mvPolynomial_chaosIntegral {ψ : Ω → SpaceTime → ℝ}
    {k : SpaceTime → SpaceTime → ℝ} {g : SpaceTime → ℝ} {L : ℝ}
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y))
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (hgi : Integrable g) (P₁ P₂ P₃ : Polynomial ℝ)
    {π : SpaceTime → SpaceTime} (hπ : Measurable π) (T : Finset SpaceTime)
    (hT : ∀ x, π x ∈ T) :
    ∃ q : MvPolynomial T ℝ,
      q.totalDegree ≤ max (P₁.natDegree + P₂.natDegree) P₃.natDegree ∧
      ∀ ω, chaosIntegral ψ k P₁ P₂ P₃ g π ω = eval (fun a : T => ψ ω a) q := by
  set κ : SpaceTime → SpaceTime → ℝ := fun b y => ∫ w in π ⁻¹' {b}, k y w with hκ
  have hκm : ∀ b, Measurable (κ b) := fun b =>
    (hkm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (π ⁻¹' {b}))).measurable
  have hκb : ∀ b y, |κ b y| ≤ L := fun b y => by
    calc |κ b y| = ‖∫ w in π ⁻¹' {b}, k y w‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ w in π ⁻¹' {b}, ‖k y w‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, ‖k y w‖ :=
        setIntegral_le_integral (hki y).norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      _ ≤ L := hL y
  have hgκ : ∀ b, Integrable (fun y => g y * κ b y) := fun b =>
    Integrable.mono' (hgi.norm.mul_const L) (hgi.1.mul (hκm b).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using hκb b y) (norm_nonneg _))
  have hinner : ∀ ω y, chaosInner ψ k P₁ π ω y = ∑ b ∈ T, P₁.eval (ψ ω b) * κ b y :=
    fun ω y => integral_mul_comp_eq_sum hπ T hT (hki y) (fun u => P₁.eval (ψ ω u))
  have hpt : ∀ ω y, chaosIntegrand ψ k P₁ P₂ P₃ g π ω y =
      (∑ b ∈ T, P₁.eval (ψ ω b) * ((g y * κ b y) * P₂.eval (ψ ω (π y)))) +
        g y * P₃.eval (ψ ω (π y)) := by
    intro ω y
    unfold chaosIntegrand
    rw [hinner, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => by ring
    · ring
  have hI : ∀ ω, chaosIntegral ψ k P₁ P₂ P₃ g π ω =
      (∑ b ∈ T, P₁.eval (ψ ω b) *
          ∑ a ∈ T, P₂.eval (ψ ω a) * ∫ y in π ⁻¹' {a}, g y * κ b y) +
        ∑ a ∈ T, P₃.eval (ψ ω a) * ∫ y in π ⁻¹' {a}, g y := by
    intro ω
    unfold chaosIntegral
    simp_rw [hpt]
    have i1 : ∀ b ∈ T, Integrable
        (fun y => P₁.eval (ψ ω b) * ((g y * κ b y) * P₂.eval (ψ ω (π y)))) := fun b _ =>
      (integrable_mul_comp hπ T hT (hgκ b) (fun u => P₂.eval (ψ ω u))).const_mul _
    have i2 : Integrable (fun y => g y * P₃.eval (ψ ω (π y))) :=
      integrable_mul_comp hπ T hT hgi (fun u => P₃.eval (ψ ω u))
    rw [integral_add (integrable_finsetSum _ i1) i2, integral_finsetSum _ i1,
      integral_mul_comp_eq_sum hπ T hT hgi (fun u => P₃.eval (ψ ω u))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul,
      integral_mul_comp_eq_sum hπ T hT (hgκ b) (fun u => P₂.eval (ψ ω u))]
  refine ⟨(∑ b : T, ∑ a : T, C (∫ y in π ⁻¹' {(a : SpaceTime)}, g y * κ b y) *
      (chaosPolyAt b P₁ * chaosPolyAt a P₂)) +
    ∑ a : T, C (∫ y in π ⁻¹' {(a : SpaceTime)}, g y) * chaosPolyAt a P₃, ?_, fun ω => ?_⟩
  · refine (totalDegree_add _ _).trans (max_le_max ?_ ?_)
    · refine totalDegree_finsetSum_le fun b _ => ?_
      refine totalDegree_finsetSum_le fun a _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_mul _ _).trans (add_le_add (totalDegree_chaosPolyAt_le _ _)
        (totalDegree_chaosPolyAt_le _ _))
    · refine totalDegree_finsetSum_le fun a _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact totalDegree_chaosPolyAt_le _ _
  · rw [hI]
    simp only [map_add, map_sum, map_mul, eval_C, eval_chaosPolyAt]
    simp only [← Finset.sum_coe_sort T]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      ring

end RegularityStructures

end

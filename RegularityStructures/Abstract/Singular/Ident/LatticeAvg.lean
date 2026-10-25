/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.Pointwise
public import RegularityStructures.Abstract.Singular.LatticeApprox.Defs
public import RegularityStructures.Abstract.WeightedSingularDefs

/-!
# The lattice average of the model functions, and its domination

`latticeAvg 𝒯 g γ f n y = ∑_k χ_{n,k}(y) (Π_{z_{n,k}} f(z_{n,k}))(y)` is the integrand of the lattice
approximation `S_n f ψ = ∫ ψ · latticeAvg n`.  Since the cells form a causal partition of unity,
`latticeAvg` is an average of the values `G_z(y)` over the lattice points `z` at distance
`≤ 8 · 2^{-n}` in the past of `y`; for such `z` in the slab `s^2 ≤ z₀` (`s = 2^{-n}`), so
`d(y, z) ≤ 8 w_z` and the crude bound `abs_fnComb_le_of_slab` applies, giving the uniform bound
`|latticeAvg n y| ≤ identDom y` for `n ≥ 1` (`abs_latticeAvg_le`).

Source: [Hai14] = arXiv:1303.5113v4, Remark 3.15 and proof of Prop. 7.2 (lattice form).
-/

@[expose] public noncomputable section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑_k χ_{n,k}(y) (Π_{z_{n,k}} f(z_{n,k}))(y)`. -/
def latticeAvg (𝒯 : RegularityStructure ι) (g : ParabolicSpace → ι → ParabolicSpace → ℝ)
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (n : ℕ) (y : ParabolicSpace) : ℝ :=
  ∑ᶠ k, latticeCell n k y * Model.fnComb 𝒯 g γ (latticePoint n k) (f (latticePoint n k)) y

/-- The dominating function: `(∑_{deg j < γ} |g_{y,j}(y)|) · Cf (1 + C_Γ⁺) K · (y₀/3)^{min(η,0)/2}`
for `y₀ > 0`, and `0` otherwise. -/
def identDom (𝒯 : RegularityStructure ι) (g : ParabolicSpace → ι → ParabolicSpace → ℝ)
    (γ η Cf CGam : ℝ) (y : ParabolicSpace) : ℝ :=
  if 0 < y.1 then
    (∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y|) *
      (Cf * (1 + max CGam 0) * identDomConst 𝒯 * Real.sqrt (y.1 / 3) ^ min η 0)
  else 0

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem latticeCell_geometry {n : ℕ} {k : LatticeIndex} {y : ParabolicSpace}
    (h : latticeCell n k y ≠ 0) :
    0 < y.1 - (latticePoint n k).1 ∧ y.1 - (latticePoint n k).1 < 2 * (((2 : ℝ) ^ n)⁻¹) ^ 2 ∧
      parabolicNorm (y - latticePoint n k) ≤ 8 * ((2 : ℝ) ^ n)⁻¹ :=
  ⟨(latticeCell_ne_zero h).1.1, (latticeCell_ne_zero h).1.2, parabolicNorm_sub_latticePoint_le h⟩

theorem sq_le_latticePoint_fst {n : ℕ} {k : LatticeIndex} (h : 0 < (latticePoint n k).1) :
    (((2 : ℝ) ^ n)⁻¹) ^ 2 ≤ (latticePoint n k).1 := by
  rw [latticePoint_fst] at h ⊢
  have hs : 0 < (((2 : ℝ) ^ n)⁻¹) ^ 2 := by positivity
  have hk : (0 : ℝ) < (k.1 : ℝ) := pos_of_mul_pos_right h hs.le
  have hk1 : (1 : ℝ) ≤ (k.1 : ℝ) := by
    have : (0 : ℤ) < k.1 := by exact_mod_cast hk
    exact_mod_cast this
  exact le_mul_of_one_le_right hs.le hk1

theorem abs_finsum_cell_sub_le {n : ℕ} {y : ParabolicSpace} {a : LatticeIndex → ℝ} {c B : ℝ}
    (h : ∀ k, latticeCell n k y ≠ 0 → |a k - c| ≤ B) :
    |(∑ᶠ k, latticeCell n k y * a k) - c| ≤ B := by
  classical
  set s := (finite_support_latticeCell n y).toFinset with hsdef
  have hs : ∀ k, latticeCell n k y ≠ 0 → k ∈ s := fun k hk => by
    simpa [hsdef, Set.Finite.mem_toFinset] using hk
  have h1 : ∑ k ∈ s, latticeCell n k y = 1 := sum_latticeCell_eq_one hs
  have h2 : ∑ᶠ k, latticeCell n k y * a k = ∑ k ∈ s, latticeCell n k y * a k :=
    finsum_eq_sum_of_support_subset _ fun k hk => hs k (left_ne_zero_of_mul hk)
  have h3 : ∑ k ∈ s, latticeCell n k y * a k - c = ∑ k ∈ s, latticeCell n k y * (a k - c) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  rw [h2, h3]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ s, |latticeCell n k y * (a k - c)| ≤ ∑ k ∈ s, latticeCell n k y * B := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : latticeCell n k y ≠ 0 := by
          simpa [hsdef, Set.Finite.mem_toFinset] using hk
        rw [abs_mul, abs_of_nonneg (latticeCell_nonneg _ _ _)]
        exact mul_le_mul_of_nonneg_left (h k hk') (latticeCell_nonneg _ _ _)
    _ = B := by rw [← Finset.sum_mul, h1, one_mul]

theorem abs_finsum_cell_le {n : ℕ} {y : ParabolicSpace} {a : LatticeIndex → ℝ} {B : ℝ}
    (h : ∀ k, latticeCell n k y ≠ 0 → |a k| ≤ B) :
    |∑ᶠ k, latticeCell n k y * a k| ≤ B := by
  simpa using abs_finsum_cell_sub_le (c := 0) (by simpa using h)

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem singularWeight_timeZeroDist_eq {z : ParabolicSpace} (hz : z ∈ timeSlab T) (hT : T ≤ 1) :
    singularWeight timeZeroDist z = Real.sqrt z.1 := by
  unfold singularWeight timeZeroDist
  rw [abs_of_pos hz.1]
  refine min_eq_right ?_
  calc Real.sqrt z.1 ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (hz.2.trans hT)
    _ = 1 := Real.sqrt_one

/-- If `f z = 0` the model function vanishes. -/
theorem fnComb_zero_right (z y : ParabolicSpace) :
    fnComb 𝒯 g γ z (0 : ι → ℝ) y = 0 := by
  simp [fnComb]

end Model

end RegularityStructures

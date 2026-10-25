/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# The slab operator of the `Φ⁴₃` fixed point for a kernel pair, weighted models

The slab operator for weighted models and a general kernel pair:
`Model.kGammaRemGSlab M h r P I γ T f = 1_{(0,T] × ℝ³} · (𝒦_γ f + R_γ f)` for a kernel pair
`(h, r)`, with additivity, homogeneity, measurability and sector values for `f` satisfying
`LayerSettingG`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- `1_{(0,T] × ℝ³} · (𝒦_γ f + R_γ f)` for the kernel pair `(h, r)`. -/
def kGammaRemGSlab (M : Model 𝒯 parabolicSemigroup) (h r : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ T : ℝ)
    (f : ParabolicSpace → ι → ℝ) : ParabolicSpace → ι → ℝ :=
  (timeSlab T).indicator (M.kGammaRemG h r P I γ f)

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ η α C₁ C₂ CPi CGam T p qG Rw : ℝ}
  {ρP ρG : ParabolicSpace → ℝ}
  {f f₁ f₂ : ParabolicSpace → ι → ℝ} {N N' : ℕ} {P : PolynomialSector 𝒯 N'}
  {h r : ParabolicSpace → ℝ}

theorem kGammaRemGSlab_of_mem (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {x : ParabolicSpace}
    (hx : x ∈ timeSlab T) : M.kGammaRemGSlab h r P I γ T f x = M.kGammaRemG h r P I γ f x :=
  Set.indicator_of_mem hx _

theorem kGammaRemGSlab_of_notMem (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {x : ParabolicSpace}
    (hx : x ∉ timeSlab T) : M.kGammaRemGSlab h r P I γ T f x = 0 :=
  Set.indicator_of_notMem hx _

private theorem sum_ite_single_mem_G {V : Submodule ℝ (ι → ℝ)} (b : ℝ)
    (hk : ∀ k : PolyIndex N', polyDeg N' k < b → (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V)
    (c : PolyIndex N' → ℝ) :
    (∑ k : PolyIndex N', if polyDeg N' k < b then c k • (Pi.single (P.emb k) 1 : ι → ℝ) else 0) ∈
      V := by
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (hk k h)
  · exact Submodule.zero_mem _

/-- **Values of `𝒦_γ f + R_γ f` in a sector `V`:** if `I` maps the sector `V_A ∋ f(x)` into `V`
and the polynomials `X^k`, `|k|_𝔰 < γ + 2`, lie in `V`, then `(𝒦_γ f + R_γ f)(x) ∈ V`. -/
theorem kGammaRemG_mem {V VA : Submodule ℝ (ι → ℝ)} (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hIV : ∀ a ∈ VA, I a ∈ V)
    (hpolyV : ∀ k : PolyIndex N', polyDeg N' k < γ + 2 → (Pi.single (P.emb k) 1 : ι → ℝ) ∈ V)
    {x : ParabolicSpace} (hfA : f x ∈ VA) (hfT : f x ∈ lowerSubspace 𝒯.deg γ) :
    M.kGammaRemG h r P I γ f x ∈ V := by
  classical
  have hJ : jMapP M h P x (f x) ∈ V := by
    change ∑ i, f x i • jVecP M h P x i ∈ V
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : f x i = 0
    · rw [hi, zero_smul]; exact Submodule.zero_mem _
    · have hdi : 𝒯.deg i < γ := by
        by_contra hge
        exact hi (hfT i (not_lt.1 hge))
      refine Submodule.smul_mem _ _ ?_
      exact sum_ite_single_mem_G (𝒯.deg i + 2)
        (fun k hk => hpolyV k (by linarith)) _
  have hN : M.nVecS h P γ f x ∈ V :=
    sum_ite_single_mem_G (γ + 2) hpolyV (fun k => M.nCoeffS h f x k.1 /
      multiFactorial k.1)
  have hR : M.remVecG r P γ f x ∈ V :=
    sum_ite_single_mem_G (γ + 2) hpolyV (fun k => M.remPairing f
      (fun y => lineIter (multiDirs k.1) r (x - y)) / multiFactorial k.1)
  unfold kGammaRemG kGammaS
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hIV _ hfA) hJ) hN) hR

end Model

end RegularityStructures

end

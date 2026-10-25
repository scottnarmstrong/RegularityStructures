/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Main

/-!
# The multilevel Schauder estimate

The statement `RegularityStructures.Statements.Model.kGamma_mem_modelledDistributions`.
Its proof is `RegularityStructures.Model.kGamma_mem_modelledDistributions`,
in the module `RegularityStructures.Abstract.Integration.Theorem512.Main`.
-/

public section

namespace RegularityStructures

/-- **The multilevel Schauder estimate** [Hai14, Theorem 5.12], first part: `𝒦_γ` maps `D^γ` into
`D^{γ+2}`, with the bound `c · max 1 C_I · max 1 C_Π · max C_Γ 1 · C_f`, where `c` depends only
on the regularity structure, `γ` and the annihilation order.
The model bounds and the bound on `f` are global, whereas [Hai14, Theorem 5.12] is local. Every
degree of the regularity structure below `γ` must exceed `-2`, which excludes the noise symbol of
the Φ⁴₃ structure (degree `-5/2 - κ`); the integration map `I` has no component in the abstract
polynomials; only the first half of [Hai14, Theorem 5.12] is stated (not the local Lipschitz
estimate in the model). -/
theorem Statements.Model.kGamma_mem_modelledDistributions.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructures.RegularityStructure ι} {N' : ℕ}
      {γ : ℝ},
      0 < γ →
        (∀ (j : ι), 𝒯.deg j < γ → -2 < 𝒯.deg j) →
          ∀ (N : ℕ) (P : RegularityStructures.PolynomialSector 𝒯 N'),
            N' ≤ N →
              RegularityStructures.SchauderNonIntegral 𝒯 γ N' P →
                ∃ (c : ℝ),
                  0 ≤ c ∧
                    ∀ (M : RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup) {CPi CGam CI Cf : ℝ}
                      (I : (ι → ℝ) →ₗ[ℝ] ι → ℝ) (V : Submodule ℝ (ι → ℝ)),
                      RegularityStructures.SchauderSetting M N γ P I V CPi CGam CI →
                        M.IsJointMeasurable →
                          ∀ {f : RegularityStructures.ParabolicSpace → ι → ℝ},
                            f ∈ M.modelledDistributions γ →
                              M.ModelledBoundOn γ Cf Set.univ f →
                                0 ≤ Cf →
                                  (∀ (x : RegularityStructures.ParabolicSpace), f x ∈ V) →
                                    (fun (x : RegularityStructures.ParabolicSpace) =>
                                          RegularityStructures.kGamma M N P I γ f x) ∈
                                        M.modelledDistributions (γ + 2) ∧
                                      M.ModelledBoundOn (γ + 2) (c * Max.max 1 CI * Max.max 1 CPi * Max.max CGam 1 * Cf)
                                        Set.univ fun (x : RegularityStructures.ParabolicSpace) =>
                                        RegularityStructures.kGamma M N P I γ f x :=
  by exact RegularityStructures.Model.kGamma_mem_modelledDistributions

end RegularityStructures

end

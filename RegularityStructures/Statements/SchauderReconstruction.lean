/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.ReconMain

/-!
# Reconstruction of `𝒦_γ f`

The statement `RegularityStructures.Statements.Model.reconstruct_kGamma`.
Its proof is `RegularityStructures.Model.reconstruct_kGamma`,
in the module `RegularityStructures.Abstract.Integration.Theorem512.ReconMain`.
-/

public section

namespace RegularityStructures

/-- **[Hai14, Theorem 5.12, (5.17)]**: the reconstruction of `𝒦_γ f` is the convolution of the
reconstruction of `f` with the singular part `K` of the heat kernel: `R 𝒦_γ f = K ∗ Rf`.
The model bounds and the bound on `f` are global, whereas [Hai14, Theorem 5.12] is local. Every
degree of the regularity structure below `γ` must exceed `-2`, which excludes the noise symbol of
the Φ⁴₃ structure (degree `-5/2 - κ`); the integration map `I` has no component in the abstract
polynomials; only the first half of [Hai14, Theorem 5.12] is stated (not the local Lipschitz
estimate in the model). -/
theorem Statements.Model.reconstruct_kGamma.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructures.RegularityStructure ι} {N' : ℕ}
      {M : RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ}
      {P : RegularityStructures.PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] ι → ℝ} {V : Submodule ℝ (ι → ℝ)},
      RegularityStructures.SchauderSetting M N γ P I V CPi CGam CI →
        N' ≤ N →
          RegularityStructures.SchauderNonIntegral 𝒯 γ N' P →
            (∀ (k : Fin 4 →₀ ℕ), ↑(RegularityStructures.multiDeg k) ≠ γ + 2) →
              M.IsJointMeasurable →
                ∀ {CPi' : ℝ},
                  M.PiBoundOn (γ + 2) CPi' Set.univ →
                    0 ≤ CPi' →
                      ∀ {f : RegularityStructures.ParabolicSpace → ι → ℝ} {Cf : ℝ},
                        f ∈ M.modelledDistributions γ →
                          M.ModelledBoundOn γ Cf Set.univ f →
                            0 ≤ Cf →
                              (∀ (x : RegularityStructures.ParabolicSpace), f x ∈ V) →
                                (M.reconstruct fun (x : RegularityStructures.ParabolicSpace) =>
                                    RegularityStructures.kGamma M N P I γ f x) =
                                  fun (t : ℝ) (z : RegularityStructures.ParabolicSpace) =>
                                  if 0 < t then
                                    RegularityStructures.parabolicSemigroup.apply t
                                      (RegularityStructures.kConv N (M.reconstruct f)) z
                                  else 0 :=
  by exact RegularityStructures.Model.reconstruct_kGamma

end RegularityStructures

end

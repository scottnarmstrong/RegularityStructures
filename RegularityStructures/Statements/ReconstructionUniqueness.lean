/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4ReconstructionUnique

/-!
# Uniqueness of the reconstruction

The statement `RegularityStructures.Statements.Model.eq_reconstruct_of_abs_pairing_le`.
Its proof is `RegularityStructures.Model.eq_reconstruct_of_abs_pairing_le`,
in the module `RegularityStructures.Abstract.QFamilyR4ReconstructionUnique`.
-/

public section

namespace RegularityStructures

/-- **Uniqueness in [Hai14, Theorem 3.10]** on `ℝ⁴`: a Besov-type `Q`-family `Λ` with `|⟨Λ − Π_x
f(x), φ^λ_x⟩| ≤ C λ^γ` for all `0 < λ ≤ 1` and `x`, for one test function `φ ∈ B^4` with `∫ φ ≠
0`, is the reconstruction `Rf`.
The model bound and the bound on `f` are global (on all of space-time), whereas [Hai14, Theorem 3.10]
is local, on compact sets; so the statement does not apply directly to models whose bounds hold only
locally, such as random models. -/
theorem Statements.Model.eq_reconstruct_of_abs_pairing_le.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructures.RegularityStructure ι}
      (M : RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup) {γ CPi Cf : ℝ}
      {f : RegularityStructures.ParabolicSpace → ι → ℝ},
      0 < γ →
        M.PiBoundOn γ CPi Set.univ →
          0 ≤ CPi →
            f ∈ M.modelledDistributions γ →
              M.ModelledBoundOn γ Cf Set.univ f →
                0 ≤ Cf →
                  (∀ (i : ι), 𝒯.deg i < γ → -4 < 𝒯.deg i) →
                    ∀ {Λ : ℝ → RegularityStructures.ParabolicSpace → ℝ},
                      Λ ∈ RegularityStructures.parabolicSemigroup.distributions →
                        (∀ (u : ℝ), 0 < u → Measurable (Λ u)) →
                          ∀ {α CΛ : ℝ},
                            -4 < α →
                              (∀ u ∈ Set.Ioc 0 1, ∀ (y : RegularityStructures.ParabolicSpace), |Λ u y| ≤ CΛ * u ^ (α / 4)) →
                                ∀ {φ : RegularityStructures.ParabolicSpace → ℝ},
                                  φ ∈ RegularityStructures.testFunctionClass 4 →
                                    ∫ (w : RegularityStructures.ParabolicSpace), φ w ≠ 0 →
                                      ∀ {C₃ : ℝ},
                                        (∀ c ∈ Set.Ioc 0 1,
                                            ∀ (x : RegularityStructures.ParabolicSpace),
                                              |RegularityStructures.parabolicSemigroup.pairing
                                                    (fun (t : ℝ) (y : RegularityStructures.ParabolicSpace) =>
                                                      Λ t y - M.regPi x (f x) t y)
                                                    (RegularityStructures.rescaledTestFunction φ c x)| ≤
                                                C₃ * c ^ γ) →
                                          Λ = M.reconstruct f :=
  by exact RegularityStructures.Model.eq_reconstruct_of_abs_pairing_le

end RegularityStructures

end

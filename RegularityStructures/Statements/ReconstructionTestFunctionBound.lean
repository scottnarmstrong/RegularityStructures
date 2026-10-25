/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ReconstructionR4

/-!
# The reconstruction bound in test-function form

The statement `RegularityStructures.Statements.Model.abs_pairing_rescaledTestFunction_le`.
Its proof is `RegularityStructures.Model.abs_pairing_rescaledTestFunction_le`,
in the module `RegularityStructures.Abstract.ReconstructionR4`.
-/

public section

namespace RegularityStructures

/-- **The bound (3.3) of [Hai14, Theorem 3.10]** on `ℝ⁴`: if every degree below `γ > 0` exceeds
`-4`, then for every test function `φ ∈ B^4`, `0 < λ ≤ 1` and `x`, the pairing `⟨Rf − Π_x f(x),
φ^λ_x⟩` exists and is at most `C C_Π C_f λ^γ` in absolute value.
The model bound and the bound on `f` are global (on all of space-time), whereas [Hai14, Theorem 3.10]
is local, on compact sets; so the statement does not apply directly to models whose bounds hold only
locally, such as random models. -/
theorem Statements.Model.abs_pairing_rescaledTestFunction_le.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructures.RegularityStructure ι}
      (M : RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup) {γ CPi Cf : ℝ},
      0 < γ →
        M.PiBoundOn γ CPi Set.univ →
          0 ≤ CPi →
            ∀ {f : RegularityStructures.ParabolicSpace → ι → ℝ},
              f ∈ M.modelledDistributions γ →
                M.ModelledBoundOn γ Cf Set.univ f →
                  0 ≤ Cf →
                    (∀ (i : ι), 𝒯.deg i < γ → -4 < 𝒯.deg i) →
                      ∀ {φ : RegularityStructures.ParabolicSpace → ℝ},
                        φ ∈ RegularityStructures.testFunctionClass 4 →
                          ∀ {lam : ℝ},
                            0 < lam →
                              lam ≤ 1 →
                                ∀ (x : RegularityStructures.ParabolicSpace),
                                  Filter.Tendsto
                                      (fun (s : ℝ) =>
                                        ∫ (y : RegularityStructures.ParabolicSpace),
                                          M.reconstructSubAt f x s y * RegularityStructures.rescaledTestFunction φ lam x y)
                                      (nhdsWithin 0 (Set.Ioi 0))
                                      (nhds
                                        (RegularityStructures.parabolicSemigroup.pairing (M.reconstructSubAt f x)
                                          (RegularityStructures.rescaledTestFunction φ lam x))) ∧
                                    |RegularityStructures.parabolicSemigroup.pairing (M.reconstructSubAt f x)
                                          (RegularityStructures.rescaledTestFunction φ lam x)| ≤
                                      RegularityStructures.r4ReconstructionConst 𝒯 γ * CPi * Cf * lam ^ γ :=
  by exact RegularityStructures.Model.abs_pairing_rescaledTestFunction_le

end RegularityStructures

end

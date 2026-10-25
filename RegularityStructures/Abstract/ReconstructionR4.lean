/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.TestFunctionBound
public import RegularityStructures.Analysis.KernelAll
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists

/-!
# The reconstruction theorem on `ℝ⁴` in Hairer's form

For the auxiliary parabolic semigroup `parabolicSemigroup` on `ℝ⁴ = ℝ × ℝ³` (order `ℓ = 4`), a
regularity structure all of whose homogeneities below `γ` exceed `-4`, a model `M` with
`|(Q_t Π_x e_i)(x)| ≤ C_Π t^{deg i/4}` and `f ∈ D^γ` with constant `C_f`, `γ > 0`:

  `|⟨Rf − Π_x f(x), φ^λ_x⟩| ≤ C C_Π C_f λ^γ`

for every `φ ∈ B^4`, `0 < λ ≤ 1` and `x ∈ ℝ⁴`, where `φ^λ_x` is the parabolically rescaled test
function and `C` depends only on the regularity structure and `γ`
([Hai14, Theorem 3.10, (3.3)]). The pairing is the limit `⟨Λ, φ⟩ = lim_{s↓0} ∫ Λ_s φ`, which
exists. Together with `Model.exists_reconstruction` (existence, uniqueness) and
`Model.abs_reconstruct_sub_reconstruct_le` (continuity in the model) this gives
[Hai14, Theorem 3.10] on `ℝ⁴`.

Source: [Hai14, Theorem 3.10].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant of the reconstruction bound on `ℝ⁴` against `B^4` test functions. -/
def r4ReconstructionConst (𝒯 : RegularityStructure ι) (γ : ℝ) : ℝ :=
  testReconstructionConst 𝒯 parabolicSemigroup γ *
    (16 + 16 * (generatorTimeCoeff + 3 * generatorSpaceCoeff))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

/-- **The reconstruction theorem on `ℝ⁴`, test-function form** [Hai14, Theorem 3.10, (3.3)]. -/
theorem abs_pairing_rescaledTestFunction_le {𝒯 : RegularityStructure ι}
    (M : Model 𝒯 parabolicSemigroup) {γ CPi Cf : ℝ} (hγ : 0 < γ)
    (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi) {f : ParabolicSpace → ι → ℝ}
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
    (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) {lam : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (x : ParabolicSpace) :
    Filter.Tendsto
        (fun s => ∫ y, M.reconstructSubAt f x s y * rescaledTestFunction φ lam x y)
        (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing (M.reconstructSubAt f x) (rescaledTestFunction φ lam x))) ∧
      |parabolicSemigroup.pairing (M.reconstructSubAt f x) (rescaledTestFunction φ lam x)| ≤
        r4ReconstructionConst 𝒯 γ * CPi * Cf * lam ^ γ := by
  have h := M.abs_pairing_reconstructSubAt_le hγ hPi hCPi hf hfb hCf
    parabolicSemigroup_isSymmetric parabolicSemigroup_isMetricScale
    parabolicSemigroup_isJointMeasurable hdeg x hlam hlam1
    (measurable_rescaledTestFunction hφ lam x)
    (measurable_parabolicGenerator_rescaledTestFunction hφ lam x)
    (integrable_rescaledTestFunction hφ hlam x)
    (integrable_parabolicGenerator_rescaledTestFunction hφ hlam x)
    (fun y hy => rescaledTestFunction_eq_zero hφ.2.1 hlam hy)
    (fun y hy => parabolicGenerator_rescaledTestFunction_eq_zero hφ hlam hy)
    (integral_abs_rescaledTestFunction_le hφ hlam x)
    (integral_abs_parabolicGenerator_rescaledTestFunction_le hφ hlam x)
    (parabolicSemigroup_isGeneratorPair (contDiff_rescaledTestFunction_of_mem hφ lam x)
      (hasCompactSupport_rescaledTestFunction hφ hlam x))
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [r4ReconstructionConst]
  ring

end Model

end RegularityStructures

end

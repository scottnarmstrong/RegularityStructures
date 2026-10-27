import Lake

open Lake DSL

package «regularity_structures» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- Reusable infrastructure: torus, heat semigroup, negative-order Hölder–Besov spaces,
Gaussian noise. -/
@[default_target]
lean_lib «RegularityStructures» where
  globs := #[.andSubmodules `RegularityStructures]
  leanOptions := projectLeanOptions

/-- Options for the statement library: the project options, but without the unused-variables
linter. A statement may name hypotheses that its type never references (Theorem A names `hW`,
`hu₀`, `hη`, `hρ`, `hξ`, `hu`); since each statement is proved by `by exact` applied to its proof
in `Phi43`, the linter would report them. -/
private def statementLeanOptions : Array LeanOption :=
  projectLeanOptions.map fun o =>
    if o.name == `linter.unusedVariables then ⟨`linter.unusedVariables, false⟩ else o

/-- The statements of Theorem A, Proposition 3.1, the preliminary lemmas and the intermediate
steps, one declaration per file, each proved by its proof in `Phi43`, together with the
definitions they use (`Phi43Statements.Defs`). Built by default. Other modules may import only
`Phi43Statements.Defs`. -/
@[default_target]
lean_lib «Phi43Statements» where
  globs := #[.submodules `Phi43Statements]
  leanOptions := statementLeanOptions

/-- The dynamical Φ⁴₃ model: source-facing definitions and theorems. -/
@[default_target]
lean_lib «Phi43» where
  globs := #[.andSubmodules `Phi43]
  leanOptions := projectLeanOptions

/-- The statements of the global theory (global dynamics, the uniform moment bound for the
regularised equations, compatibility across Hölder exponents), one declaration per file, each
proved by its proof in `GlobalPhi43`, together with the definitions they use
(`GlobalPhi43Statements.Defs`). Built by default. -/
@[default_target]
lean_lib «GlobalPhi43Statements» where
  globs := #[.andSubmodules `GlobalPhi43Statements]
  leanOptions := statementLeanOptions

/-- Global dynamics of the Φ⁴₃ equation on `T³`: the global flow, coming down from infinity, the
Markov and Feller property, the invariant measure and the stationary solution. -/
@[default_target]
lean_lib «GlobalPhi43» where
  globs := #[.andSubmodules `GlobalPhi43]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/TheoremA`: the Mathlib-only statement of Theorem A and
its companion theorems, one intentional `sorry` per theorem. -/
lean_lib «TheoremAChallenge» where
  roots := #[`comparators.TheoremA.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/TheoremA` statements proved from the library. -/
lean_lib «TheoremASolution» where
  roots := #[`comparators.TheoremA.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/Reconstruction`: the Mathlib-only statement of the
reconstruction theorem, one intentional `sorry` per theorem. -/
lean_lib «ReconstructionChallenge» where
  roots := #[`comparators.Reconstruction.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/Reconstruction` statements proved from the library. -/
lean_lib «ReconstructionSolution» where
  roots := #[`comparators.Reconstruction.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/Schauder`: the Mathlib-only statement of the multilevel
Schauder estimate, one intentional `sorry` per theorem. -/
lean_lib «SchauderChallenge» where
  roots := #[`comparators.Schauder.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/Schauder` statements proved from the library. -/
lean_lib «SchauderSolution» where
  roots := #[`comparators.Schauder.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/GlobalDynamics`: the Mathlib-only statement of the
global dynamics of the Φ⁴₃ equation and its companion theorems, one intentional `sorry` per
theorem. -/
lean_lib «GlobalDynamicsChallenge» where
  roots := #[`comparators.GlobalDynamics.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/GlobalDynamics` statements proved from the library. -/
lean_lib «GlobalDynamicsSolution» where
  roots := #[`comparators.GlobalDynamics.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/RegularisedBound`: the Mathlib-only statement of the
uniform moment bound for the regularised equations and its companion theorems, one intentional
`sorry` per theorem. -/
lean_lib «RegularisedBoundChallenge» where
  roots := #[`comparators.RegularisedBound.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/RegularisedBound` statements proved from the library. -/
lean_lib «RegularisedBoundSolution» where
  roots := #[`comparators.RegularisedBound.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/ExponentCompatibility`: the Mathlib-only statement of the
compatibility of the global flows across Hölder exponents and its companion theorems, one
intentional `sorry` per theorem. -/
lean_lib «ExponentCompatibilityChallenge» where
  roots := #[`comparators.ExponentCompatibility.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/ExponentCompatibility` statements proved from the library. -/
lean_lib «ExponentCompatibilitySolution» where
  roots := #[`comparators.ExponentCompatibility.Solution]
  leanOptions := projectLeanOptions

/-- Witnesses: the hypotheses of the statements and of the library theorems are jointly
satisfiable. -/
@[default_target]
lean_lib «Witnesses» where
  srcDir := "tests"
  globs := #[.submodules `Witnesses]
  leanOptions := projectLeanOptions

/-- Regression examples: definitions that exclude degenerate objects, and obstructions
that explain the choices of the formalisation. -/
@[default_target]
lean_lib «Regression» where
  srcDir := "tests"
  globs := #[.submodules `regression]
  leanOptions := projectLeanOptions

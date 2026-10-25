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

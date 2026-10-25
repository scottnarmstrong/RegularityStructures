/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Singular.LatticeApprox
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# The operator `𝒦_γ` for singular modelled distributions

[Hai14, (5.15)–(5.16)] with the reconstruction replaced by the lattice test-function
reconstruction `Model.latticeRecon` (Abstract/Singular/LatticeApprox) and the shells
`K_n = scaledShell h n` of a profile `h` (for the fixed point: the causal profile
`annKernel0C N`, so that `D^k K_n(x − ·)` only sees the past of `x`):

* `singShellPairing M h f x k n = ⟨Rf − Π_x f(x), D^k K_n(x − ·)⟩`;
* `nCoeffS M h f x k = ∑_n singShellPairing M h f x k n`;
* `nVecS M h P γ f x = ∑_{|k|_𝔰 < γ + 2} nCoeffS M h f x k / k! · X^k`;
* `kGammaS M h P I γ f x = I f(x) + J(x) f(x) + nVecS M h P γ f x`, with `J = jMapP M h P`.

Source: [Hai14] = arXiv:1303.5113v4, (5.15)–(5.16), §6 (Proposition 6.16), §7 (Theorem 7.1).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- `⟨Rf − Π_x f(x), D^k K_n(x − ·)⟩` for the lattice reconstruction and `K_n = scaledShell h n`. -/
def singShellPairing (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) -
    parabolicSemigroup.pairing (M.regPi x (f x))
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))

/-- The coefficient of `X^k / k!` in `N_γ f(x)`: `∑_n ⟨Rf − Π_x f(x), D^k K_n(x − ·)⟩`. -/
def nCoeffS (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) : ℝ :=
  ∑' n : ℕ, M.singShellPairing h f x k n

open Classical in
/-- `(N_γ f)(x) = ∑_{|k|_𝔰 < γ + 2} nCoeffS / k! · X^k` [Hai14, (5.16)]. -/
def nVecS (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < γ + 2 then
    (M.nCoeffS h f x k.1 / multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

/-- `(𝒦_γ f)(x) = I f(x) + J(x) f(x) + (N_γ f)(x)` [Hai14, (5.15)] for the lattice
reconstruction and the shells of the profile `h`. -/
def kGammaS (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) : ι → ℝ :=
  I (f x) + jMapP M h P x (f x) + M.nVecS h P γ f x

end Model

end RegularityStructures

end

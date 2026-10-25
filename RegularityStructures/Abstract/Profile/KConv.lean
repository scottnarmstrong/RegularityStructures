/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# The function `K ∗ Λ` for a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Commute.KConv`: for a
`Q`-family `Λ` all of whose local exponents exceed `-2`, the convolution with `K = ∑_n K_n`,
`K_n = scaledShell h n`, is the function
  `kConvP h Λ z = ∑_n ⟨Λ, K_n(z - ·)⟩`.
The series converges absolutely (`summable_and_abs_kConv_leP`) and `kConvP h Λ` has polynomial
growth.  The profile-independent auxiliary lemmas (`kConvRate`, `hasSum_annShell_bound`, ...) are
reused.  Input of [Hai14, Lemma 5.16].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `K ∗ Λ (z) = ∑_n ⟨Λ, K_n(z - ·)⟩`, `K_n = scaledShell h n`. -/
def kConvP (h : ParabolicSpace → ℝ) (Λ : ℝ → ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))

end RegularityStructures

end


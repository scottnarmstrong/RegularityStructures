/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossTables
public import Phi43.BPHZ.TreeI2Psi2CrossChaosFour
public import Phi43.BPHZ.TreeI2Psi2DifferenceAlgebra
public import Phi43.BPHZ.TreeI2Psi2DiagramDiffBound

/-!
# Pointwise bounds for the second difference of the chaos kernels at two mollifiers

`i2Psi2DiffChaos4Two N ρ ρ' a b y y' w w'` and `i2Psi2DiffChaos2Two` are the mixed second
differences `χ(ρa,ρa,ρa,ρa) - χ(ρa,ρa,ρ'b,ρ'b) - χ(ρ'b,ρ'b,ρa,ρa) + χ(ρ'b,ρ'b,ρ'b,ρ'b)` of the
chaos-`4` and chaos-`2` kernels of `TreeI2Psi2CrossChaos`.  With the kernel increments
`A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')` and `μ = (max a b)^θ`,
`θ ∈ (0, 1]`: `|A(w) A'(w') Δ₄(w, w')| ≤ C μ² i2Psi2Maj4 θ K x y y' (w, w')`, and likewise for
chaos `2` with `i2Psi2Maj2`, for `a, b ∈ (0, 1]`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The second difference of the chaos-`4` kernels over the pair `((ρ, a), (ρ', b))`. -/
def i2Psi2DiffChaos4Two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ, ρ] ![a, a, a, a] y y' w w' -
    hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' w w' -
    hairerI2Psi2Chaos4Two N ![ρ', ρ', ρ, ρ] ![b, b, a, a] y y' w w' +
    hairerI2Psi2Chaos4Two N ![ρ', ρ', ρ', ρ'] ![b, b, b, b] y y' w w'

/-- The second difference of the chaos-`2` kernels over the pair `((ρ, a), (ρ', b))`. -/
def i2Psi2DiffChaos2Two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ, ρ] ![a, a, a, a] y y' w w' -
    hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' w w' -
    hairerI2Psi2Chaos2Two N ![ρ', ρ', ρ, ρ] ![b, b, a, a] y y' w w' +
    hairerI2Psi2Chaos2Two N ![ρ', ρ', ρ', ρ'] ![b, b, b, b] y y' w w'

/-- The table `(Q_{ρa,ρa}, Q_{ρa,ρ'b}, Q_{ρ'b,ρa}, Q_{ρ'b,ρ'b})(z)`. -/
def i2Psi2Tab1Two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ) (z : SpaceTime) :
    I3PsiDiffTable :=
  ⟨hairerCrossCovarianceTwo N ρ a ρ a z, hairerCrossCovarianceTwo N ρ a ρ' b z,
    hairerCrossCovarianceTwo N ρ' b ρ a z, hairerCrossCovarianceTwo N ρ' b ρ' b z⟩

/-- The table `(Q_{ρa,ρa}, Q_{ρa,ρa}, Q_{ρ'b,ρ'b}, Q_{ρ'b,ρ'b})(z)`. -/
def i2Psi2Tab2Two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ) (z : SpaceTime) :
    I3PsiDiffTable :=
  ⟨hairerCrossCovarianceTwo N ρ a ρ a z, hairerCrossCovarianceTwo N ρ a ρ a z,
    hairerCrossCovarianceTwo N ρ' b ρ' b z, hairerCrossCovarianceTwo N ρ' b ρ' b z⟩

/-- The table `(Q_{ρa,ρa}, Q_{ρ'b,ρ'b}, Q_{ρa,ρa}, Q_{ρ'b,ρ'b})(z)`. -/
def i2Psi2Tab3Two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ) (z : SpaceTime) :
    I3PsiDiffTable :=
  ⟨hairerCrossCovarianceTwo N ρ a ρ a z, hairerCrossCovarianceTwo N ρ' b ρ' b z,
    hairerCrossCovarianceTwo N ρ a ρ a z, hairerCrossCovarianceTwo N ρ' b ρ' b z⟩

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem i2Psi2DiffChaos4Two_eq (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (y y' w w' : SpaceTime) :
    i2Psi2DiffChaos4Two N ρ ρ' a b y y' w w' =
      4 * i2Psi2Dm (i2Psi2Tab1Two N ρ ρ' a b (w - w')) (i2Psi2Tab1Two N ρ ρ' a b (w - w'))
          (i2Psi2Tab1Two N ρ ρ' a b (y - y')) (i2Psi2Tab1Two N ρ ρ' a b (y - y')) +
        4 * i2Psi2Dm (i2Psi2Tab1Two N ρ ρ' a b (w - y')) (i2Psi2Tab1Two N ρ ρ' a b (w - y'))
          (i2Psi2Tab1Two N ρ ρ' a b (y - w')) (i2Psi2Tab1Two N ρ ρ' a b (y - w')) +
        16 * i2Psi2Dm (i2Psi2Tab1Two N ρ ρ' a b (w - w')) (i2Psi2Tab1Two N ρ ρ' a b (w - y'))
          (i2Psi2Tab1Two N ρ ρ' a b (y - w')) (i2Psi2Tab1Two N ρ ρ' a b (y - y')) := by
  simp only [i2Psi2DiffChaos4Two, hairerI2Psi2Chaos4Two, hairerWickSquareFourChaos4, i2Psi2Dm,
    i2Psi2Tab1Two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem i2Psi2DiffChaos2Two_eq (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (y y' w w' : SpaceTime) :
    i2Psi2DiffChaos2Two N ρ ρ' a b y y' w w' =
      16 * i2Psi2Dm (i2Psi2Tab2Two N ρ ρ' a b (w - y)) (i2Psi2Tab3Two N ρ ρ' a b (w' - y'))
          (i2Psi2Tab1Two N ρ ρ' a b (w - w')) (i2Psi2Tab1Two N ρ ρ' a b (y - y')) +
        16 * i2Psi2Dm (i2Psi2Tab2Two N ρ ρ' a b (w - y)) (i2Psi2Tab3Two N ρ ρ' a b (w' - y'))
          (i2Psi2Tab1Two N ρ ρ' a b (w - y')) (i2Psi2Tab1Two N ρ ρ' a b (y - w')) := by
  simp only [i2Psi2DiffChaos2Two, hairerI2Psi2Chaos2Two, hairerWickSquareFourChaos2, i2Psi2Dm,
    i2Psi2Tab1Two, i2Psi2Tab2Two, i2Psi2Tab3Two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

end RegularityStructures.Phi43

end

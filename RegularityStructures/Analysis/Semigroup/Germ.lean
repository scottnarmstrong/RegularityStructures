/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Germs and their semigroup reconstruction

A *germ* is a family `F : E → ℝ → E → ℝ` of `Q`-distributions indexed by base points: `F y` is the
local description of the target distribution near `y`, and its diagonal `F y t y = Q_t(y, F_y)` is
what the reconstruction is compared with. In the regularity-structures application
`F y = Π_y f(y)`.

* `IsGerm F`: each `F y` is a `Q`-distribution, and the diagonal `y ↦ F y t y` is measurable and
  bounded for `0 < t ≤ 1`;
* `IsCoherent F γ A C`: `|F y t z − F z t z| ≤ C ∑_{a ∈ A} t^{a/ℓ} d(z, y)^{γ - a}` for
  `0 < t ≤ 1` ([Hos25, proof of Theorem 4.1, step (1)]; [CZ20, Definition 4.1]);
* `approx F t s = R^t_s F`, the function `x ↦ ∫ Q_{t-s}(x, y) Q_s(y, F_y) dy` for `s < t`, and
  `x ↦ Q_t(x, F_x)` for `s = t` ([Hos25, proof of Theorem 4.1]);
* `reconstruct F t x = lim_{s ↓ 0} R^t_s F(x)` for `t > 0`, and `0` for `t ≤ 0`.

Source: [Hos25, Section 4], [CZ20].
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The diagonal `y ↦ F y t y = Q_t(y, F_y)` of a germ. -/
def diag (F : E → ℝ → E → ℝ) (t : ℝ) (y : E) : ℝ := F y t y

/-- Regularity of a germ: every `F y` is a `Q`-distribution and the diagonal is measurable for
`t > 0` and bounded for `0 < t ≤ 1`. -/
structure IsGerm (F : E → ℝ → E → ℝ) : Prop where
  mem : ∀ y, F y ∈ K.distributions
  measurable_diag : ∀ ⦃t : ℝ⦄, 0 < t → Measurable (diag F t)
  bounded_diag : ∀ ⦃t : ℝ⦄, t ∈ Ioc (0 : ℝ) 1 → ∃ B, ∀ y, |diag F t y| ≤ B

/-- Coherence of order `γ` with exponent set `A` and constant `C`:
`|Q_t(z, F_y - F_z)| ≤ C ∑_{a ∈ A} t^{a/ℓ} d(z, y)^{γ - a}` for `0 < t ≤ 1`. -/
def IsCoherent (F : E → ℝ → E → ℝ) (γ : ℝ) (A : Finset ℝ) (C : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ Ioc (0 : ℝ) 1 → ∀ y z,
    |F y t z - F z t z| ≤ C * ∑ a ∈ A, t ^ (a / K.order) * K.scaleDist z y ^ (γ - a)

/-- The approximation `R^t_s F`: `x ↦ ∫ Q_{t-s}(x, y) Q_s(y, F_y) dy` for `s < t`, and the
diagonal `x ↦ Q_s(x, F_x)` otherwise (the case of interest is `s = t`). -/
def approx (F : E → ℝ → E → ℝ) (t s : ℝ) (x : E) : ℝ :=
  if s < t then K.apply (t - s) (diag F s) x else diag F s x

/-- The reconstruction of a germ: `(RF)_t(x) = lim_{s ↓ 0} R^t_s F(x)` for `t > 0`, and `0` for
`t ≤ 0`. -/
def reconstruct (F : E → ℝ → E → ℝ) (t : ℝ) (x : E) : ℝ :=
  if 0 < t then limUnder (𝓝[>] (0 : ℝ)) (fun s => K.approx F t s x) else 0

end RegularityStructures.RegularisingSemigroup

end

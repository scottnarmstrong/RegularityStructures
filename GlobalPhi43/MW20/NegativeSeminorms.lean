module

public import GlobalPhi43.MW20.FiniteSmoothing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual local negative testing seminorms

These are suprema of the actual smoothing integrals, taking values in the
extended nonnegative reals so unbounded tests are not silently assigned zero.
The ordinary source norm includes scale 1; the recentered source norms use
0<T<1. The kernel family is a parameter. Tests use the past-looking
orientation `Ψ_T(y-x)`.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- Extended local testing supremum, allowing a base-dependent germ. -/
@[expose] noncomputable def localTestSeminorm (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (I : Set ℝ) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ t ∈ I, ENNReal.ofReal (t ^ (-α) * |pastSmooth (κ t) (G x) x|)

/-- The supremum is bounded precisely when all its actual tests are bounded. -/
theorem localTestSeminorm_le_iff (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (I : Set ℝ) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    localTestSeminorm κ D I α G ≤ ENNReal.ofReal C ↔
      ∀ x ∈ D, ∀ t ∈ I, t ^ (-α) * |pastSmooth (κ t) (G x) x| ≤ C := by
  simp only [localTestSeminorm, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hC]

/-- Extract the source test bound from the actual extended seminorm. -/
theorem localTestSeminorm_test_bound (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (I : Set ℝ) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hnorm : localTestSeminorm κ D I α G ≤ ENNReal.ofReal C)
    {x : ParabolicSpace} (hx : x ∈ D) {t : ℝ} (ht : 0 < t) (htI : t ∈ I) :
    |pastSmooth (κ t) (G x) x| ≤ C * t ^ α := by
  have hb := (localTestSeminorm_le_iff κ D I α G hC).mp hnorm x hx t htI
  calc
    |pastSmooth (κ t) (G x) x| = t ^ α * (t ^ (-α) * |pastSmooth (κ t) (G x) x|) := by
      rw [← mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_mul]
    _ ≤ t ^ α * C := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)
    _ = C * t ^ α := mul_comm _ _

/-- Ordinary tree seminorm (2.9), with the closed upper scale endpoint. -/
@[expose] noncomputable def negativeTreeSeminorm (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (α : ℝ) (f : ParabolicSpace → ℝ) : ℝ≥0∞ :=
  localTestSeminorm κ D (Ioc 0 1) α (fun _ => f)

/-- The canonical recentered YV object in (2.17), including exactly C₂. -/
@[expose] noncomputable def recenteredASeminorm (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (Y V : ParabolicSpace → ℝ) (C₂ : ℝ) : ℝ≥0∞ :=
  localTestSeminorm κ D (Ioo 0 1) (-4 * ε)
    (fun x y => (Y y - Y x) * V y - C₂)

/-- The canonical recentered ZJ object in (2.18); there is no counterterm. -/
@[expose] noncomputable def recenteredBSeminorm (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (Z J : ParabolicSpace → ℝ) : ℝ≥0∞ :=
  localTestSeminorm κ D (Ioo 0 1) (-4 * ε) (fun x y => (Z y - Z x) * J y)

/-- The canonical recentered ZV object in (2.19), retaining its J counterterm. -/
@[expose] noncomputable def recenteredDSeminorm (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (Z V J : ParabolicSpace → ℝ) (C₂ : ℝ) : ℝ≥0∞ :=
  localTestSeminorm κ D (Ioo 0 1) (-(1 / 2) - 5 * ε)
    (fun x y => (Z y - Z x) * V y - 3 * C₂ * J y)

/-- Ordinary tree tests, extracted without changing the testing domain. -/
theorem negativeTreeSeminorm_test_bound (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (α : ℝ) (f : ParabolicSpace → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : negativeTreeSeminorm κ D α f ≤ ENNReal.ofReal C)
    {x : ParabolicSpace} (hx : x ∈ D) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    |pastSmooth (κ t) f x| ≤ C * t ^ α :=
  localTestSeminorm_test_bound κ D (Ioc 0 1) α (fun _ => f) hC hnorm hx ht ⟨ht, ht₁⟩

/-- The A test used in Lemma 2.10, with the literal canonical subtraction. -/
theorem recenteredASeminorm_test_bound (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (Y V : ParabolicSpace → ℝ) (C₂ : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : recenteredASeminorm κ D ε Y V C₂ ≤ ENNReal.ofReal C)
    {x : ParabolicSpace} (hx : x ∈ D) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    |pastSmooth (κ t) (fun y => (Y y - Y x) * V y - C₂) x| ≤ C * t ^ (-4 * ε) :=
  localTestSeminorm_test_bound κ D (Ioo 0 1) (-4 * ε) _ hC hnorm hx ht ⟨ht, ht₁⟩

/-- The reversed-sign B test appearing in the first product germ has the same
seminorm as the canonical (2.18) object. -/
theorem recenteredBSeminorm_reversed_test_bound (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (Z J : ParabolicSpace → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : recenteredBSeminorm κ D ε Z J ≤ ENNReal.ofReal C)
    {x : ParabolicSpace} (hx : x ∈ D) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    |pastSmooth (κ t) (fun y => (Z x - Z y) * J y) x| ≤ C * t ^ (-4 * ε) := by
  have hb := localTestSeminorm_test_bound κ D (Ioo 0 1) (-4 * ε)
    (fun x y => (Z y - Z x) * J y) hC hnorm hx ht ⟨ht, ht₁⟩
  have hid : pastSmooth (κ t) (fun y => (Z x - Z y) * J y) x =
      -pastSmooth (κ t) (fun y => (Z y - Z x) * J y) x := by
    unfold pastSmooth
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [hid, abs_neg]
  exact hb

end GlobalPhi43.MW20

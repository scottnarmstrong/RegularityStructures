/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Integration.PolyCompat.Compat
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Agreement of two models on polynomials and on realised integrals

Generic (structure-independent) pinning lemmas for two models `M`, `M'` of the same regularity
structure:

* the regularisation `Q_t Π_x` only depends on the values at `t > 0` in the pairing
  (`RegularisingSemigroup.pairing_congr_of_pos`), hence the germ `realGermP` and the realised
  family `realRegP` depend only on `Q_t Π_x e_i`, `t > 0`;
* two kernel-realising models whose `Π` agree on `e_i` agree on `I e_i`
  (`Model.regPi_integral_eq_of_realises`);
* two polynomially compatible models agree on `T̄`, and an element of `T̄` is determined by its
  `Π`-image (`Model.eq_of_regPi_eq_of_mem`).
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace RegularityStructures

theorem RegularisingSemigroup.pairing_congr_of_pos {E : Type*} [MeasurableSpace E]
    {μ : Measure E} (K : RegularisingSemigroup E μ) {Λ Λ' : ℝ → E → ℝ} (φ : E → ℝ)
    (h : ∀ s : ℝ, 0 < s → Λ s = Λ' s) : K.pairing Λ φ = K.pairing Λ' φ := by
  unfold RegularisingSemigroup.pairing
  have he : (fun s => ∫ y, Λ s y * φ y ∂μ) =ᶠ[𝓝[>] (0 : ℝ)] fun s => ∫ y, Λ' s y * φ y ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [h s hs]
  unfold limUnder
  rw [Filter.map_congr he]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem realGermP_congr {M M' : Model 𝒯 parabolicSemigroup} (h : ParabolicSpace → ℝ)
    {x : ParabolicSpace} {i : ι}
    (hag : ∀ t : ℝ, 0 < t → ∀ z, M.regPi x (Pi.single i 1) t z = M'.regPi x (Pi.single i 1) t z)
    (y : ParabolicSpace) : realGermP M h x i y = realGermP M' h x i y := by
  unfold realGermP
  refine tsum_congr fun n => ?_
  exact RegularisingSemigroup.pairing_congr_of_pos _ _ fun s hs => by
    funext z
    exact hag s hs z

namespace Model

variable {M M' : Model 𝒯 parabolicSemigroup}

/-- Two models realising the same kernel for `I`, whose `Π` agree on `e_i`, agree on `I e_i`. -/
theorem regPi_integral_eq_of_realises {h : ParabolicSpace → ℝ} {γ : ℝ}
    {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hM : M.RealisesKernelP h γ I V) (hM' : M'.RealisesKernelP h γ I V) {i : ι}
    (hi : 𝒯.deg i < γ) (hV : (Pi.single i 1 : ι → ℝ) ∈ V) (x : ParabolicSpace)
    (hag : ∀ t : ℝ, 0 < t → ∀ z, M.regPi x (Pi.single i 1) t z = M'.regPi x (Pi.single i 1) t z)
    {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    M.regPi x (I (Pi.single i 1)) t z = M'.regPi x (I (Pi.single i 1)) t z := by
  rw [hM x i hi hV t ht z, hM' x i hi hV t ht z, realRegP_of_pos _ _ _ _ ht,
    realRegP_of_pos _ _ _ _ ht]
  rw [show realGermP M h x i = realGermP M' h x i from funext (realGermP_congr h hag)]

/-- Polynomially compatible models agree on `T̄`. -/
theorem regPi_eq_of_mem_polynomialSector {N' : ℕ} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) (hM' : M'.IsPolyCompatible P) (x : ParabolicSpace) {v : ι → ℝ}
    (hv : v ∈ P.subspace) (t : ℝ) (z : ParabolicSpace) : M.regPi x v t z = M'.regPi x v t z := by
  rw [P.eq_polyEmbed_of_mem hv, regPi_polyEmbed hM, regPi_polyEmbed hM']

/-- An element of `T̄` is determined by its `Π`-image, across polynomially compatible models. -/
theorem eq_of_regPi_eq_of_mem {N' : ℕ} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) (hM' : M'.IsPolyCompatible P) (x : ParabolicSpace) {v v' : ι → ℝ}
    (hv : v ∈ P.subspace) (hv' : v' ∈ P.subspace)
    (h : ∀ t : ℝ, 0 < t → ∀ z, M.regPi x v t z = M'.regPi x v' t z) : v = v' := by
  have h0 := eq_zero_of_regPi_eq_zero hM x (Submodule.sub_mem _ hv hv') fun t ht z => by
    rw [M.regPi_sub, h t ht z, regPi_eq_of_mem_polynomialSector hM hM' x hv' t z, sub_self]
  exact sub_eq_zero.1 h0

end Model

end RegularityStructures

end

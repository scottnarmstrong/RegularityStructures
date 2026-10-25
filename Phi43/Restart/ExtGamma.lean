/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.ExtSetting

/-!
# The Hairer `Γ`-estimate for the integrals of the sources, with one constant

`exists_extGamma_const`: there is `c ≥ 0` (depending only on `κ`, `N`) such that every model `M'`
satisfying `ExtSettingWNear` at level `κ` for `phi43IntegrationF` on the `Ξ`-free block has, for
every non-polynomial `Ξ`-free symbol `i` of degree `< κ` (`ExtSource`), `x, y ∈ timeSlab 1` with
`d(y, x) ≤ 4`, and every `j` with `deg j < deg i + 2`:
`|(Γ'_{yx} 𝓘 e_i)_j| ≤ c (1 + C_Π max(C_Γ,1)) max(C_Γ,1) d^{deg i + 2 - deg j}`.
-/

public section

open Set

namespace RegularityStructures.Phi43.Restart

variable {κ : Kappa}

theorem extSource_nat {i : SymbolF} (h : ExtSource κ i) (m : ℕ) :
    (m : ℝ) ≠ phi43DegreeF κ i + 2 := by
  obtain ⟨τ, rfl, -, hn, hd⟩ := h
  exact homogeneity_add_two_ne_nat hd hn m

theorem exists_extGamma_const (N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup)
      {CPi CGam : ℝ},
      M'.ExtSettingWNear (annKernel0C N) N κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
        (blockSpan phi43XiFreeF) CPi CGam →
      ∀ i, ExtSource κ i → ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j, phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        c * (1 + CPi * max CGam 1) * max CGam 1 *
          parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j) := by
  classical
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hone : ∀ i : SymbolF, ∃ c : ℝ, 0 ≤ c ∧ (ExtSource κ i →
      ∀ (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup) {CPi CGam : ℝ},
      M'.ExtSettingWNear (annKernel0C N) N κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
        (blockSpan phi43XiFreeF) CPi CGam →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j, phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        c * (1 + CPi * max CGam 1) * max CGam 1 *
          parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j)) := by
    intro i
    by_cases hc : ExtSource κ i
    · obtain ⟨hVi, hid⟩ := hc.mem
      obtain ⟨c, hc0, hb⟩ := Model.exists_abs_gammaMap_integral_le_win_near
        (shellProfile_annKernel0C N) (blockSpan phi43XiFreeF)
        (fun j _ => phi43DegreeF_gt_neg_four κ j) (phi43PolynomialSectorF κ) hid hVi
        (fun k _ l hl => by
          have hl' : (multiDeg l : ℝ) = phi43DegreeF κ i + 2 - multiDeg k.1 := hl
          apply extSource_nat hc (multiDeg l + multiDeg k.1)
          push_cast
          linarith)
        (fun k _ j hj hjV hjd hkj => by
          obtain ⟨τ, rfl, hn, hone', hd⟩ := hc
          have hjA := mem_of_single_mem_blockSpan hjV
          cases j with
          | planted p =>
              have := phi43DegreeF_planted_ge κ p
              change homogeneity κ τ < κ.1 at hid
              change phi43DegreeF κ (.planted p) ≤ homogeneity κ τ at hjd
              linarith
          | old σ =>
              have hnσ : σ ≠ .noise := by simpa [phi43XiFreeF] using hjA
              have h1σ : σ ≠ .one := fun h => hj (h ▸ old_one_mem_range)
              change homogeneity κ σ ≤ homogeneity κ τ at hjd
              exact homogeneity_add_two_ne_nat (by linarith) h1σ _ hkj)
      exact ⟨c, hc0, fun _ M' CPi CGam S x y hx hy hxy j hj => by
        exact hb M' phi43IntegrationF S (CI := 1)
          (fun a b => phi43IntegrationF_single_abs_le a b) hx hy hxy j hj⟩
    · exact ⟨0, le_rfl, fun h => absurd h hc⟩
  choose c hc0 hc using hone
  refine ⟨∑ i, c i, Finset.sum_nonneg fun i _ => hc0 i, ?_⟩
  intro M' CPi CGam S i hi x y hx hy hxy j hj
  have h1 := hc i hi M' S hx hy hxy j hj
  have hci : c i ≤ ∑ i, c i :=
    Finset.single_le_sum (fun i _ => hc0 i) (Finset.mem_univ i)
  have hmax : 0 ≤ max CGam 1 := zero_le_one.trans (le_max_right _ _)
  have hF : 0 ≤ 1 + CPi * max CGam 1 := add_nonneg zero_le_one
    (mul_nonneg S.piBound_nonneg hmax)
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hci hF) hmax

end RegularityStructures.Phi43.Restart

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.ExtGamma
public import RegularityStructures.Abstract.Ext514W.TwoModelGammaNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The two-model Hairer `Γ`-estimate for the integrals of the sources, with one constant

Two-model companion of `Phi43.Restart.ExtGamma` [Hai14, (5.18), second bound of Thm. 5.14].
`exists_extGamma_const_diff`: there is `c ≥ 0` (depending only on `κ`, `N`) such that for any two
models `M₁, M₂` of the enlarged structure realising the kernel for `phi43IntegrationF` on the
`Ξ`-free block at level `κ`, with qualitative growth, window bounds `C_{Γ₁}, C_{Π₂}, C_{Γ₂}` and
window differences `C_{dΠ}, C_{dΓ}` at level `κ`, every non-polynomial `Ξ`-free symbol `i` of
degree `< κ` (`ExtSource`), `x, y ∈ timeSlab 1` with `d(y, x) ≤ 4` and `deg j < deg i + 2`:
`|(Γ¹_{yx} 𝓘 e_i − Γ²_{yx} 𝓘 e_i)_j| ≤ c (C_{dΠ} G² + C_{dΓ} (1 + C_{Π₂} G)) d^{deg i + 2 − deg j}`,
`G = max (max C_{Γ₁} C_{Γ₂}) 1`.
-/

public section

open Set

namespace RegularityStructures.Phi43.Restart

variable {κ : Kappa}

/-- The degree bound `-2 < deg j` on the `Ξ`-free block. -/
theorem xiFree_deg_gt_neg_two {j : SymbolF}
    (hj : (Pi.single j 1 : SymbolF → ℝ) ∈ blockSpan phi43XiFreeF) : -2 < phi43DegreeF κ j := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hjA := mem_of_single_mem_blockSpan hj
  cases j with
  | planted p =>
      have := phi43DegreeF_planted_ge κ p
      linarith
  | old τ =>
      have hn : τ ≠ .noise := by simpa [phi43XiFreeF] using hjA
      change -2 < homogeneity κ τ
      cases τ <;> simp only [homogeneity] <;> first | exact absurd rfl hn | linarith

theorem exists_extGamma_const_diff (N : ℕ) (hN : 3 ≤ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup)
      {CPi₂ CGam₁ CGam₂ CdPi CdGam : ℝ},
      M₁.IsRealisingP (annKernel0C N) κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
        (blockSpan phi43XiFreeF) →
      M₂.IsRealisingP (annKernel0C N) κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
        (blockSpan phi43XiFreeF) →
      M₁.GammaNearOn κ.1 CGam₁ hairerTimeWindow →
      M₂.PiBoundOn κ.1 CPi₂ hairerTimeWindow → M₂.GammaNearOn κ.1 CGam₂ hairerTimeWindow →
      0 ≤ CPi₂ →
      M₁.PiDiffBoundOn M₂ κ.1 CdPi hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ κ.1 CdGam hairerTimeWindow →
      0 ≤ CdPi → 0 ≤ CdGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁.GrowthModel κ.1 C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂.GrowthModel κ.1 C' C'' ρP ρG p q) →
      ∀ i, ExtSource κ i → ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j, phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M₁.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j -
          M₂.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        c * (CdPi * max (max CGam₁ CGam₂) 1 * max (max CGam₁ CGam₂) 1 +
          CdGam * (1 + CPi₂ * max (max CGam₁ CGam₂) 1)) *
          parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j) := by
  classical
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hone : ∀ i : SymbolF, ∃ c : ℝ, 0 ≤ c ∧ (ExtSource κ i →
      ∀ (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup)
      {CPi₂ CGam₁ CGam₂ CdPi CdGam : ℝ},
      M₁.IsRealisingP (annKernel0C N) κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
        (blockSpan phi43XiFreeF) →
      M₂.IsRealisingP (annKernel0C N) κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
        (blockSpan phi43XiFreeF) →
      M₁.GammaNearOn κ.1 CGam₁ hairerTimeWindow →
      M₂.PiBoundOn κ.1 CPi₂ hairerTimeWindow → M₂.GammaNearOn κ.1 CGam₂ hairerTimeWindow →
      0 ≤ CPi₂ →
      M₁.PiDiffBoundOn M₂ κ.1 CdPi hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ κ.1 CdGam hairerTimeWindow →
      0 ≤ CdPi → 0 ≤ CdGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁.GrowthModel κ.1 C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂.GrowthModel κ.1 C' C'' ρP ρG p q) →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j, phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M₁.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j -
          M₂.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        c * (CdPi * max (max CGam₁ CGam₂) 1 * max (max CGam₁ CGam₂) 1 +
          CdGam * (1 + CPi₂ * max (max CGam₁ CGam₂) 1)) *
          parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j)) := by
    intro i
    by_cases hc : ExtSource κ i
    · obtain ⟨hVi, hid⟩ := hc.mem
      obtain ⟨c, hc0, hb⟩ := Model.exists_abs_gammaMap_integral_sub_le_win_near
        (shellProfile_annKernel0C N) (phi43XiFreeF_isSector κ) (isCoordClosed_blockSpan _)
        (fun j hj _ => xiFree_deg_gt_neg_two hj)
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
      refine ⟨c, hc0, fun _ M₁ M₂ CPi₂ CGam₁ CGam₂ CdPi CdGam hr₁ hr₂ hG₁ hP₂ hG₂ hCP₂ hdP hdG
        hdP0 hdG0 g₁ g₂ x y hx hy hxy j hj => ?_⟩
      have := hb M₁ M₂ (CI := 1) phi43IntegrationF hr₁ hr₂
        (phi43IntegrationF_isAbstractIntegration κ) hG₁ hP₂ hG₂ hCP₂ hdP hdG hdP0 hdG0
        (fun a b => phi43IntegrationF_single_abs_le a b) g₁ g₂
        (fun j _ hjd k hk3 => by
          have h2 : (multiDeg k : ℝ) < 3 := by linarith
          exact_mod_cast h2)
        (fun a _ kk => phi43IntegrationF_polyEmb_eq_zero κ a kk) hN hx hy hxy j hj
      exact this
    · exact ⟨0, le_rfl, fun h => absurd h hc⟩
  choose c hc0 hc using hone
  refine ⟨∑ i, c i, Finset.sum_nonneg fun i _ => hc0 i, ?_⟩
  intro M₁ M₂ CPi₂ CGam₁ CGam₂ CdPi CdGam hr₁ hr₂ hG₁ hP₂ hG₂ hCP₂ hdP hdG hdP0 hdG0 g₁ g₂ i hi
    x y hx hy hxy j hj
  have h1 := hc i hi M₁ M₂ hr₁ hr₂ hG₁ hP₂ hG₂ hCP₂ hdP hdG hdP0 hdG0 g₁ g₂ hx hy hxy j hj
  have hci : c i ≤ ∑ i, c i :=
    Finset.single_le_sum (fun i _ => hc0 i) (Finset.mem_univ i)
  have hmax : 0 ≤ max (max CGam₁ CGam₂) 1 := zero_le_one.trans (le_max_right _ _)
  have hF : 0 ≤ CdPi * max (max CGam₁ CGam₂) 1 * max (max CGam₁ CGam₂) 1 +
      CdGam * (1 + CPi₂ * max (max CGam₁ CGam₂) 1) :=
    add_nonneg (mul_nonneg (mul_nonneg hdP0 hmax) hmax)
      (mul_nonneg hdG0 (add_nonneg zero_le_one (mul_nonneg hCP₂ hmax)))
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hci hF)
    (Real.rpow_nonneg (parabolicNorm_nonneg _) _)

end RegularityStructures.Phi43.Restart

end

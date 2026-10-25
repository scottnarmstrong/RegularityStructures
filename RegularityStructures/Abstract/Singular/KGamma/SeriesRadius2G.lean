/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.PairingG
public import RegularityStructures.Abstract.Singular.LatticeApprox.Pieces
public import RegularityStructures.Analysis.Parabolic.Lattice
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The model pairing against test functions supported in `B(x, 2)`, weighted models

Weighted (`_growth`) version, for a `Model.GrowthModel`.
For `ψ` smooth, vanishing outside `B(x, 2)` and with `‖D^j ψ‖ ≤ E` for `j ≤ 4`, `deg i < γ` and
`x ∈ timeWindow8`: `|⟨Π_x e_i, ψ⟩| ≤ C K₀ Rw² E`
(`exists_abs_pairing_regPi_single_le_of_deriv_bound_growth`).  The linearity statements need no
weight bound.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

private theorem norm_dilateCLM_le_sixtyFour {c : ℝ} (h0 : 0 ≤ c) (h8 : c ≤ 8) :
    ‖parabolicDilateCLM c‖ ≤ 64 := by
  by_cases h1 : c ≤ 1
  · exact (norm_parabolicDilateCLM_le_one h0 h1).trans (by norm_num)
  · have := norm_parabolicDilateCLM_le (not_le.1 h1).le
    nlinarith

private theorem norm_iteratedFDeriv_comp_dilate_le_eight {h : ParabolicSpace → ℝ}
    (hh : ContDiff ℝ ∞ h) {A : ℝ} (hA : ∀ k ≤ 4, ∀ u, ‖iteratedFDeriv ℝ k h u‖ ≤ A) {c : ℝ}
    (h0 : 0 ≤ c) (h8 : c ≤ 8) (a : ParabolicSpace) {k : ℕ} (hk : k ≤ 4) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v => h (a + parabolicDilate c v)) v‖ ≤ A * 64 ^ 4 := by
  have hh' : ContDiff ℝ ∞ (fun u => h (a + u)) := hh.comp (contDiff_const.add contDiff_id)
  have e : (fun v => h (a + parabolicDilate c v)) =
      (fun u => h (a + u)) ∘ (parabolicDilateCLM c) := by
    funext v; simp
  rw [e]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) _
    (hh'.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn := norm_dilateCLM_le_sixtyFour h0 h8
  have hp : ∏ _i : Fin k, ‖parabolicDilateCLM c‖ ≤ 64 ^ 4 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (pow_le_pow_left₀ (norm_nonneg _) hn k).trans
      (pow_le_pow_right₀ (by norm_num) hk)
  have hd : ‖iteratedFDeriv ℝ k (fun u => h (a + u)) (parabolicDilateCLM c v)‖ ≤ A := by
    rw [iteratedFDeriv_comp_add_left]
    exact hA k hk _
  exact mul_le_mul hd hp (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    ((norm_nonneg _).trans hd)

/-- Scaled derivative bounds of the level-`3` lattice cells in the coordinates `v ↦ z_c + v`. -/
private theorem exists_bound_latticeCell_three :
    ∃ B : ℝ, 0 < B ∧ ∀ (c : LatticeIndex), ∀ k ≤ 4, ∀ v : ParabolicSpace,
      ‖iteratedFDeriv ℝ k (fun v => latticeCell 3 c (latticePoint 3 c + parabolicDilate 1 v)) v‖
        ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_iteratedFDeriv_latticeBump4 4
  refine ⟨(C + 1) * 64 ^ 4, by positivity, fun c k hk v => ?_⟩
  have e : (fun v => latticeCell 3 c (latticePoint 3 c + parabolicDilate 1 v)) =
      fun v => latticeBump4 ((parabolicDilate ((2 : ℝ) ^ 3) (latticePoint 3 c) - latticeCoe c) +
        parabolicDilate 8 v) := by
    funext v
    rw [latticeCell_add_parabolicDilate, add_comm]
    norm_num
  rw [e]
  exact norm_iteratedFDeriv_comp_dilate_le_eight contDiff_latticeBump4
    (A := C + 1) (fun k hk u => (hC k hk u).trans (by linarith)) (by norm_num) (by norm_num) _ hk v

/-- Number of level-`3` cells meeting a ball of radius `2`. -/
private theorem card_latticeBox_three_le (x : ParabolicSpace) :
    ((latticeBox 3 x (3 ^ 2) 3).card : ℝ) ≤ (2 * 4 ^ 3 * 3 ^ 2 + 2) * (2 * 2 ^ 3 * 3 + 2) ^ 3 :=
  card_latticeBox_le (by norm_num) (by norm_num)

/-- The decomposition `ψ = ∑_c ψ χ_{3,c}` of a test function supported in `B(x, 2)` into pieces
scaled at lattice points `z_c`, `‖z_c − x‖ ≤ 3`, with radius `1` and constant `2⁴ E B`. -/
private theorem exists_pieces_of_deriv_bound {B : ℝ}
    (hBc : ∀ (c : LatticeIndex), ∀ k ≤ 4, ∀ v : ParabolicSpace,
      ‖iteratedFDeriv ℝ k (fun v => latticeCell 3 c (latticePoint 3 c + parabolicDilate 1 v)) v‖
        ≤ B) (hB : 0 < B) {x : ParabolicSpace} {ψ : ParabolicSpace → ℝ} {E : ℝ} (hE : 0 < E)
    (hψ : ContDiff ℝ ∞ ψ) (hsupp : ∀ w, 2 < parabolicNorm (w - x) → ψ w = 0)
    (hder : ∀ j ≤ 4, ∀ w, ‖iteratedFDeriv ℝ j ψ w‖ ≤ E) :
    ∃ s : Finset LatticeIndex,
      (s.card : ℝ) ≤ (2 * 4 ^ 3 * 3 ^ 2 + 2) * (2 * 2 ^ 3 * 3 + 2) ^ 3 ∧
      (∀ c ∈ s, parabolicNorm (latticePoint 3 c - x) ≤ 3) ∧
      (∀ c : LatticeIndex, IsScaledTest (fun w => ψ w * latticeCell 3 c w)
        (latticePoint 3 c) 1 (2 ^ 4 * E * B)) ∧
      ψ = fun w => ∑ c ∈ s, (1 : ℝ) * (ψ w * latticeCell 3 c w) := by
  set s0 := latticeBox 3 x (3 ^ 2) 3 with hs0
  set s := s0.filter (fun c => parabolicNorm (latticePoint 3 c - x) ≤ 3) with hs_def
  have hs : ∀ c w, ψ w * latticeCell 3 c w ≠ 0 → c ∈ s := by
    intro c w hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    have hw : parabolicNorm (w - x) ≤ 2 := by
      by_contra hlt
      exact h1 (hsupp w (not_le.1 hlt))
    have hc := parabolicNorm_sub_latticePoint_le h2
    have e : latticePoint 3 c - x = (latticePoint 3 c - w) + (w - x) := by abel
    have : parabolicNorm (latticePoint 3 c - x) ≤ 3 := by
      have := parabolicNorm_add_le (latticePoint 3 c - w) (w - x)
      rw [← e, parabolicNorm_sub_comm (latticePoint 3 c) w] at this
      norm_num at hc
      linarith
    exact Finset.mem_filter.2 ⟨mem_latticeBox_of_parabolicNorm_le this, this⟩
  have hpiece : ∀ c : LatticeIndex, IsScaledTest (fun w => ψ w * latticeCell 3 c w)
      (latticePoint 3 c) 1 (2 ^ 4 * E * B) := by
    intro c
    refine ⟨hψ.mul (contDiff_latticeCell 3 c), one_pos, le_rfl, by positivity, fun w hw => ?_,
      fun j hj v => ?_⟩
    · by_contra h
      have := parabolicNorm_sub_latticePoint_le (right_ne_zero_of_mul h)
      norm_num at this
      linarith
    · have hf1 : ContDiff ℝ ∞ (fun v => ψ (latticePoint 3 c + parabolicDilate 1 v)) :=
        hψ.comp (contDiff_const.add (parabolicDilateCLM 1).contDiff)
      have hg1 : ContDiff ℝ ∞ (fun v => latticeCell 3 c (latticePoint 3 c + parabolicDilate 1 v)) :=
        (contDiff_latticeCell 3 c).comp (contDiff_const.add (parabolicDilateCLM 1).contDiff)
      have hfA : ∀ j ≤ 4, ∀ u, ‖iteratedFDeriv ℝ j
          (fun v => ψ (latticePoint 3 c + parabolicDilate 1 v)) u‖ ≤ E := by
        intro j hj u
        have e : (fun v => ψ (latticePoint 3 c + parabolicDilate 1 v)) =
            fun v => ψ (latticePoint 3 c + v) := by
          funext v; simp [parabolicDilate_one]
        rw [e, iteratedFDeriv_comp_add_left]
        exact hder j hj _
      exact norm_iteratedFDeriv_mul_le_of_le (r := 4) hf1 hg1 hfA
        (fun j hj u => hBc c j hj u) hj v
  have hψeq : ψ = fun w => ∑ c ∈ s, (1 : ℝ) * (ψ w * latticeCell 3 c w) := by
    funext w
    have := eq_sum_latticeCell_mul (fun c w' h => hs c w' h) w (ψ w) fun h => h
    simpa using this
  refine ⟨s, ?_, fun c hc => (Finset.mem_filter.1 hc).2, hpiece, hψeq⟩
  exact (Nat.cast_le.2 (Finset.card_filter_le s0 _)).trans (card_latticeBox_three_le x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- Linearity in `τ` of the pairing with a test function supported in `B(x, 2)` (the pairing is
not centred at the support): `⟨Π_x τ, g⟩ = ∑_i τ_i ⟨Π_x e_i, g⟩` for `g` scaled at any `z`. -/
theorem pairing_regPi_eq_sum_single_offcentre_growth (M : Model 𝒯 parabolicSemigroup)
    {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ} (hg : IsScaledTest g z R A)
    (x : ParabolicSpace) :
    parabolicSemigroup.pairing (M.regPi x τ) g =
      ∑ i, τ i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) g := by
  have hΓτ : M.gammaMap z x τ ∈ lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap z x).map_lowerSubspace hτ
  rw [M.pairing_regPi_eq_gammaMap x z τ g,
    M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg hΓτ hg]
  have hcomp : ∀ j, M.gammaMap z x τ j = ∑ i, τ i * M.gammaMap z x (Pi.single i 1) j := by
    intro j
    conv_lhs => rw [eq_sum_single τ]
    simp [map_sum, Finset.sum_apply]
  have hterm : ∀ i, τ i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) g =
      τ i * ∑ j, M.gammaMap z x (Pi.single i 1) j *
        parabolicSemigroup.pairing (M.regPi z (Pi.single j 1)) g := by
    intro i
    by_cases hτi : τ i = 0
    · rw [hτi, zero_mul, zero_mul]
    · have hi : 𝒯.deg i < γ := by
        by_contra hge; exact hτi (hτ i (not_lt.1 hge))
      have he : (Pi.single i 1 : ι → ℝ) ∈ lowerSubspace 𝒯.deg γ := by
        rw [mem_lowerSubspace]
        intro j hj
        by_cases hji : j = i
        · subst hji; exact absurd hi (not_lt.2 hj)
        · simp [hji]
      rw [M.pairing_regPi_eq_gammaMap x z _ g,
        M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg
          ((M.isGradedUnipotent_gammaMap z x).map_lowerSubspace he) hg]
  simp_rw [hterm, hcomp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Linearity in `τ` of the pairing with a test function supported in `B(x, 2)`. -/
theorem pairing_regPi_eq_sum_single_of_deriv_bound_growth (M : Model 𝒯 parabolicSemigroup)
    {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) {x : ParabolicSpace} {ψ : ParabolicSpace → ℝ} {E : ℝ}
    (hE : 0 < E) (hψ : ContDiff ℝ ∞ ψ) (hsupp : ∀ w, 2 < parabolicNorm (w - x) → ψ w = 0)
    (hder : ∀ j ≤ 4, ∀ w, ‖iteratedFDeriv ℝ j ψ w‖ ≤ E) :
    parabolicSemigroup.pairing (M.regPi x τ) ψ =
      ∑ i, τ i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) ψ := by
  obtain ⟨B, hB, hBc⟩ := exists_bound_latticeCell_three
  obtain ⟨s, -, -, hpiece, hψeq⟩ := exists_pieces_of_deriv_bound hBc hB hE hψ hsupp hder
  have hsum := fun (σ' : ι → ℝ) (hσ' : σ' ∈ lowerSubspace 𝒯.deg γ) =>
    M.pairing_regPi_sum_mul_of_scaled_centres_growth G hdeg hσ' x (fun _ => (1 : ℝ))
      (fun c w => ψ w * latticeCell 3 c w) s (fun c => latticePoint 3 c) (fun _ => 1)
      (fun _ => 2 ^ 4 * E * B) (fun c _ => hpiece c)
  have hcomp : ∀ c ∈ s, parabolicSemigroup.pairing (M.regPi x τ)
      (fun w => ψ w * latticeCell 3 c w) = ∑ i, τ i * parabolicSemigroup.pairing
        (M.regPi x (Pi.single i 1)) (fun w => ψ w * latticeCell 3 c w) :=
    fun c _ => M.pairing_regPi_eq_sum_single_offcentre_growth G hdeg hτ (hpiece c) x
  have hψ' : ψ = fun w => ∑ c ∈ s, ψ w * latticeCell 3 c w := by
    funext w
    exact (congrFun hψeq w).trans (by simp)
  have key : ∀ σ' ∈ lowerSubspace 𝒯.deg γ, parabolicSemigroup.pairing (M.regPi x σ') ψ =
      ∑ c ∈ s, parabolicSemigroup.pairing (M.regPi x σ') (fun w => ψ w * latticeCell 3 c w) := by
    intro σ' h'
    have := hsum σ' h'
    simp_rw [one_mul] at this
    rw [← this, ← hψ']
  rw [key τ hτ, Finset.sum_congr rfl hcomp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hτi : τ i = 0
  · simp [hτi]
  · have hi : 𝒯.deg i < γ := by
      by_contra hge; exact hτi (hτ i (not_lt.1 hge))
    have he : (Pi.single i 1 : ι → ℝ) ∈ lowerSubspace 𝒯.deg γ := by
      rw [mem_lowerSubspace]
      intro j hj
      by_cases hji : j = i
      · subst hji; exact absurd hi (not_lt.2 hj)
      · simp [hji]
    rw [key _ he, Finset.mul_sum]

end Model

end RegularityStructures

end

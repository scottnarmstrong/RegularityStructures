/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.WrapShellWNear
public import RegularityStructures.Abstract.Singular.KGamma.WrapWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellG

/-!
# The layer bound for test functions of radius two, near-pair `Γ`-bounds

The time-Taylor remainder of `D^k K_0(x − ·)` at scale `n = 0` lives in `B(x, 2)`. Writing a
function supported in `B(x, 2)` as a finite sum of pieces `ψ χ_{3,c}` over level-3 lattice cells
gives the layer bound in terms of the sup of its derivatives of order `≤ 4`,
`|⟨R f, ψ⟩| ≤ C K₀ C_f E` (`exists_abs_latticeRecon_le_of_deriv_bound_win_near`). Consequently, for
`x` in the slab with `x₀ ≤ 4^{-n}`,
`|⟨R f, D^k K_n(x − ·)⟩| ≤ C K₀ C_f (x₀ 4^n)^m 2^{(|k| − 2 − α ∧ η) n}` for all `n ≥ 0`
(`exists_abs_latticeRecon_shell_le_timeTaylor_all_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set Filter

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

/-- **Layer bound for test functions supported in `B(x, 2)`**: if `ψ` is smooth, vanishes outside
`B(x, 2)` and after time `T`, and `‖D^i ψ‖ ≤ E` for `i ≤ 4`, then the lattice approximations
converge and `|⟨R f, ψ⟩| ≤ C K₀ C_f E`. -/
theorem exists_abs_latticeRecon_le_of_deriv_bound_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {ψ : ParabolicSpace → ℝ} {x : ParabolicSpace} {E : ℝ}, 0 < E → ContDiff ℝ ∞ ψ →
      (∀ w, 2 < parabolicNorm (w - x) → ψ w = 0) →
      (∀ i ≤ 4, ∀ w, ‖iteratedFDeriv ℝ i ψ w‖ ≤ E) → (∀ w : ParabolicSpace, T < w.1 → ψ w = 0) →
      Tendsto (M.latticeApprox f ψ) atTop (𝓝 (M.latticeRecon f ψ)) ∧
      |M.latticeRecon f ψ| ≤ C * (max 1 CGam * CPi) * Cf * E := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_le_of_scaled_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨B, hB, hBc⟩ := exists_bound_latticeCell_three
  set K : ℝ := (2 * 4 ^ 3 * 3 ^ 2 + 2) * (2 * 2 ^ 3 * 3 + 2) ^ 3 with hK
  refine ⟨Cl * K * (2 ^ 4 * B), by positivity, fun M f T Cf CPi CGam S ψ x E hE hψ hsupp hder hψT => ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  set s := latticeBox 3 x (3 ^ 2) 3 with hs_def
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
    exact mem_latticeBox_of_parabolicNorm_le this
  -- the pieces
  have hpiece : ∀ c : LatticeIndex, IsScaledTest (fun w => ψ w * latticeCell 3 c w)
      (latticePoint 3 c) 1 (2 ^ 4 * E * B) := by
    intro c
    refine ⟨hψ.mul (contDiff_latticeCell 3 c), one_pos, le_rfl, by positivity, fun w hw => ?_,
      fun i hi v => ?_⟩
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
        (fun j hj u => hBc c j hj u) hi v
  have hvan : ∀ c : LatticeIndex, ∀ w : ParabolicSpace, T < w.1 → ψ w * latticeCell 3 c w = 0 :=
    fun c w hw => by rw [hψT w hw, zero_mul]
  have hbound := fun c : LatticeIndex => hCl M f T Cf CPi CGam S (hpiece c) (hvan c)
  have hψeq : ψ = ∑ c ∈ s, fun w => ψ w * latticeCell 3 c w := by
    funext w
    rw [Finset.sum_apply]
    exact eq_sum_latticeCell_mul (fun c w' h => hs c w' h) w (ψ w) fun h => h
  have hcd : ∀ c ∈ s, ContDiff ℝ ∞ (fun w => ψ w * latticeCell 3 c w) :=
    fun c _ => (hpiece c).contDiff
  have hsu : ∀ c ∈ s, ∀ w, (fun _ : LatticeIndex => (1 : ℝ)) c < parabolicNorm (w - latticePoint 3 c) →
      (fun w => ψ w * latticeCell 3 c w) w = 0 := fun c _ => (hpiece c).supp
  have hL : ∀ c ∈ s, Tendsto (M.latticeApprox f (fun w => ψ w * latticeCell 3 c w)) atTop
      (𝓝 (M.latticeRecon f (fun w => ψ w * latticeCell 3 c w))) := fun c _ => (hbound c).1
  have hsumT := M.tendsto_latticeApprox_finset_sum_growth S.hfT G S.hdeg s
    (fun c w => ψ w * latticeCell 3 c w) (fun c => latticePoint 3 c) (fun _ => 1) hcd hsu
    (fun c => M.latticeRecon f (fun w => ψ w * latticeCell 3 c w)) hL
  have hsumR := M.latticeRecon_finset_sum_growth S.hfT G S.hdeg s
    (fun c w => ψ w * latticeCell 3 c w) (fun c => latticePoint 3 c) (fun _ => 1) hcd hsu
    (fun c => M.latticeRecon f (fun w => ψ w * latticeCell 3 c w)) hL
  rw [← hψeq] at hsumT hsumR
  refine ⟨?_, ?_⟩
  · rw [hsumR]; exact hsumT
  · rw [hsumR]
    have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
    have hpc : ∀ c ∈ s, |M.latticeRecon f (fun w => ψ w * latticeCell 3 c w)| ≤
        Cl * (max 1 CGam * CPi) * Cf * (2 ^ 4 * E * B) := by
      intro c _
      refine (hbound c).2.trans (le_of_eq ?_)
      simp
    have hcard : (s.card : ℝ) ≤ K := card_latticeBox_three_le x
    calc |∑ c ∈ s, M.latticeRecon f (fun w => ψ w * latticeCell 3 c w)|
        ≤ ∑ c ∈ s, |M.latticeRecon f (fun w => ψ w * latticeCell 3 c w)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c ∈ s, Cl * (max 1 CGam * CPi) * Cf * (2 ^ 4 * E * B) := Finset.sum_le_sum hpc
      _ = s.card * (Cl * (max 1 CGam * CPi) * Cf * (2 ^ 4 * E * B)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * (Cl * (max 1 CGam * CPi) * Cf * (2 ^ 4 * E * B)) := by
          refine mul_le_mul_of_nonneg_right hcard ?_
          have := S.hCf
          positivity
      _ = _ := by ring

variable {N : ℕ} {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
  (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)

include hh hc in
/-- The time-Taylor bound at scale `n = 0` (where the remainder lives in `B(x, 2)`):
for `x` in the slab with `x₀ ≤ 1`, `|⟨R f, D^k K_0(x − ·)⟩| ≤ C K₀ C_f x₀^m`. -/
theorem exists_abs_latticeRecon_shell_le_timeTaylor_zero_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → x.1 ≤ 1 →
      |M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h 0) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf * x.1 ^ m := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_abs_latticeRecon_le_of_deriv_bound_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  have hgs : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter hh.contDiff _
  have hgc : HasCompactSupport (lineIter (multiDirs k) h) :=
    hasCompactSupport_of_eq_zero_unit fun w hw => lineIter_eq_zero_of_lt hh.eq_zero _ hw
  obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedFDeriv_timeTaylorRem_le hgs hgc m
  refine ⟨Cl * (256 * (B + 1)), by positivity, fun M f T Cf CPi CGam S x hx hx1 => ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hx0 : 0 < x.1 := hx.1
  set E : ℝ := 256 * ((B + 1) * x.1 ^ m) with hE
  have hEpos : 0 < E := by positivity
  have hrem_eq : shellTimeTaylorRem h k m 0 x = fun y =>
      timeTaylorRem x.1 m (lineIter (multiDirs k) h) (((0 : ℝ), x.2) - y) := by
    funext y
    rw [shellTimeTaylorRem_eq hh.contDiff]
    simp [parabolicDilate_one]
  have hQs : ContDiff ℝ ∞ (timeTaylorRem x.1 m (lineIter (multiDirs k) h)) :=
    contDiff_timeTaylorRem hgs _ _
  have hder : ∀ i ≤ 4, ∀ w, ‖iteratedFDeriv ℝ i (shellTimeTaylorRem h k m 0 x) w‖ ≤ E := by
    intro i hi w
    have e : shellTimeTaylorRem h k m 0 x = fun y =>
        timeTaylorRem x.1 m (lineIter (multiDirs k) h) (((0 : ℝ), x.2) + (-ContinuousLinearMap.id ℝ
          ParabolicSpace) y) := by
      rw [hrem_eq]; funext y; simp [sub_eq_add_neg]
    have hn : ‖-ContinuousLinearMap.id ℝ ParabolicSpace‖ ≤ 4 := by
      rw [norm_neg]
      exact (ContinuousLinearMap.norm_id_le).trans (by norm_num)
    have := norm_iteratedFDeriv_comp_affine_le hQs (D := (B + 1) * x.1 ^ m)
      (fun j hj u => (hB x.1 j hj u).trans (by
        rw [abs_of_pos hx0]; nlinarith [pow_pos hx0 m])) ((0 : ℝ), x.2)
      (-ContinuousLinearMap.id ℝ ParabolicSpace) hn hi w
    rw [e]; exact this.trans (le_of_eq (by rw [hE]; ring))
  have hsupp : ∀ w, 2 < parabolicNorm (w - x) → shellTimeTaylorRem h k m 0 x w = 0 := by
    intro w hw
    refine shellTimeTaylorRem_eq_zero_of_lt hh k m 0 hx0.le (by simpa using hx1) ?_
    simpa using hw
  have hf0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0 := fun z hz =>
    S.hf0 z fun hzs => absurd hz (not_le.2 hzs.1)
  have hGT : ∀ w : ParabolicSpace, T < w.1 →
      lineIter (multiDirs k) (scaledShell h 0) (x - w) = 0 := fun w hw =>
    lineIter_multiDirs_scaledShell_sub_eq_zero hh.contDiff hc k 0 (hx.2.trans hw.le)
  have hremT : ∀ w : ParabolicSpace, T < w.1 → shellTimeTaylorRem h k m 0 x w = 0 := fun w hw => by
    unfold shellTimeTaylorRem
    rw [hGT w hw, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun j _ => by
      rw [lineIter_multiDirs_scaledShell_projection_eq_zero hh.contDiff hc _ 0 x.2
        (hx0.le.trans (hx.2.trans hw.le)), mul_zero]
  obtain ⟨ht1, hb⟩ := hCl M f T Cf CPi CGam S hEpos (contDiff_shellTimeTaylorRem hh.contDiff k m 0 x)
    hsupp hder hremT
  rw [M.latticeRecon_shell_eq_rem_growth hh hc k G S.hdeg S.hfT hf0 m 0 hsupp ht1]
  refine hb.trans (le_of_eq ?_)
  rw [hE]
  ring

include hh hc in
/-- The time-Taylor bound for all scales `n ≥ 0`: for `x` in the slab with `x₀ ≤ 4^{-n}`,
`|⟨R f, D^k K_n(x − ·)⟩| ≤ C K₀ C_f (x₀ 4^n)^m 2^{(|k| − 2 − α ∧ η) n}`. -/
theorem exists_abs_latticeRecon_shell_le_timeTaylor_all_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {x : ParabolicSpace},
      x ∈ timeSlab T → ∀ n : ℕ, x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2 →
      |M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf * (x.1 * 4 ^ n) ^ m *
          ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - min α η) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_latticeRecon_shell_le_timeTaylor_win_near hh hc k 𝒯 γ η α hdeg hγ hαγ
    hαη m
  obtain ⟨C₀, hC₀, h₀⟩ := exists_abs_latticeRecon_shell_le_timeTaylor_zero_win_near hh hc k 𝒯 γ η α hdeg hγ
    hαγ hαη m
  refine ⟨max C₁ C₀, (hC₁.trans (le_max_left _ _)), fun M f T Cf CPi CGam S x hx n hxn => ?_⟩
  have hK0 : 0 ≤ (max 1 CGam * CPi) * Cf := by
    exact mul_nonneg S.hK0 S.hCf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := h₀ M f T Cf CPi CGam S hx (by simpa using hxn)
    simp only [pow_zero, mul_one, Real.one_rpow]
    refine this.trans ?_
    have hxm : 0 ≤ x.1 ^ m := pow_nonneg hx.1.le _
    have := mul_le_mul_of_nonneg_right (le_max_right C₁ C₀) (mul_nonneg hK0 hxm)
    nlinarith [this]
  · have := h₁ M f T Cf CPi CGam S hx n hn hxn
    refine this.trans ?_
    have hxm : 0 ≤ (x.1 * 4 ^ n) ^ m * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - min α η) :=
      mul_nonneg (pow_nonneg (mul_nonneg hx.1.le (by positivity)) _) (by positivity)
    have := mul_le_mul_of_nonneg_right (le_max_left C₁ C₀) (mul_nonneg hK0 hxm)
    nlinarith [this]

end Model

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.LinearWNear
public import RegularityStructures.Abstract.Singular.Remainder.PairingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Remainder.IncrementG
public import RegularityStructures.Abstract.Singular.Remainder.Linear
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Increments of `R_γ f`, near-pair `Γ`-bounds

Lemma 7.7 (smooth part), the increment bound: for `x, y` with `x₀, y₀ ≤ T ≤ 1`, `d = ‖y − x‖_𝔰 ≤ 1`,
and `|k|_𝔰 < γ + 2`, `|(R_γ f(y) − Γ_{yx} R_γ f(x))_{X^k}| ≤ C K₀ Cf d^{γ + 2 − |k|_𝔰}`
(`exists_abs_remVec_sub_gammaMap_le_win_near`).

The component is `(1/k!)` times the pairing of `R f` with the Taylor remainder kernel
`D^k R(y − ·) − ∑_{|l|_𝔰 < γ+2−|k|_𝔰} (y−x)^l/l! D^{k+l} R(x − ·)`
(`remPairing_taylorProfile_eq_win_near`), whose scaled derivatives are `≲ d^{γ+2−|k|}` times a
spatial decay by the quantitative Taylor bounds.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open scoped ContDiff

open Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

/-- The Taylor remainder kernel is the signed sum of the pieces `D^{k}R(y − ·)`, `D^{k+l}R(x − ·)`. -/
theorem remPairing_taylorProfile_eq_win_near {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
    {γ η α Cf CPi CGam T : ℝ} (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    (k : Fin 4 →₀ ℕ) (σ : ℝ) {x y : ParabolicSpace} (hx : x.1 ≤ T) (hy : y.1 ≤ T) :
    M.RemSumm f (fun w => taylorProfile (lineIter (multiDirs k) r) σ (y - x)
        (x - w)) ∧
      M.remPairing f (fun w => taylorProfile (lineIter (multiDirs k) r) σ (y - x)
        (x - w)) =
      M.remPairing f (fun w => lineIter (multiDirs k) r (y - w)) -
        ∑ l ∈ taylorIdx σ, coeffT (parabolicCoords (y - x)) l *
          M.remPairing f (fun w => lineIter (multiDirs (k + l)) r (x - w)) := by
  classical
  set c : Option (Fin 4 →₀ ℕ) → ℝ :=
    fun o => o.elim (1 : ℝ) fun l => -coeffT (parabolicCoords (y - x)) l with hc
  set ψ : Option (Fin 4 →₀ ℕ) → ParabolicSpace → ℝ := fun o =>
    o.elim (fun w => lineIter (multiDirs k) r (y - w))
      (fun l w => lineIter (multiDirs (k + l)) r (x - w)) with hψ
  have hRem : ∀ a ∈ Finset.insertNone (taylorIdx σ), M.RemSumm f (ψ a) := fun a _ => by
    cases a with
    | none => exact S.remSumm_lineIter_win hr k hy
    | some l => exact S.remSumm_lineIter_win hr (k + l) hx
  obtain ⟨h1, h2⟩ := remPairing_sum_smul_win_near S (Finset.insertNone (taylorIdx σ)) c ψ hRem
  have hfun : (fun w => ∑ a ∈ Finset.insertNone (taylorIdx σ), c a * ψ a w) =
      fun w => taylorProfile (lineIter (multiDirs k) r) σ (y - x) (x - w) := by
    funext w
    rw [Finset.sum_insertNone, hr.taylorProfile_lineIter_sub_apply, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp [hc, hψ]
  rw [hfun] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, Finset.sum_insertNone]
  simp [hc, hψ, sub_eq_add_neg]

/-- **Increments of `R_γ f`** (Lemma 7.7, smooth part): for `x₀, y₀ ≤ T ≤ 1`,
`d = ‖y − x‖_𝔰 ≤ 1` and `|k|_𝔰 < γ + 2`,
`|(R_γ f(y) − Γ_{yx} R_γ f(x))_{X^k}| ≤ C K₀ Cf d^{γ + 2 − |k|_𝔰}`. -/
theorem exists_abs_remVec_sub_gammaMap_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {r : ParabolicSpace → ℝ} (hr : RemKernel r) (P : PolynomialSector 𝒯 N')
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N')
    (k : PolyIndex N') (hk : polyDeg N' k < γ + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ x y : ParabolicSpace, x.1 ≤ T → y.1 ≤ T →
      parabolicNorm (y - x) ≤ 1 →
      |(M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) (P.emb k)| ≤
        C * (max 1 CGam * CPi) * Cf * parabolicNorm (y - x) ^ (γ + 2 - polyDeg N' k) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_remSumm_abs_remPairing_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  have hσdef : polyDeg N' k = (multiDeg k.1 : ℝ) := rfl
  have hσ : 0 < γ + 2 - (multiDeg k.1 : ℝ) := by rw [hσdef] at hk; linarith
  obtain ⟨n, c, hc0, hT⟩ := exists_remDecay_taylorProfile hσ
  obtain ⟨BG, hBG0, hBG⟩ := hr.exists_remDecay_lineIter k.1 n 7
  refine ⟨C₂ * (c * BG), by positivity, fun M f T Cf CPi CGam S hM x y hx hy hd => ?_⟩
  set d : ℝ := parabolicNorm (y - x) with hdd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hGs : ContDiff ℝ ∞ (lineIter (multiDirs k.1) r) :=
    contDiff_lineIter hr.contDiff _
  have hΦ : IsRemKernel (taylorProfile (lineIter (multiDirs k.1) r)
      (γ + 2 - (multiDeg k.1 : ℝ)) (y - x)) (c * BG * d ^ (γ + 2 - (multiDeg k.1 : ℝ))) :=
    ⟨contDiff_taylorProfile hGs _ _, by positivity, fun i hi u hu =>
      hT hGs hBG0 hBG (y - x) hd i hi u (by linarith)⟩
  obtain ⟨-, hb⟩ := hC₂ M f T Cf CPi CGam S hΦ hx (fun w hw =>
    hr.taylorProfile_lineIter_sub_eq_zero k.1 _ (by linarith) (by linarith))
  obtain ⟨-, heq⟩ := remPairing_taylorProfile_eq_win_near S hr k.1 (γ + 2 - (multiDeg k.1 : ℝ)) hx hy
  have hD := Model.remVecG_sub_gammaMap_apply_emb hM r γ f x y k hk hNγ
  rw [← heq] at hD
  have hk1 : (1 : ℝ) ≤ multiFactorial k.1 := by exact_mod_cast multiFactorial_pos k.1
  have hDabs : |(M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) (P.emb k)| ≤
      |M.remPairing f (fun w => taylorProfile (lineIter (multiDirs k.1) r)
        (γ + 2 - (multiDeg k.1 : ℝ)) (y - x) (x - w))| := by
    rw [← hD, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ multiFactorial k.1)]
    exact le_mul_of_one_le_right (abs_nonneg _) hk1
  refine hDabs.trans (hb.trans (le_of_eq ?_))
  rw [hσdef]
  ring

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Partial derivatives on the open half space `{t > 0}` of space-time

For a function `F` on `ℝ × ℝ³`, smooth on `{t > 0}`, the coordinate derivatives
`pd i F` (`i = 0` is time) are *total* functions, set to `0` for `t ≤ 0`, so that identities between
them hold as equalities of functions. `pdIter i n` is the `n`-fold derivative and
`D k = ∂₀^{k₀} ∂₁^{k₁} ∂₂^{k₂} ∂₃^{k₃}` for a multi-index `k` (time derivative outermost).

* `SmoothPos F`: `F` is `C^∞` on `{t > 0}`; it is stable under `pd`;
* `pd_comm`: mixed partials commute on `SmoothPos` functions;
* `D_add`: `D (m + l) F = D m (D l F)`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The open half space `{t > 0}` of space-time. -/
def posTime : Set ParabolicSpace := {z | 0 < z.1}

/-- The point of space-time with coordinates `c = (c₀, c₁, c₂, c₃)`. -/
def stOfCoords (c : Fin 4 → ℝ) : ParabolicSpace := (c 0, fun j => c j.succ)

/-- The `i`-th coordinate vector of space-time. -/
def stBasis (i : Fin 4) : ParabolicSpace := stOfCoords (Pi.single i 1)

/-- `F` is `C^∞` on the open half space `{t > 0}`. -/
def SmoothPos (F : ParabolicSpace → ℝ) : Prop := ContDiffOn ℝ ∞ F posTime

/-- The derivative of `F` in the direction `v`, for `t > 0` (and `0` for `t ≤ 0`). -/
def pdv (v : ParabolicSpace) (F : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  if 0 < z.1 then fderiv ℝ F z v else 0

/-- The partial derivative in the `i`-th coordinate direction. -/
def pd (i : Fin 4) : (ParabolicSpace → ℝ) → ParabolicSpace → ℝ := pdv (stBasis i)

/-- The `n`-fold partial derivative in the `i`-th coordinate direction. -/
def pdIter (i : Fin 4) (n : ℕ) (F : ParabolicSpace → ℝ) : ParabolicSpace → ℝ := (pd i)^[n] F

/-- The mixed derivative `∂₀^{k₀} ∂₁^{k₁} ∂₂^{k₂} ∂₃^{k₃} F`. -/
def D (k : Fin 4 → ℕ) (F : ParabolicSpace → ℝ) : ParabolicSpace → ℝ :=
  pdIter 0 (k 0) (pdIter 1 (k 1) (pdIter 2 (k 2) (pdIter 3 (k 3) F)))

end RegularityStructures.Datum

end

public section

open scoped ContDiff

namespace RegularityStructures.Datum

theorem isOpen_posTime : IsOpen posTime :=
  isOpen_lt continuous_const continuous_fst

theorem stOfCoords_sum (c : Fin 4 → ℝ) : stOfCoords c = ∑ i, c i • stBasis i := by
  ext j
  · simp [stOfCoords, stBasis, Pi.single_apply, Fin.sum_univ_succ, Fin.succ_ne_zero]
  · fin_cases j <;>
      simp [stOfCoords, stBasis, Pi.single_apply, Fin.sum_univ_succ, Fin.succ_ne_zero]

theorem pdv_of_pos {v : ParabolicSpace} {F : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (hz : 0 < z.1) : pdv v F z = fderiv ℝ F z v := by
  simp [pdv, hz]

theorem pdv_of_nonpos {v : ParabolicSpace} {F : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (hz : z.1 ≤ 0) : pdv v F z = 0 := by
  simp [pdv, not_lt.2 hz]

theorem SmoothPos.differentiableAt {F : ParabolicSpace → ℝ} (hF : SmoothPos F)
    {z : ParabolicSpace} (hz : 0 < z.1) : DifferentiableAt ℝ F z :=
  (hF.differentiableOn (by simp)).differentiableAt (isOpen_posTime.mem_nhds hz)

theorem SmoothPos.pdv {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (v : ParabolicSpace) :
    SmoothPos (pdv v F) := by
  have h : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z v) posTime :=
    (hF.fderiv_of_isOpen isOpen_posTime (by simp)).clm_apply contDiffOn_const
  exact h.congr fun z hz => pdv_of_pos hz

theorem SmoothPos.pd {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (i : Fin 4) :
    SmoothPos (pd i F) := hF.pdv _

theorem SmoothPos.pdIter {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (i : Fin 4) (n : ℕ) :
    SmoothPos (pdIter i n F) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [RegularityStructures.Datum.pdIter, Function.iterate_succ_apply']
    exact ih.pd i

theorem SmoothPos.D {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (k : Fin 4 → ℕ) :
    SmoothPos (D k F) :=
  (((hF.pdIter 3 _).pdIter 2 _).pdIter 1 _).pdIter 0 _

theorem pdv_congr {v : ParabolicSpace} {F G : ParabolicSpace → ℝ}
    (h : ∀ z ∈ posTime, F z = G z) : pdv v F = pdv v G := by
  funext z
  by_cases hz : 0 < z.1
  · rw [pdv_of_pos hz, pdv_of_pos hz]
    have : F =ᶠ[nhds z] G := Filter.eventually_of_mem (isOpen_posTime.mem_nhds hz) h
    rw [this.fderiv_eq]
  · rw [pdv_of_nonpos (not_lt.1 hz), pdv_of_nonpos (not_lt.1 hz)]

theorem pdv_add {v : ParabolicSpace} {F G : ParabolicSpace → ℝ} (hF : SmoothPos F)
    (hG : SmoothPos G) : pdv v (F + G) = pdv v F + pdv v G := by
  funext z
  by_cases hz : 0 < z.1
  · simp only [Pi.add_apply, pdv_of_pos hz]
    rw [fderiv_add (hF.differentiableAt hz) (hG.differentiableAt hz)]
    rfl
  · simp [pdv_of_nonpos (not_lt.1 hz)]

theorem pdv_smul {v : ParabolicSpace} {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (c : ℝ) :
    pdv v (c • F) = c • pdv v F := by
  funext z
  by_cases hz : 0 < z.1
  · simp only [Pi.smul_apply, pdv_of_pos hz]
    rw [fderiv_const_smul (hF.differentiableAt hz)]
    rfl
  · simp [pdv_of_nonpos (not_lt.1 hz)]

theorem SmoothPos.sum {ι : Type*} {s : Finset ι} {F : ι → ParabolicSpace → ℝ}
    (hF : ∀ a ∈ s, SmoothPos (F a)) : SmoothPos (∑ a ∈ s, F a) := by
  have h : ContDiffOn ℝ ∞ (fun z => ∑ a ∈ s, F a z) posTime := ContDiffOn.sum hF
  have e : (∑ a ∈ s, F a) = fun z => ∑ a ∈ s, F a z := by
    funext z
    simp
  rw [SmoothPos, e]
  exact h

theorem SmoothPos.smul {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (c : ℝ) :
    SmoothPos (c • F) := ContDiffOn.const_smul c hF

theorem pdv_sum {v : ParabolicSpace} {ι : Type*} (s : Finset ι) {F : ι → ParabolicSpace → ℝ}
    (hF : ∀ a ∈ s, SmoothPos (F a)) : pdv v (∑ a ∈ s, F a) = ∑ a ∈ s, pdv v (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    by_cases hz : 0 < z.1
    · simp [pdv_of_pos hz]
    · simp [pdv_of_nonpos (not_lt.1 hz)]
  | insert a s ha ih =>
    have hs : SmoothPos (∑ b ∈ s, F b) := SmoothPos.sum fun b hb =>
      hF b (Finset.mem_insert_of_mem hb)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pdv_add (hF a (Finset.mem_insert_self _ _)) hs,
      ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))]

theorem pdv_pdv_apply {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (v w : ParabolicSpace)
    {z : ParabolicSpace} (hz : 0 < z.1) :
    pdv v (pdv w F) z = fderiv ℝ (fderiv ℝ F) z v w := by
  rw [pdv_of_pos hz]
  have hev : pdv w F =ᶠ[nhds z] fun z' => fderiv ℝ F z' w :=
    Filter.eventually_of_mem (isOpen_posTime.mem_nhds hz) fun z' hz' => pdv_of_pos hz'
  rw [hev.fderiv_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    ((hF.fderiv_of_isOpen isOpen_posTime (m := ∞) (by simp)).differentiableOn (by simp)).differentiableAt
      (isOpen_posTime.mem_nhds hz)
  have h := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z hd.hasFDerivAt
  have h' : HasFDerivAt (fun z' => fderiv ℝ F z' w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ F) z)) z := h
  rw [h'.fderiv]
  rfl

/-- Mixed partial derivatives commute on `C^∞` functions. -/
theorem pdv_comm {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (v w : ParabolicSpace) :
    pdv v (pdv w F) = pdv w (pdv v F) := by
  funext z
  by_cases hz : 0 < z.1
  · rw [pdv_pdv_apply hF v w hz, pdv_pdv_apply hF w v hz]
    have hc : ContDiffAt ℝ ∞ F z := hF.contDiffAt (isOpen_posTime.mem_nhds hz)
    exact (hc.isSymmSndFDerivAt (by simp)).eq v w
  · rw [pdv_of_nonpos (not_lt.1 hz), pdv_of_nonpos (not_lt.1 hz)]

theorem pd_comm {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (i j : Fin 4) :
    pd i (pd j F) = pd j (pd i F) := pdv_comm hF _ _

theorem pdIter_zero (i : Fin 4) (F : ParabolicSpace → ℝ) : pdIter i 0 F = F := rfl

theorem pdIter_succ (i : Fin 4) (n : ℕ) (F : ParabolicSpace → ℝ) :
    pdIter i (n + 1) F = pdIter i n (pd i F) := Function.iterate_succ_apply _ _ _

theorem pdIter_succ' (i : Fin 4) (n : ℕ) (F : ParabolicSpace → ℝ) :
    pdIter i (n + 1) F = pd i (pdIter i n F) := Function.iterate_succ_apply' _ _ _

theorem pdIter_add (i : Fin 4) (a b : ℕ) (F : ParabolicSpace → ℝ) :
    pdIter i (a + b) F = pdIter i a (pdIter i b F) := Function.iterate_add_apply _ _ _ _

theorem pdv_pdIter_comm {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (v : ParabolicSpace)
    (j : Fin 4) (n : ℕ) : pdv v (pdIter j n F) = pdIter j n (pdv v F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdIter_succ', pdIter_succ', ← ih]
    exact pdv_comm (hF.pdIter j n) v (stBasis j)

theorem pdIter_comm {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (i j : Fin 4) (a b : ℕ) :
    pdIter i a (pdIter j b F) = pdIter j b (pdIter i a F) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pdIter_succ', pdIter_succ', ih]
    exact (pdv_pdIter_comm (hF.pdIter i a) _ j b)

theorem D_add {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (m l : Fin 4 → ℕ) :
    D (m + l) F = D m (D l F) := by
  have h3 := hF.pdIter 3 (l 3)
  have h2 := h3.pdIter 2 (l 2)
  have h1 := h2.pdIter 1 (l 1)
  simp only [D, Pi.add_apply]
  have s3 : pdIter 3 (m 3) (pdIter 0 (l 0) (pdIter 1 (l 1) (pdIter 2 (l 2) (pdIter 3 (l 3) F)))) =
      pdIter 0 (l 0) (pdIter 1 (l 1) (pdIter 2 (l 2) (pdIter 3 (m 3 + l 3) F))) := by
    rw [pdIter_comm h1 3 0, pdIter_comm h2 3 1, pdIter_comm h3 3 2, ← pdIter_add]
  have h3' := hF.pdIter 3 (m 3 + l 3)
  have h2' := h3'.pdIter 2 (m 2 + l 2)
  have s2 : pdIter 2 (m 2) (pdIter 0 (l 0) (pdIter 1 (l 1) (pdIter 2 (l 2)
      (pdIter 3 (m 3 + l 3) F)))) =
      pdIter 0 (l 0) (pdIter 1 (l 1) (pdIter 2 (m 2 + l 2) (pdIter 3 (m 3 + l 3) F))) := by
    rw [pdIter_comm (h3'.pdIter 2 (l 2) |>.pdIter 1 (l 1)) 2 0, pdIter_comm (h3'.pdIter 2 (l 2)) 2 1,
      ← pdIter_add]
  have s1 : pdIter 1 (m 1) (pdIter 0 (l 0) (pdIter 1 (l 1)
      (pdIter 2 (m 2 + l 2) (pdIter 3 (m 3 + l 3) F)))) =
      pdIter 0 (l 0) (pdIter 1 (m 1 + l 1) (pdIter 2 (m 2 + l 2) (pdIter 3 (m 3 + l 3) F))) := by
    rw [pdIter_comm (h2'.pdIter 1 (l 1)) 1 0, ← pdIter_add]
  rw [s3, s2, s1, ← pdIter_add]

end RegularityStructures.Datum

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorOp

/-!
# Iterated coordinatewise Taylor polynomials

For a list `J` of coordinates, steps `s : Fin 4 → ℝ` and orders `m : Fin 4 → ℕ`, `tyOp J s m` is the
composition of the one-dimensional Taylor polynomials `tayOp (coordDir j) (s j) (m j)`, and
`remJ J s m φ = φ(· + ∑_{j ∈ J} s_j e_j) - tyOp J s m φ`.

* `remJ_cons`: `remJ (j :: J) φ = remJ J (S_j φ) + tyOp J (remOp e_j s_j m_j φ)`;
* `exists_abs_tyOp_le`: `|tyOp J s m ψ| ≤ ∑_{K ∈ W} d^{|K|_𝔰} |D^K ψ|` for a finite list `W` of
  derivative words, when `|s_j| ≤ d^{w_j}`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The composition of the coordinatewise Taylor polynomials. -/
def tyOp (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) : List (Fin 4) → (ParabolicSpace → ℝ) →
    (ParabolicSpace → ℝ)
  | [], φ => φ
  | j :: J, φ => tyOp s m J (tayOp (coordDir j) (s j) (m j) φ)

/-- The total displacement `∑_{j ∈ J} s_j e_j`. -/
def disp (s : Fin 4 → ℝ) (J : List (Fin 4)) : ParabolicSpace :=
  (J.map fun j => s j • coordDir j).sum

/-- The remainder `φ(· + disp) - tyOp φ`. -/
def remJ (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) (J : List (Fin 4)) (φ : ParabolicSpace → ℝ)
    (w : ParabolicSpace) : ℝ :=
  φ (w + disp s J) - tyOp s m J φ w

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem tayOp_eq (e : ParabolicSpace) (s : ℝ) (m : ℕ) (φ : ParabolicSpace → ℝ) :
    tayOp e s m φ = fun w => ∑ p ∈ Finset.range (m + 1),
      (((Nat.factorial p : ℕ) : ℝ)⁻¹ * s ^ p) * (dirDeriv e)^[p] φ w := by
  funext w; simp only [tayOp, mul_assoc]

theorem contDiff_tayOp {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace)
    (s : ℝ) (m : ℕ) : ContDiff ℝ ∞ (tayOp e s m φ) := by
  rw [tayOp_eq]
  exact ContDiff.sum fun p _ => contDiff_const.mul (contDiff_iterate_dirDeriv hφ e p)

theorem hasCompactSupport_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ParabolicSpace → ℝ}
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport fun w => ∑ i ∈ s, f i w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun w => ∑ i ∈ (∅ : Finset ι), f i w) = 0 := by funext w; simp
    rw [e]; exact HasCompactSupport.zero
  | insert a s ha ih =>
    have := (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have e : (fun w => ∑ i ∈ insert a s, f i w) = f a + fun w => ∑ i ∈ s, f i w := by
      funext w; simp [Finset.sum_insert ha]
    rw [e]; exact this

theorem iterate_dirDeriv_sub {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (e : ParabolicSpace) (p : ℕ) :
    (dirDeriv e)^[p] (fun w => f w - g w) =
      fun w => (dirDeriv e)^[p] f w - (dirDeriv e)^[p] g w := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact dirDeriv_sub (contDiff_iterate_dirDeriv hf e p) (contDiff_iterate_dirDeriv hg e p) e

theorem lineIter_iterate_dirDeriv {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : ParabolicSpace) (K : List ParabolicSpace) (n : ℕ) :
    lineIter K ((dirDeriv e)^[n] φ) = (dirDeriv e)^[n] (lineIter K φ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', lineIter_dirDeriv_comm (contDiff_iterate_dirDeriv hφ e n),
      ih, Function.iterate_succ_apply']

theorem tayOp_sub {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (e : ParabolicSpace) (s : ℝ) (m : ℕ) :
    tayOp e s m (fun w => f w - g w) = fun w => tayOp e s m f w - tayOp e s m g w := by
  funext w
  simp only [tayOp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := iterate_dirDeriv_sub hf hg e p
  rw [this]; ring

theorem lineIter_tayOp {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace)
    (s : ℝ) (m : ℕ) (K : List ParabolicSpace) :
    lineIter K (tayOp e s m φ) = tayOp e s m (lineIter K φ) := by
  rw [tayOp_eq, tayOp_eq, lineIter_finset_sum _ fun p _ =>
    contDiff_const.mul (contDiff_iterate_dirDeriv hφ e p)]
  funext w
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lineIter_const_mul (contDiff_iterate_dirDeriv hφ e p)]
  simp only
  congr 1
  rw [lineIter_iterate_dirDeriv hφ]

theorem tyOp_sub (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) :
    ∀ (J : List (Fin 4)) {f g : ParabolicSpace → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      tyOp s m J (fun w => f w - g w) = fun w => tyOp s m J f w - tyOp s m J g w
  | [], _, _, _, _ => rfl
  | j :: J, f, g, hf, hg => by
    simp only [tyOp]
    rw [tayOp_sub hf hg]
    exact tyOp_sub s m J (contDiff_tayOp hf _ _ _) (contDiff_tayOp hg _ _ _)

theorem remOp_eq_sub (e : ParabolicSpace) (s : ℝ) (m : ℕ) (φ : ParabolicSpace → ℝ) :
    remOp e s m φ = fun w => φ (w + s • e) - tayOp e s m φ w := rfl

theorem remJ_cons (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) (j : Fin 4) (J : List (Fin 4))
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    remJ s m (j :: J) φ = fun w =>
      remJ s m J (fun u => φ (u + s j • coordDir j)) w +
        tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w := by
  funext w
  have hS : ContDiff ℝ ∞ fun u => φ (u + s j • coordDir j) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have hT := contDiff_tayOp hφ (coordDir j) (s j) (m j)
  rw [remOp_eq_sub, tyOp_sub s m J hS hT]
  simp only [remJ, tyOp, disp, List.map_cons, List.sum_cons]
  rw [show w + (s j • coordDir j + (J.map fun j => s j • coordDir j).sum) =
    w + (J.map fun j => s j • coordDir j).sum + s j • coordDir j by abel]
  ring

end RegularityStructures

end

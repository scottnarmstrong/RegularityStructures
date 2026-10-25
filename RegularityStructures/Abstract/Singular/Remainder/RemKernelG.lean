/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Kernel
public import RegularityStructures.Abstract.Singular.Remainder.Defs
public import RegularityStructures.Analysis.Heat.Causal.Support
public import RegularityStructures.Analysis.Heat.Decay.Remainder
public import RegularityStructures.Abstract.Model

/-!
# Generic smooth remainder kernels

`RemKernel r`: `r : ℝ⁴ → ℝ` is smooth, causal (`r z = 0` for `z₀ ≤ 0`) and every derivative
`D^L r` along coordinate directions decays spatially, `|D^L r (z)| ≤ C (1 + |z'|²)^{-m}`, uniformly
on bounded times `z₀ ≤ T₀`.  This is the only information about the remainder `R = G − K` used by
the lift `R_γ` of the smooth remainder to singular modelled distributions.  `annRemainderC N`
is an instance (`remKernel_annRemainderC`).

`Model.remVecG r P γ f x = ∑_k X^k/k! ⟨R f, D^k r(x − ·)⟩` is the lift for the generic kernel; for
`r = annRemainderC N` it is `Model.remVec N P γ f x` (`remVecG_annRemainderC`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A smooth causal remainder kernel with spatially decaying derivatives on bounded times. -/
structure RemKernel (r : ParabolicSpace → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) r
  causal : ∀ z : ParabolicSpace, z.1 ≤ 0 → r z = 0
  decay : ∀ (L : List (Fin 4)) (m : ℕ) (T₀ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace,
    z.1 ≤ T₀ → |lineIter (L.map coordDir) r z| ≤ C * (1 + sqNorm3 z.2)⁻¹ ^ m

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

open Classical in
/-- `R_γ f(x) = ∑_{|k|_𝔰 < γ + 2} X^k / k! ⟨R f, D^k r(x − ·)⟩` for a generic remainder kernel
`r`; for `r = annRemainderC N` this is `remVec N`. -/
def remVecG (M : Model 𝒯 parabolicSemigroup) (r : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < γ + 2 then
    (M.remPairing f (fun y => lineIter (multiDirs k.1) r (x - y)) /
      multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

end Model

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem remKernel_annRemainderC (N : ℕ) : RemKernel (annRemainderC N) where
  contDiff := contDiff_annRemainderC N
  causal := fun _ h => annRemainderC_eq_zero_of_nonpos N h
  decay := fun _ m _ => exists_abs_lineIter_annRemainderC_le_of_list N _ m

namespace RemKernel

variable {r : ParabolicSpace → ℝ}

theorem lineIter_eq_zero (hr : RemKernel r) (L : List ParabolicSpace) {z : ParabolicSpace}
    (hz : z.1 ≤ 0) : lineIter L r z = 0 :=
  lineIter_eq_zero_of_nonpos hr.contDiff hr.causal L hz

theorem lineIter_sub_eq_zero (hr : RemKernel r) (L : List ParabolicSpace)
    {x y : ParabolicSpace} (h : x.1 ≤ y.1) : lineIter L r (x - y) = 0 :=
  hr.lineIter_eq_zero L (by simpa using h)

/-- For every `k`, `n` and `τ₀`, the derivatives of `D^k r` of order `≤ n` decay uniformly. -/
theorem exists_remDecay_lineIter (hr : RemKernel r) (k : Fin 4 →₀ ℕ) (n : ℕ) (τ₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ RemDecay (lineIter (multiDirs k) r) n τ₀ B := by
  have hC : ∀ p : (Σ i : Fin (n + 1), (Fin i → Fin 4)), ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ParabolicSpace, z.1 ≤ τ₀ →
        |lineIter (List.ofFn (fun i => coordDir (p.2 i)) ++ multiDirs k) r z| ≤
          C * remWt z.2 := fun p => by
    obtain ⟨C, hC0, hC⟩ := hr.decay (List.ofFn p.2 ++ (Finsupp.toMultiset k).toList) 3 τ₀
    refine ⟨C, hC0, fun z hz => ?_⟩
    have e : List.ofFn (fun i => coordDir (p.2 i)) ++ multiDirs k =
        (List.ofFn p.2 ++ (Finsupp.toMultiset k).toList).map coordDir := by
      simp [multiDirs, List.map_ofFn]
      rfl
    rw [e]
    exact hC z hz
  choose C hC0 hC using hC
  set B₀ : ℝ := ∑ p, C p with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun p _ => hC0 p
  refine ⟨4 ^ n * B₀, by positivity, fun i hi u hu => ?_⟩
  have hg : ContDiff ℝ ∞ (lineIter (multiDirs k) r) := contDiff_lineIter hr.contDiff _
  have hb0 : 0 ≤ B₀ * remWt u.2 := mul_nonneg hB₀0 (remWt_nonneg _)
  have h1 := norm_iteratedFDeriv_le_of_words hg i u hb0 fun r' => by
    rw [← lineIter_append]
    have := hC ⟨⟨i, Nat.lt_succ_of_le hi⟩, r'⟩ u hu
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (remWt_nonneg _))
    exact Finset.single_le_sum (f := C) (fun p _ => hC0 p) (Finset.mem_univ _)
  refine h1.trans ?_
  have : (4 : ℝ) ^ i ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hi
  calc (4 : ℝ) ^ i * (B₀ * remWt u.2) ≤ 4 ^ n * (B₀ * remWt u.2) :=
        mul_le_mul_of_nonneg_right this hb0
    _ = _ := by ring

theorem isRemKernel_lineIter (hr : RemKernel r) (k : Fin 4 →₀ ℕ) :
    ∃ B : ℝ, IsRemKernel (lineIter (multiDirs k) r) B := by
  obtain ⟨B, hB0, hB⟩ := hr.exists_remDecay_lineIter k 4 3
  exact ⟨B, ⟨contDiff_lineIter hr.contDiff _, hB0, hB⟩⟩

end RemKernel

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Nonlin
public import RegularityStructures.PDE.MildDeriv
public import RegularityStructures.PDE.SpatialDeriv

/-!
# The jet of a mild solution

If `u` is a continuous mild solution of `∂_t u = Δu + G(t, x, u)` with a `C¹` nonlinearity and
`C¹` initial datum, then `u(t)` has continuous partial derivatives `w(t)`, and the pair `(u, w)` is
a mild solution of the jet system `∂_t J = ΔJ + jetNonlin G (t, x, J)` with initial datum
`(u₀, Du₀)` (`exists_jet_of_isMildSolution`). Iterating gives all higher spatial derivatives.
-/

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Calculus rules for `HasTorusDeriv` -/

theorem HasTorusDeriv.add {g h : C(Torus3, E)} {Dg Dh : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) (hh : HasTorusDeriv h Dh) : HasTorusDeriv (g + h) (Dg + Dh) := by
  intro y
  simpa [map_add] using (hg y).fun_add (hh y)

theorem HasTorusDeriv.neg {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) : HasTorusDeriv (-g) (-Dg) := by
  intro y
  simpa [map_neg] using (hg y).fun_neg

/-- Postcomposition with a continuous linear map commutes with taking partial derivatives. -/
theorem HasTorusDeriv.compLeft {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) (L : E →L[ℝ] F) :
    HasTorusDeriv (L.compLeftContinuous ℝ Torus3 g)
      ((ContinuousLinearMap.pi fun i => L.comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => E) i)).compLeftContinuous
          ℝ Torus3 Dg) := by
  intro y
  have heq : ofPartials (((ContinuousLinearMap.pi fun i => L.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => E) i)).compLeftContinuous
        ℝ Torus3 Dg) (torusProj y)) = L.comp (ofPartials (Dg (torusProj y))) := by
    refine ContinuousLinearMap.ext fun k => ?_
    rw [ContinuousLinearMap.comp_apply, ofPartials_apply, ofPartials_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [heq]
  exact L.hasFDerivAt.comp y (hg y)

/-- Partial derivatives are unique. -/
theorem HasTorusDeriv.unique {g : C(Torus3, E)} {Dg Dg' : C(Torus3, Fin 3 → E)}
    (h : HasTorusDeriv g Dg) (h' : HasTorusDeriv g Dg') : Dg = Dg' := by
  ext x i
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  have := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] E => L (Pi.single i 1)) ((h y).unique (h' y))
  simpa [ofPartials_single] using this

/-! ### Componentwise heat operator and Duhamel integral -/

variable [CompleteSpace E] [CompleteSpace F]

theorem heatOp_prodMk (t : ℝ) (a : C(Torus3, E)) (b : C(Torus3, F)) :
    heatOp t (a.prodMk b) = (heatOp t a).prodMk (heatOp t b) := by
  have h1 := heatOp_compLeftContinuous t (ContinuousLinearMap.fst ℝ E F) (a.prodMk b)
  have h2 := heatOp_compLeftContinuous t (ContinuousLinearMap.snd ℝ E F) (a.prodMk b)
  have ha : (ContinuousLinearMap.fst ℝ E F).compLeftContinuous ℝ Torus3 (a.prodMk b) = a := by
    ext x; rfl
  have hb : (ContinuousLinearMap.snd ℝ E F).compLeftContinuous ℝ Torus3 (a.prodMk b) = b := by
    ext x; rfl
  rw [ha] at h1
  rw [hb] at h2
  ext x
  · exact (congrArg (fun f : C(Torus3, E) => f x) h1).symm
  · exact (congrArg (fun f : C(Torus3, F) => f x) h2).symm

theorem duhamel_prodMk {h₁ : ℝ → C(Torus3, E)} {h₂ : ℝ → C(Torus3, F)} (hh₁ : Continuous h₁)
    (hh₂ : Continuous h₂) (t : ℝ) :
    duhamel (fun s => (h₁ s).prodMk (h₂ s)) t = (duhamel h₁ t).prodMk (duhamel h₂ t) := by
  have hc : Continuous fun s => (h₁ s).prodMk (h₂ s) := by
    have h1 : Continuous fun q : ℝ × Torus3 => h₁ q.1 q.2 :=
      continuous_eval.comp ((hh₁.comp continuous_fst).prodMk continuous_snd)
    have h2 : Continuous fun q : ℝ × Torus3 => h₂ q.1 q.2 :=
      continuous_eval.comp ((hh₂.comp continuous_fst).prodMk continuous_snd)
    exact (ContinuousMap.curry ⟨fun q : ℝ × Torus3 => (h₁ q.1 q.2, h₂ q.1 q.2),
      h1.prodMk h2⟩).continuous
  have h1 := duhamel_compLeftContinuous hc (ContinuousLinearMap.fst ℝ E F) t
  have h2 := duhamel_compLeftContinuous hc (ContinuousLinearMap.snd ℝ E F) t
  have ha : (fun s => (ContinuousLinearMap.fst ℝ E F).compLeftContinuous ℝ Torus3
      ((h₁ s).prodMk (h₂ s))) = h₁ := by
    funext s; ext x; rfl
  have hb : (fun s => (ContinuousLinearMap.snd ℝ E F).compLeftContinuous ℝ Torus3
      ((h₁ s).prodMk (h₂ s))) = h₂ := by
    funext s; ext x; rfl
  rw [ha] at h1
  rw [hb] at h2
  ext x
  · exact (congrArg (fun f : C(Torus3, E) => f x) h1).symm
  · exact (congrArg (fun f : C(Torus3, F) => f x) h2).symm

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] in
theorem prodMk_add_prodMk (a c : C(Torus3, E)) (b d : C(Torus3, F)) :
    a.prodMk b + c.prodMk d = (a + c).prodMk (b + d) := by
  ext x <;> rfl

/-- **The jet of a mild solution.** If `G` is `C¹`, `u₀` has partial derivatives `Du₀`, and `u` is
a continuous mild solution on `[0, T]`, then `u(t)` has continuous partial derivatives `w(t)` and
`(u, w)` is a mild solution of the jet system with initial datum `(u₀, Du₀)`. -/
theorem exists_jet_of_isMildSolution [FiniteDimensional ℝ E] {G : C(ℝ × Torus3 × E, E)}
    (hG : ContDiff ℝ 1 (nonlinLift G)) {u₀ : C(Torus3, E)} {Du₀ : C(Torus3, Fin 3 → E)}
    (hu₀ : HasTorusDeriv u₀ Du₀) {T : ℝ} (hT : 0 ≤ T) {u : ℝ → C(Torus3, E)}
    (hu : Continuous u) (hmild : IsMildSolution G u₀ T u) :
    ∃ w : ℝ → C(Torus3, Fin 3 → E), Continuous w ∧ (∀ t ∈ Icc 0 T, HasTorusDeriv (u t) (w t)) ∧
      (∀ t ∈ Icc 0 T, w t = heatOp t Du₀ +
        duhamel (fun s => nemytskiiDeriv G hG s (u s) (w s)) t) ∧
      IsMildSolution (E := E × (Fin 3 → E)) (jetNonlin G hG) (u₀.prodMk Du₀) T
        (fun t => (u t).prodMk (w t)) := by
  obtain ⟨w, hw, hmw, hd⟩ := exists_hasTorusDeriv_of_isMildSolution (DG := nonlinDeriv G hG)
    (hasFDerivAt_nonlinLift hG) hu₀ hT hu hmild
  refine ⟨w, hw, hd, fun t ht => hmw t ht, fun t ht => ?_⟩
  have hNu := continuous_nemytskii_comp G hu
  have hNw := continuous_nemytskii_comp (E := Fin 3 → E)
    (linearisedNonlin (nonlinDeriv G hG) u hu) hw
  have hsplit : (fun s => nemytskii (E := E × (Fin 3 → E)) (jetNonlin G hG) s
      ((u s).prodMk (w s))) = fun s => (nemytskii G s (u s)).prodMk
        (nemytskii (E := Fin 3 → E) (linearisedNonlin (nonlinDeriv G hG) u hu) s (w s)) := by
    funext s
    ext x <;> rfl
  rw [hsplit, duhamel_prodMk hNu hNw, heatOp_prodMk, prodMk_add_prodMk, ← hmild t ht,
    ← hmw t ht]

end RegularityStructures.PDE

end

module

public import GlobalPhi43.MW20.CubicComparison

/-!
# The terminal-time face in MW20 Lemma 2.7

The equation is only used at times strictly below one. Continuity extends the
barrier comparison to the terminal face; no new PDE assumption is imposed there.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set Filter Topology

/-- Positive-part comparison throughout the source cylinder and its terminal
face, from a forcing inequality on the open cylinder alone. -/
theorem le_cubicBarrier_through_terminal {u : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u)
    {G : ℝ} (hG : 0 ≤ G)
    (hpde : ∀ z ∈ sourceCylinder 0, sourceHeat u z + u z ^ 3 ≤ G ^ 3)
    (z : ParabolicSpace) {ρ : ℝ} (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ z.1) (ht1 : z.1 ≤ 1)
    (hx : ∀ i, ρ ≤ 1 - z.2 i ∧ ρ ≤ 1 + z.2 i) : u z ≤ cubicBarrier G z := by
  rcases lt_or_eq_of_le ht1 with hlt | heq
  · exact le_cubicBarrier_of_source_cubic hu hG hpde z hρ ht hlt hx
  · rcases z with ⟨t, x⟩
    change t = 1 at heq
    subst t
    let σ := min ρ (1 / 2 : ℝ)
    have hσ : 0 < σ := lt_min hρ (by norm_num)
    have hσρ : σ ≤ ρ := min_le_left _ _
    have hσ2 : σ ^ 2 < 1 := by
      have hs : σ ≤ 1 / 2 := min_le_right _ _
      nlinarith
    have hspace (i : Fin 3) : -1 < x i ∧ x i < 1 := by
      constructor <;> linarith [(hx i).1, (hx i).2]
    have hpath : ContinuousAt (fun t : ℝ => (t, x)) 1 := by fun_prop
    have hc : ContinuousAt (fun t : ℝ => u (t, x) - cubicBarrier G (t, x)) 1 :=
      ((hu.twice (1, x) (by norm_num) le_rfl hspace).continuousAt.comp (f := fun s : ℝ => (s, x)) hpath).sub
        ((cubicBarrier_contDiffAt G (1, x) (by norm_num) hspace).continuousAt.comp (f := fun s : ℝ => (s, x)) hpath)
    have hlim : Tendsto (fun s : ℝ => u (s, x) - cubicBarrier G (s, x))
        (𝓝[<] (1 : ℝ)) (𝓝 (u (1, x) - cubicBarrier G (1, x))) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    apply sub_nonpos.mp
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hσ2] with s hs
    exact sub_nonpos.mpr (le_cubicBarrier_of_source_cubic hu hG hpde (s, x)
      hσ hs.1.le hs.2 (fun i => ⟨hσρ.trans (hx i).1, hσρ.trans (hx i).2⟩))

/-- The positive-part estimate has a universal constant, with no dependence
on boundary values or the size of derivatives of the forcing. -/
theorem source_cubic_upper_bound {u : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u)
    {G : ℝ} (hG : 0 ≤ G)
    (hpde : ∀ z ∈ sourceCylinder 0, sourceHeat u z + u z ^ 3 ≤ G ^ 3)
    (z : ParabolicSpace) {ρ : ℝ} (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ z.1) (ht1 : z.1 ≤ 1)
    (hx : ∀ i, ρ ≤ 1 - z.2 i ∧ ρ ≤ 1 + z.2 i) :
    u z ≤ 15 * max (1 / ρ) G :=
  (le_cubicBarrier_through_terminal hu hG hpde z hρ ht ht1 hx).trans
    (cubicBarrier_le_boundary G z hρ ht hx)

end GlobalPhi43.MW20

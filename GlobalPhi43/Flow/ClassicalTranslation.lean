module

public import GlobalPhi43.Flow.SmoothSolutions

/-! Classical translation and restart for the existing chosen smooth solution.
External forcing shifts are arbitrary real numbers; relative restart times are
nonnegative. These deterministic identities introduce no exceptional event. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Every classical solution with the same data agrees with the chosen path,
including time zero. No second choice of a solution is made. -/
theorem smoothSolution_eq_classical (b : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution b f x u)
    {r : ℝ} (hr : 0 ≤ r) : smoothSolution b f hf x hx r = u r :=
  classicalSolution_unique b (smoothSolution_spec b f hf x hx) hu r hr

/-- The chosen path depends on the forcing, not on its smoothness witness. -/
theorem smoothSolution_congr_forcing (b : ℝ) {f g : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : IsSmoothOnSpaceTime g) (hfg : f = g)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) (r : ℝ) :
    smoothSolution b f hf x hx r = smoothSolution b g hg x hx r := by
  subst g
  rfl

theorem shiftForcing_add (s q : ℝ) (f : SpaceTime → ℝ) :
    shiftForcing q (shiftForcing s f) = shiftForcing (s + q) f := by
  funext p
  simp only [shiftForcing]
  congr 1
  ext
  · ring
  · rfl

/-- Smoothness of every nonnegative-time state of the chosen classical path.
The zero endpoint uses the original smooth datum, not positive-time smoothing. -/
theorem smoothSolution_smooth_state (b : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    {q : ℝ} (hq : 0 ≤ q) : IsSmoothOnTorus (smoothSolution b f hf x hx q) := by
  rcases eq_or_lt_of_le hq with hq | hq
  · subst q
    rw [(smoothSolution_spec b f hf x hx).initial]
    exact hx
  · exact isSmoothOnTorus_of_classical (smoothSolution_spec b f hf x hx) hq

/-- Restart of the chosen classical path at every nonnegative relative time,
with no restriction on the subsequent nonnegative relative horizon. -/
theorem smoothSolution_restart (b : ℝ) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) :
    smoothSolution b (shiftForcing q f) (isSmoothOnSpaceTime_shiftForcing hf q)
      (smoothSolution b f hf x hx q) (smoothSolution_smooth_state b f hf x hx hq) r =
      smoothSolution b f hf x hx (q + r) :=
  smoothSolution_eq_classical b _ _ _ _
    (isClassicalSolution_shift (smoothSolution_spec b f hf x hx) hq) hr

end GlobalPhi43.Flow

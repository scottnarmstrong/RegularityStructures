/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Realising

/-!+# The causal realising identity on the noise

Hairer [Hai14, Definition 5.9, Proposition 8.27]: the first integrated
symbol is the actual convolution of the smooth noise. The shell-pairing
definition of the abstract germ agrees with that convolution.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

end RegularityStructures.Phi43

end

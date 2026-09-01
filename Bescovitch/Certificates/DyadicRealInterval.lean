/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.FixedDyadicInterval

/-!
# Real semantics of dyadic intervals

This module states real-number membership for exact and guarded fixed-width dyadic intervals.
-/

@[expose] public section

namespace Bescovitch

namespace DyadicInterval

variable {precision : ℕ}

/-- Real membership in the ordinary interval represented by a dyadic interval. -/
def ContainsReal (interval : DyadicInterval precision) (value : ℝ) : Prop :=
  interval.interpret.Contains value

end DyadicInterval

namespace FixedDyadicInterval

variable {width precision : ℕ}

/-- A guarded interval contains a real number when its represented dyadic interval does. -/
def ContainsReal (interval : FixedDyadicInterval width precision) (value : ℝ) : Prop :=
  ∃ exact : DyadicInterval precision,
    interval.Represents exact ∧ exact.ContainsReal value

end FixedDyadicInterval

end Bescovitch

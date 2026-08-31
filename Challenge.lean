/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Statement

/-!
# Challenge: the planar Besicovitch threshold

The comparator checks this statement and every transparent definition in its type.
-/

@[expose] public section

namespace Bescovitch

/-- The planar one-dimensional rectifiability threshold is at most the six-point endpoint. -/
theorem sigma_one_plane_le_s_star : sigmaOne Plane ≤ sStar := by
  sorry

end Bescovitch

/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Connected components in compact spaces

A connected component in a compact Hausdorff space has arbitrarily small clopen
neighborhoods. This is the compact-space separation fact used in the BPC argument.
-/

@[expose] public section

open Set

namespace Bescovitch

/-- In a compact Hausdorff space, a connected component contained in an open set has a clopen
neighborhood contained in that open set. -/
theorem exists_isClopen_between_connectedComponent {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
    (hcomponent : connectedComponent x ⊆ U) :
    ∃ H : Set X, IsClopen H ∧ connectedComponent x ⊆ H ∧ H ⊆ U := by
  rw [connectedComponent_eq_iInter_isClopen] at hcomponent
  have hfinite := hU.isClosed_compl.isCompact.inter_iInter_nonempty
    (fun s : {s : Set X // IsClopen s ∧ x ∈ s} ↦ s) fun s ↦ s.2.1.1
  rw [← not_disjoint_iff_nonempty_inter, imp_not_comm, not_forall] at hfinite
  obtain ⟨sets, hsets⟩ :=
    hfinite (disjoint_compl_left_iff_subset.2 hcomponent)
  refine ⟨⋂ s ∈ sets, Subtype.val s, ?_, ?_, ?_⟩
  · exact isClopen_biInter_finset fun s _ ↦ s.2.1
  · rw [connectedComponent_eq_iInter_isClopen]
    intro y hy
    exact mem_iInter₂.2 fun s _ ↦ mem_iInter.1 hy s
  · rwa [← disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty,
      ← not_nonempty_iff_eq_empty]

end Bescovitch

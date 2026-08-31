/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.BPC.Defs

/-!
# Basic facts about the Besicovitch pair condition

This file develops the elementary set-distance API needed by the six-point transfer.
-/

@[expose] public section

noncomputable section

open Set
open scoped ENNReal

namespace Bescovitch

variable {X : Type*} [PseudoEMetricSpace X] {s t : Set X}

/-- The set distance is bounded by the distance between any selected pair of points. -/
theorem setEDist_le_edist_of_mem {x y : X} (hx : x ∈ s) (hy : y ∈ t) :
    setEDist s t ≤ edist x y := by
  exact iInf_le_of_le x <| iInf_le_of_le hx <| iInf_le_of_le y <| iInf_le_of_le hy le_rfl

/-- Extended set distance is symmetric. -/
theorem setEDist_comm (s t : Set X) : setEDist s t = setEDist t s := by
  apply le_antisymm
  · refine le_iInf fun y ↦ le_iInf fun hy ↦ le_iInf fun x ↦ le_iInf fun hx ↦ ?_
    simpa [edist_comm] using setEDist_le_edist_of_mem (s := s) (t := t) hx hy
  · refine le_iInf fun x ↦ le_iInf fun hx ↦ le_iInf fun y ↦ le_iInf fun hy ↦ ?_
    simpa [edist_comm] using setEDist_le_edist_of_mem (s := t) (t := s) hy hx

@[simp]
theorem setEDist_empty_left (t : Set X) : setEDist ∅ t = ∞ := by
  simp [setEDist]

@[simp]
theorem setEDist_empty_right (s : Set X) : setEDist s ∅ = ∞ := by
  rw [setEDist_comm, setEDist_empty_left]

/-- Two nonempty sets in a metric space have finite extended distance. -/
theorem setEDist_ne_top {Y : Type*} [PseudoMetricSpace Y] {u v : Set Y}
    (hu : u.Nonempty) (hv : v.Nonempty) : setEDist u v ≠ ∞ := by
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hv
  exact ne_top_of_le_ne_top (edist_ne_top x y) (setEDist_le_edist_of_mem hx hy)

/-- A strict upper bound on set distance is witnessed by an actual pair of points. -/
theorem exists_edist_lt_of_setEDist_lt {r : ℝ≥0∞} (h : setEDist s t < r) :
    ∃ x ∈ s, ∃ y ∈ t, edist x y < r := by
  rw [setEDist, iInf_lt_iff] at h
  obtain ⟨x, hx⟩ := h
  rw [iInf_lt_iff] at hx
  obtain ⟨hxs, hx⟩ := hx
  rw [iInf_lt_iff] at hx
  obtain ⟨y, hy⟩ := hx
  rw [iInf_lt_iff] at hy
  obtain ⟨hyt, hy⟩ := hy
  exact ⟨x, hxs, y, hyt, hy⟩

end Bescovitch

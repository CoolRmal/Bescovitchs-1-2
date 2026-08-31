/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.List.Basic

/-!
# Checked materialization of straight-line expressions

Checkpoints replace expensive subexpressions by supplied values after checking equality. The
expression remains fixed in Lean, while generated certificate data supplies only checkpoint values.
-/

@[expose] public section

namespace Bescovitch

/-- A fixed straight-line expression with explicit materialization checkpoints. -/
inductive MaterializedExpr (α : Type*) where
  | input (value : α)
  | unary (operation : α → α) (argument : MaterializedExpr α)
  | binary (operation : α → α → α) (left right : MaterializedExpr α)
  | letIn (value : MaterializedExpr α) (body : α → MaterializedExpr α)
  | checkpoint (argument : MaterializedExpr α)

namespace MaterializedExpr

variable {α : Type*}

/-- The mathematical value of a materialized expression, ignoring checkpoint data. -/
def eval : MaterializedExpr α → α
  | .input value => value
  | .unary operation argument => operation argument.eval
  | .binary operation left right => operation left.eval right.eval
  | .letIn value body => (body value.eval).eval
  | .checkpoint argument => argument.eval

/-- Evaluate an expression while checking and consuming its checkpoint values. -/
def run (equal : α → α → Bool) :
    MaterializedExpr α → List α → Option (α × List α)
  | .input value, data => some (value, data)
  | .unary operation argument, data => do
      let (value, rest) ← argument.run equal data
      pure (operation value, rest)
  | .binary operation left right, data => do
      let (leftValue, afterLeft) ← left.run equal data
      let (rightValue, rest) ← right.run equal afterLeft
      pure (operation leftValue rightValue, rest)
  | .letIn value body, data => do
      let (computed, rest) ← value.run equal data
      (body computed).run equal rest
  | .checkpoint argument, data => do
      let (value, afterArgument) ← argument.run equal data
      let claimed :: rest := afterArgument | none
      if equal claimed value then pure (claimed, rest) else none

/-- A successful run returns the ordinary mathematical value. -/
theorem run_eq_eval {equal : α → α → Bool}
    (equal_sound : ∀ {left right}, equal left right = true → left = right)
    {expression : MaterializedExpr α} {data rest : List α} {value : α}
    (h : expression.run equal data = some (value, rest)) : value = expression.eval := by
  induction expression generalizing data rest value with
  | input input =>
      simp [run] at h
      exact h.1.symm
  | unary operation argument ih =>
      rw [run] at h
      cases hargument : argument.run equal data with
      | none => simp [hargument] at h
      | some result =>
          rcases result with ⟨argumentValue, afterArgument⟩
          rw [hargument] at h
          simp at h
          exact h.1.symm.trans (congrArg operation (ih hargument))
  | binary operation left right leftIH rightIH =>
      rw [run] at h
      cases hleft : left.run equal data with
      | none => simp [hleft] at h
      | some leftResult =>
          rcases leftResult with ⟨leftValue, afterLeft⟩
          cases hright : right.run equal afterLeft with
          | none => simp [hleft, hright] at h
          | some rightResult =>
              rcases rightResult with ⟨rightValue, afterRight⟩
              rw [hleft] at h
              simp [hright] at h
              exact h.1.symm.trans (congrArg₂ operation (leftIH hleft) (rightIH hright))
  | letIn bound body boundIH bodyIH =>
      rw [run] at h
      cases hbound : bound.run equal data with
      | none => simp [hbound] at h
      | some boundResult =>
          rcases boundResult with ⟨boundValue, afterBound⟩
          rw [hbound] at h
          simpa only [eval, boundIH hbound] using bodyIH boundValue h
  | checkpoint argument ih =>
      rw [run] at h
      cases hargument : argument.run equal data with
      | none => simp [hargument] at h
      | some result =>
          rcases result with ⟨argumentValue, afterArgument⟩
          cases afterArgument with
          | nil => simp [hargument] at h
          | cons claimed afterCheckpoint =>
              rw [hargument] at h
              by_cases hclaimed : equal claimed argumentValue = true
              · simp [hclaimed] at h
                exact h.1.symm.trans (equal_sound hclaimed |>.trans (ih hargument))
              · simp [hclaimed] at h

/-- Check all checkpoint values and require the materialization stream to be exhausted. -/
def check (equal : α → α → Bool) (expression : MaterializedExpr α) (data : List α) : Bool :=
  match expression.run equal data with
  | some (_, []) => true
  | _ => false

/-- A successful complete check produces the mathematical value of the fixed expression. -/
theorem check_sound {equal : α → α → Bool}
    (equal_sound : ∀ {left right}, equal left right = true → left = right)
    {expression : MaterializedExpr α} {data : List α}
    (h : expression.check equal data = true) :
    expression.run equal data = some (expression.eval, []) := by
  rw [check] at h
  cases heq : expression.run equal data with
  | none => simp [heq] at h
  | some result =>
      rcases result with ⟨value, rest⟩
      cases rest with
      | nil =>
          have hvalue := run_eq_eval equal_sound heq
          subst value
          rfl
      | cons head tail => simp [heq] at h

/-- Extract the value returned by a complete materialized run. -/
def checkedValue (equal : α → α → Bool)
    (expression : MaterializedExpr α) (data : List α) : Option α :=
  match expression.run equal data with
  | some (value, []) => some value
  | _ => none

/-- The value returned by a successful complete run is the mathematical value. -/
theorem checkedValue_eq_eval {equal : α → α → Bool}
    (equal_sound : ∀ {left right}, equal left right = true → left = right)
    {expression : MaterializedExpr α} {data : List α}
    (h : expression.check equal data = true) :
    expression.checkedValue equal data = some expression.eval := by
  rw [checkedValue, check_sound equal_sound h]

end MaterializedExpr

end Bescovitch

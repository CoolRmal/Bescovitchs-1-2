/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.List.Basic

/-!
# Materialization modulo an equivalence relation

Typed local variables permit reuse of checked intermediate values. A checkpoint may replace its
computed value by any equivalent supplied value, which supports canonicalized certificate data.
-/

@[expose] public section

namespace Bescovitch

universe u

/-- A fixed expression with typed local variables and equivalence-checked materializations. -/
inductive RelMaterializedExpr (α : Type u) [Setoid α] : ℕ → Type u where
  | input {n : ℕ} (value : α) : RelMaterializedExpr α n
  | var {n : ℕ} (index : Fin n) : RelMaterializedExpr α n
  | unary {n : ℕ} (operation : α → α)
      (proper : ∀ ⦃left right : α⦄, left ≈ right → operation left ≈ operation right)
      (argument : RelMaterializedExpr α n) : RelMaterializedExpr α n
  | binary {n : ℕ} (operation : α → α → α)
      (proper : ∀ ⦃left left' right right' : α⦄,
        left ≈ left' → right ≈ right' → operation left right ≈ operation left' right')
      (left right : RelMaterializedExpr α n) : RelMaterializedExpr α n
  | letIn {n : ℕ} (value : RelMaterializedExpr α n)
      (body : RelMaterializedExpr α (n + 1)) : RelMaterializedExpr α n
  | checkpoint {n : ℕ} (argument : RelMaterializedExpr α n) : RelMaterializedExpr α n

namespace RelMaterializedExpr

variable {α : Type*} [Setoid α]

/-- Evaluate an expression without consulting materialization data. -/
def eval : {n : ℕ} → RelMaterializedExpr α n → (Fin n → α) → α
  | _, .input value, _ => value
  | _, .var index, environment => environment index
  | _, .unary operation _ argument, environment => operation (argument.eval environment)
  | _, .binary operation _ left right, environment =>
      operation (left.eval environment) (right.eval environment)
  | _, .letIn value body, environment =>
      body.eval (Fin.cases (value.eval environment) environment)
  | _, .checkpoint argument, environment => argument.eval environment

/-- Evaluate an expression while checking and consuming supplied materializations. -/
def run (equal : α → α → Bool) : {n : ℕ} →
    RelMaterializedExpr α n → (Fin n → α) → List α → Option (α × List α)
  | _, .input value, _, data => some (value, data)
  | _, .var index, environment, data => some (environment index, data)
  | _, .unary operation _ argument, environment, data => do
      let (value, rest) ← argument.run equal environment data
      pure (operation value, rest)
  | _, .binary operation _ left right, environment, data => do
      let (leftValue, afterLeft) ← left.run equal environment data
      let (rightValue, rest) ← right.run equal environment afterLeft
      pure (operation leftValue rightValue, rest)
  | _, .letIn value body, environment, data => do
      let (computed, rest) ← value.run equal environment data
      body.run equal (Fin.cases computed environment) rest
  | _, .checkpoint argument, environment, data => do
      let (computed, afterArgument) ← argument.run equal environment data
      let claimed :: rest := afterArgument | none
      if equal claimed computed then pure (claimed, rest) else none

/-- A successful run is equivalent to ordinary evaluation in any equivalent environment. -/
theorem run_rel_eval {equal : α → α → Bool}
    (equal_sound : ∀ {left right}, equal left right = true → left ≈ right)
    {n : ℕ} {expression : RelMaterializedExpr α n}
    {runEnvironment evalEnvironment : Fin n → α}
    (henvironment : ∀ i, runEnvironment i ≈ evalEnvironment i)
    {data rest : List α} {value : α}
    (h : expression.run equal runEnvironment data = some (value, rest)) :
    value ≈ expression.eval evalEnvironment := by
  induction expression generalizing data rest value with
  | input input =>
      simp [run] at h
      rw [← h.1]
      exact Setoid.refl input
  | var index =>
      simp [run] at h
      rw [← h.1]
      exact henvironment index
  | unary operation proper argument ih =>
      rw [run] at h
      cases hargument : argument.run equal runEnvironment data with
      | none => simp [hargument] at h
      | some result =>
          rcases result with ⟨argumentValue, afterArgument⟩
          rw [hargument] at h
          simp at h
          rw [← h.1]
          exact proper (ih henvironment hargument)
  | binary operation proper left right leftIH rightIH =>
      rw [run] at h
      cases hleft : left.run equal runEnvironment data with
      | none => simp [hleft] at h
      | some leftResult =>
          rcases leftResult with ⟨leftValue, afterLeft⟩
          cases hright : right.run equal runEnvironment afterLeft with
          | none => simp [hleft, hright] at h
          | some rightResult =>
              rcases rightResult with ⟨rightValue, afterRight⟩
              rw [hleft] at h
              simp [hright] at h
              rw [← h.1]
              exact proper (leftIH henvironment hleft) (rightIH henvironment hright)
  | letIn bound body boundIH bodyIH =>
      rw [run] at h
      cases hbound : bound.run equal runEnvironment data with
      | none => simp [hbound] at h
      | some boundResult =>
          rcases boundResult with ⟨boundValue, afterBound⟩
          rw [hbound] at h
          apply bodyIH _ h
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact boundIH henvironment hbound
          · exact henvironment j
  | checkpoint argument ih =>
      rw [run] at h
      cases hargument : argument.run equal runEnvironment data with
      | none => simp [hargument] at h
      | some result =>
          rcases result with ⟨computed, afterArgument⟩
          cases afterArgument with
          | nil => simp [hargument] at h
          | cons claimed afterCheckpoint =>
              rw [hargument] at h
              by_cases hclaimed : equal claimed computed = true
              · simp [hclaimed] at h
                rw [← h.1]
                exact Setoid.trans (equal_sound hclaimed) (ih henvironment hargument)
              · simp [hclaimed] at h

/-- The unique environment for a closed expression. -/
def emptyEnvironment : Fin 0 → α := Fin.elim0

/-- Check all checkpoints of a closed expression and require the data stream to be exhausted. -/
def check (equal : α → α → Bool) (expression : RelMaterializedExpr α 0)
    (data : List α) : Bool :=
  match expression.run equal emptyEnvironment data with
  | some (_, []) => true
  | _ => false

/-- A successful closed check returns a value equivalent to the fixed expression. -/
theorem check_sound {equal : α → α → Bool}
    (equal_sound : ∀ {left right}, equal left right = true → left ≈ right)
    {expression : RelMaterializedExpr α 0} {data : List α}
    (h : expression.check equal data = true) :
    ∃ value, expression.run equal emptyEnvironment data = some (value, []) ∧
      value ≈ expression.eval emptyEnvironment := by
  rw [check] at h
  cases heq : expression.run equal emptyEnvironment data with
  | none => simp [heq] at h
  | some result =>
      rcases result with ⟨value, rest⟩
      cases rest with
      | nil =>
          refine ⟨value, ?_, run_rel_eval equal_sound (fun i => Fin.elim0 i) heq⟩
          rfl
      | cons head tail => simp [heq] at h

end RelMaterializedExpr

end Bescovitch

/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.IntegerInterval

/-!
# Linked unbounded-integer scalar traces

A certificate stores every endpoint once in a binary register tree.  Each instruction contains
only rational constants and register indices; the checker reads its operands and claimed output
from that same tree.  Successful checks therefore reject missing or forward references while
certifying the corresponding exact rational arithmetic.
-/

@[expose] public section

namespace Bescovitch.IntegerScalarTrace

variable {precision : ℕ}

/-- A binary register file whose type records its number of leaves. -/
inductive RegisterTree : ℕ → Type
  | leaf (value : IntegerInterval) : RegisterTree 1
  | node {leftSize rightSize : ℕ} (left : RegisterTree leftSize)
      (right : RegisterTree rightSize) : RegisterTree (leftSize + rightSize)

namespace RegisterTree

/-- List the endpoint values in register order. -/
def toList : {size : ℕ} → RegisterTree size → List IntegerInterval
  | _, .leaf value => [value]
  | _, .node left right => left.toList ++ right.toList

/-- The type index is exactly the number of ordered leaves. -/
@[simp] theorem toList_length {size : ℕ} (tree : RegisterTree size) :
    tree.toList.length = size := by
  induction tree with
  | leaf => rfl
  | node left right leftInduction rightInduction =>
      simp only [toList, List.length_append, leftInduction, rightInduction]

/-- Read a register by following one branch at each node. -/
def get? : {size : ℕ} → RegisterTree size → ℕ → Option IntegerInterval
  | _, .leaf value, 0 => some value
  | _, .leaf _, _ + 1 => none
  | _, .node (leftSize := leftSize) left right, register =>
      if register < leftSize then left.get? register
      else right.get? (register - leftSize)

/-- Tree lookup agrees extensionally with lookup in the ordered leaf list. -/
theorem get?_eq_toList_getElem? {size : ℕ} (tree : RegisterTree size) (register : ℕ) :
    tree.get? register = tree.toList[register]? := by
  induction tree generalizing register with
  | leaf value => cases register <;> rfl
  | @node leftSize rightSize left right leftInduction rightInduction =>
      simp only [get?, toList]
      by_cases hregister : register < leftSize
      · rw [if_pos hregister, leftInduction]
        symm
        apply List.getElem?_append_left
        simpa using hregister
      · rw [if_neg hregister, rightInduction]
        symm
        calc
          (left.toList ++ right.toList)[register]? =
              right.toList[register - left.toList.length]? :=
            List.getElem?_append_right (by
              simpa using Nat.le_of_not_gt hregister)
          _ = right.toList[register - leftSize]? := by
            rw [toList_length]

end RegisterTree

/-- A scalar instruction containing no cached endpoints; its output is the current cursor. -/
inductive Equation where
  | ofRat (value : ℚ)
  | add (left right : ℕ)
  | neg (value : ℕ)
  | mul (left right : ℕ)

namespace Equation

/-- Every operand of an instruction precedes its output. -/
def ValidAt (cursor : ℕ) : Equation → Prop
  | .ofRat _ => True
  | .add left right => left < cursor ∧ right < cursor
  | .neg value => value < cursor
  | .mul left right => left < cursor ∧ right < cursor

/-- Instruction validity is decidable from its operand indices. -/
instance instDecidableValidAt (cursor : ℕ) (equation : Equation) :
    Decidable (equation.ValidAt cursor) := by
  cases equation <;> simp only [ValidAt] <;> infer_instance

/-- Exact rational value produced by an instruction. -/
def exactValue (exact : ℕ → ℚ) : Equation → ℚ
  | .ofRat value => value
  | .add left right => exact left + exact right
  | .neg value => -exact value
  | .mul left right => exact left * exact right

/-- Evaluate one instruction from the common endpoint register file. -/
def eval? {size : ℕ} (registers : RegisterTree size) (precision : ℕ) :
    Equation → Option IntegerInterval
  | .ofRat value => some (IntegerInterval.ofRat precision value)
  | .add left right => return (← registers.get? left).add (← registers.get? right)
  | .neg value => return (← registers.get? value).neg
  | .mul left right =>
      return (← registers.get? left).mul precision (← registers.get? right)

/-- Check one well-founded instruction against its output in the same register file. -/
def checkAt {size : ℕ} (registers : RegisterTree size) (precision cursor : ℕ)
    (equation : Equation) : Bool :=
  decide (equation.ValidAt cursor) &&
    match equation.eval? registers precision, registers.get? cursor with
    | some computed, some claimed => computed == claimed
    | _, _ => false

/-- A successful instruction check exposes its validity and its common computed output. -/
theorem checked_data {size : ℕ} {registers : RegisterTree size}
    {precision cursor : ℕ} {equation : Equation}
    (hcheck : equation.checkAt registers precision cursor = true) :
    equation.ValidAt cursor ∧
      ∃ output, equation.eval? registers precision = some output ∧
        registers.get? cursor = some output := by
  simp only [checkAt, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  refine ⟨hcheck.1, ?_⟩
  cases hevaluation : equation.eval? registers precision with
  | none => simp [hevaluation] at hcheck
  | some computed =>
      cases houtput : registers.get? cursor with
      | none => simp [hevaluation, houtput] at hcheck
      | some claimed =>
          simp only [hevaluation, houtput, beq_iff_eq] at hcheck
          exact ⟨claimed, congrArg some hcheck.2, rfl⟩

end Equation

/-- Check a consecutive suffix of compact scalar instructions. -/
def checkEquations {size : ℕ} (registers : RegisterTree size) (precision : ℕ) :
    ℕ → List Equation → Bool
  | _, [] => true
  | cursor, equation :: equations =>
      equation.checkAt registers precision cursor &&
        checkEquations registers precision (cursor + 1) equations

/-- An exact rational register assignment models an instruction suffix. -/
def ExactModelsFrom (cursor : ℕ) : List Equation → (ℕ → ℚ) → Prop
  | [], _ => True
  | equation :: equations, exact =>
      exact cursor = equation.exactValue exact ∧
        ExactModelsFrom (cursor + 1) equations exact

/-- Every instruction in a suffix refers only to preceding registers. -/
def ValidFrom (cursor : ℕ) : List Equation → Prop
  | [] => True
  | equation :: equations =>
      equation.ValidAt cursor ∧ ValidFrom (cursor + 1) equations

private def Equation.evalValid {cursor : ℕ} (initial : Fin cursor → ℚ)
    (equation : Equation) (hvalid : equation.ValidAt cursor) : ℚ :=
  match equation with
  | .ofRat value => value
  | .add left right => initial ⟨left, hvalid.1⟩ + initial ⟨right, hvalid.2⟩
  | .neg value => -initial ⟨value, hvalid⟩
  | .mul left right => initial ⟨left, hvalid.1⟩ * initial ⟨right, hvalid.2⟩

private def extendExact {cursor : ℕ} (initial : Fin cursor → ℚ) (last : ℚ) :
    Fin (cursor + 1) → ℚ :=
  fun register ↦ if h : register < cursor then initial ⟨register, h⟩ else last

private theorem Equation.exactValue_eq_evalValid {cursor : ℕ}
    {exact : ℕ → ℚ} {initial : Fin cursor → ℚ} {equation : Equation}
    (hvalid : equation.ValidAt cursor)
    (hagrees : ∀ register : Fin cursor, exact register = initial register) :
    equation.exactValue exact = equation.evalValid initial hvalid := by
  cases equation with
  | ofRat => rfl
  | add left right =>
      simp only [exactValue, evalValid]
      rw [hagrees ⟨left, hvalid.1⟩, hagrees ⟨right, hvalid.2⟩]
  | neg value =>
      simp only [exactValue, evalValid]
      rw [hagrees ⟨value, hvalid⟩]
  | mul left right =>
      simp only [exactValue, evalValid]
      rw [hagrees ⟨left, hvalid.1⟩, hagrees ⟨right, hvalid.2⟩]

/-- Every well-founded instruction suffix has an exact model extending arbitrary inputs. -/
theorem exactModelsFrom_exists {cursor : ℕ} {equations : List Equation}
    (hvalid : ValidFrom cursor equations) (initial : Fin cursor → ℚ) :
    ∃ exact : ℕ → ℚ,
      (∀ register : Fin cursor, exact register = initial register) ∧
        ExactModelsFrom cursor equations exact := by
  induction equations generalizing cursor with
  | nil =>
      let exact (register : ℕ) : ℚ :=
        if h : register < cursor then initial ⟨register, h⟩ else 0
      refine ⟨exact, ?_, trivial⟩
      intro register
      simp [exact]
  | cons equation equations induction =>
      have hequation : equation.ValidAt cursor := hvalid.1
      let output := equation.evalValid initial hequation
      obtain ⟨exact, hagrees, hmodels⟩ :=
        induction hvalid.2 (extendExact initial output)
      refine ⟨exact, ?_, ?_, hmodels⟩
      · intro register
        simpa [extendExact] using hagrees register.castSucc
      · rw [equation.exactValue_eq_evalValid hequation (by
          intro register
          simpa [extendExact] using hagrees register.castSucc)]
        simpa [extendExact, output] using hagrees (Fin.last cursor)

/-- Every earlier endpoint register contains its exact rational value. -/
def RegistersContainBefore {size : ℕ} (registers : RegisterTree size)
    (precision : ℕ) (exact : ℕ → ℚ) (cursor : ℕ) : Prop :=
  ∀ register, register < cursor →
    ∃ interval, registers.get? register = some interval ∧
      interval.Contains precision (exact register)

private theorem Equation.output_contains {size : ℕ} {registers : RegisterTree size}
    {exact : ℕ → ℚ} {cursor : ℕ} {equation : Equation}
    (hcheck : equation.checkAt registers precision cursor = true)
    (hcontains : RegistersContainBefore registers precision exact cursor) :
    ∃ interval, registers.get? cursor = some interval ∧
      interval.Contains precision (equation.exactValue exact) := by
  obtain ⟨hvalid, output, hevaluation, houtput⟩ := equation.checked_data hcheck
  cases equation with
  | ofRat value =>
      have hequal : IntegerInterval.ofRat precision value = output := by
        simpa [Equation.eval?] using hevaluation
      subst output
      exact ⟨IntegerInterval.ofRat precision value, houtput,
        IntegerInterval.ofRat_contains precision value⟩
  | add left right =>
      obtain ⟨leftInterval, hleftLookup, hleft⟩ := hcontains left hvalid.1
      obtain ⟨rightInterval, hrightLookup, hright⟩ := hcontains right hvalid.2
      have hequal : leftInterval.add rightInterval = output := by
        simpa [Equation.eval?, hleftLookup, hrightLookup] using hevaluation
      subst output
      exact ⟨leftInterval.add rightInterval, houtput,
        IntegerInterval.add_contains hleft hright⟩
  | neg value =>
      obtain ⟨interval, hlookup, hvalue⟩ := hcontains value hvalid
      have hequal : interval.neg = output := by
        simpa [Equation.eval?, hlookup] using hevaluation
      subst output
      exact ⟨interval.neg, houtput, IntegerInterval.neg_contains hvalue⟩
  | mul left right =>
      obtain ⟨leftInterval, hleftLookup, hleft⟩ := hcontains left hvalid.1
      obtain ⟨rightInterval, hrightLookup, hright⟩ := hcontains right hvalid.2
      have hequal : leftInterval.mul precision rightInterval = output := by
        simpa [Equation.eval?, hleftLookup, hrightLookup] using hevaluation
      subst output
      exact ⟨leftInterval.mul precision rightInterval, houtput,
        IntegerInterval.mul_contains hleft hright⟩

/-- A successful compact check verifies well-foundedness of its instruction suffix. -/
theorem validFrom_of_checkEquations {size : ℕ} {registers : RegisterTree size}
    {cursor : ℕ} {equations : List Equation}
    (hcheck : checkEquations registers precision cursor equations = true) :
    ValidFrom cursor equations := by
  induction equations generalizing cursor with
  | nil => trivial
  | cons equation equations induction =>
      simp only [checkEquations, Bool.and_eq_true] at hcheck
      exact ⟨(equation.checked_data hcheck.1).1, induction hcheck.2⟩

/-- Checked compact instructions preserve exact rational containment. -/
theorem checkEquations_sound {size : ℕ} {registers : RegisterTree size}
    {exact : ℕ → ℚ} {cursor : ℕ} {equations : List Equation}
    (hcheck : checkEquations registers precision cursor equations = true)
    (hmodels : ExactModelsFrom cursor equations exact)
    (hcontains : RegistersContainBefore registers precision exact cursor) :
    RegistersContainBefore registers precision exact (cursor + equations.length) := by
  induction equations generalizing cursor with
  | nil => simpa using hcontains
  | cons equation equations induction =>
      simp only [checkEquations, Bool.and_eq_true] at hcheck
      obtain ⟨interval, hlookup, houtput⟩ :=
        equation.output_contains hcheck.1 hcontains
      have hnext : RegistersContainBefore registers precision exact (cursor + 1) := by
        intro register hregister
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hregister) with hlt | rfl
        · exact hcontains register hlt
        · exact ⟨interval, hlookup, hmodels.1.symm ▸ houtput⟩
      have hrest := induction hcheck.2 hmodels.2 hnext
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hrest

/-- A checked compact block extends any exact interpretation of its input registers. -/
theorem checkedBlock_contains_extension {size : ℕ} {registers : RegisterTree size}
    {cursor : ℕ} {equations : List Equation}
    (hcheck : checkEquations registers precision cursor equations = true)
    (initial : Fin cursor → ℚ)
    (hinputs : ∀ register : Fin cursor,
      ∃ interval, registers.get? register = some interval ∧
        interval.Contains precision (initial register)) :
    ∃ exact : ℕ → ℚ,
      (∀ register : Fin cursor, exact register = initial register) ∧
        ExactModelsFrom cursor equations exact ∧
          RegistersContainBefore registers precision exact (cursor + equations.length) := by
  obtain ⟨exact, hagrees, hmodels⟩ :=
    exactModelsFrom_exists (validFrom_of_checkEquations hcheck) initial
  refine ⟨exact, hagrees, hmodels, checkEquations_sound hcheck hmodels ?_⟩
  intro register hregister
  obtain ⟨interval, hlookup, hcontains⟩ := hinputs ⟨register, hregister⟩
  exact ⟨interval, hlookup, by simpa only [hagrees ⟨register, hregister⟩] using hcontains⟩

end Bescovitch.IntegerScalarTrace

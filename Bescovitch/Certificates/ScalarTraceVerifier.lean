/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.FixedDyadicInterval

/-!
# Blockwise scalar traces

A trace block uses guarded signed bit-vector interval arithmetic. It checks only the live outputs
needed by later blocks. The soundness theorem relates every successful fixed computation to the
same unbounded dyadic computation, so overflow cannot certify a false endpoint or sign.
-/

@[expose] public section

namespace Bescovitch.ScalarTraceVerifier

variable {width precision : ℕ}

/-- Proof-free encoding of one fixed-width interval. -/
structure EncodedInterval (width : ℕ) where
  /-- Signed lower endpoint numerator. -/
  lower : BitVec width
  /-- Signed upper endpoint numerator. -/
  upper : BitVec width
  deriving DecidableEq, Repr

/-- Encode signed endpoint numerators at a chosen width. -/
def EncodedInterval.ofInt (width : ℕ) (lower upper : ℤ) : EncodedInterval width :=
  ⟨BitVec.ofInt width lower, BitVec.ofInt width upper⟩

/-- Decode endpoints, recording their signed order in the guard. -/
def EncodedInterval.decode (value : EncodedInterval width) :
    FixedDyadicInterval width precision :=
  let ok := value.lower.sle value.upper
  ⟨value.lower, value.upper, ok, by simp [ok]⟩

/-- Check a computed guarded interval against proof-free encoded endpoints. -/
def matchClaim (computed : FixedDyadicInterval width precision)
    (claimed : EncodedInterval width) : Bool :=
  computed.ok && computed.lower == claimed.lower && computed.upper == claimed.upper

/-- A successful endpoint comparison identifies the computed interval. -/
theorem eq_decode_of_matches {computed : FixedDyadicInterval width precision}
    {claimed : EncodedInterval width} (h : matchClaim computed claimed = true) :
    computed = claimed.decode := by
  simp only [matchClaim, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨hok, hlower⟩, hupper⟩
  cases computed with
  | mk lower upper ok ordered =>
      cases claimed with
      | mk claimedLower claimedUpper =>
          simp only at hlower hupper
          subst lower
          subst upper
          simp only [EncodedInterval.decode]
          have horder := ordered hok
          cases ok <;> simp_all

/-- One interval-arithmetic instruction over a growing register array. -/
inductive Op where
  | ofRat (value : ℚ)
  | ofInterval (lower upper : ℚ)
  | add (left right : ℕ)
  | neg (value : ℕ)
  | mul (left right : ℕ)
  deriving DecidableEq, Repr

/-- Evaluate one instruction with guarded signed bit vectors. -/
def evalFixed? (registers : Array (FixedDyadicInterval width precision)) :
    Op → Option (FixedDyadicInterval width precision)
  | .ofRat value => some (FixedDyadicInterval.ofRat width precision value)
  | .ofInterval lower upper =>
      if h : lower ≤ upper then
        some (FixedDyadicInterval.fromDyadic width
          (DyadicInterval.ofInterval precision ⟨lower, upper, h⟩))
      else
        none
  | .add left right => return (← registers[left]?).add (← registers[right]?)
  | .neg value => return (← registers[value]?).neg
  | .mul left right => return (← registers[left]?).mul (← registers[right]?)

/-- Evaluate one instruction with unbounded dyadic intervals. -/
def evalExact? (registers : Array (DyadicInterval precision)) :
    Op → Option (DyadicInterval precision)
  | .ofRat value => some (DyadicInterval.ofRat precision value)
  | .ofInterval lower upper =>
      if h : lower ≤ upper then some (DyadicInterval.ofInterval precision ⟨lower, upper, h⟩)
      else none
  | .add left right => return (← registers[left]?).add (← registers[right]?)
  | .neg value => return (← registers[value]?).neg
  | .mul left right => return (← registers[left]?).mul (← registers[right]?)

/-- Run a block, rejecting an invalid operand or any fixed-width overflow. -/
def runFixed : Array (FixedDyadicInterval width precision) → List Op →
    Option (Array (FixedDyadicInterval width precision))
  | registers, [] => some registers
  | registers, op :: ops => do
      let result ← evalFixed? registers op
      if result.ok then runFixed (registers.push result) ops else none

/-- Run the corresponding block with unbounded dyadic endpoints. -/
def runExact : Array (DyadicInterval precision) → List Op →
    Option (Array (DyadicInterval precision))
  | registers, [] => some registers
  | registers, op :: ops => do
      let result ← evalExact? registers op
      runExact (registers.push result) ops

/-- Pointwise exact representation of an unbounded register array. -/
def Related (fixed : Array (FixedDyadicInterval width precision))
    (exact : Array (DyadicInterval precision)) : Prop :=
  fixed.size = exact.size ∧ ∀ (i : ℕ) fixedValue exactValue,
    fixed[i]? = some fixedValue → exact[i]? = some exactValue →
      fixedValue.Represents exactValue

private theorem related_get {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (i : ℕ)
    {fixedValue : FixedDyadicInterval width precision} {exactValue : DyadicInterval precision}
    (hfixed : fixed[i]? = some fixedValue) (hexact : exact[i]? = some exactValue) :
    fixedValue.Represents exactValue :=
  h.2 i fixedValue exactValue hfixed hexact

private theorem exact_get_exists {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (i : ℕ)
    {fixedValue : FixedDyadicInterval width precision}
    (hfixed : fixed[i]? = some fixedValue) :
    ∃ exactValue, exact[i]? = some exactValue := by
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp hfixed
  have hiExact : i < exact.size := by simpa [← h.1] using hi
  exact ⟨exact[i], Array.getElem?_eq_getElem hiExact⟩

private theorem fromDyadic_represents (exact : DyadicInterval precision)
    (hok : (FixedDyadicInterval.fromDyadic width exact).ok = true) :
    (FixedDyadicInterval.fromDyadic width exact).Represents exact := by
  simp only [FixedDyadicInterval.Represents, FixedDyadicInterval.fromDyadic,
    Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  exact ⟨hok, hok.1.1, hok.1.2⟩

private theorem eval_add_related {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (left right : ℕ)
    {fixedResult : FixedDyadicInterval width precision}
    {exactResult : DyadicInterval precision}
    (hfixed : evalFixed? fixed (.add left right) = some fixedResult)
    (hexact : evalExact? exact (.add left right) = some exactResult)
    (hok : fixedResult.ok = true) : fixedResult.Represents exactResult := by
  cases hfixedLeft : fixed[left]? with
  | none => simp [evalFixed?, hfixedLeft] at hfixed
  | some fixedLeft =>
      cases hfixedRight : fixed[right]? with
      | none => simp [evalFixed?, hfixedLeft, hfixedRight] at hfixed
      | some fixedRight =>
          simp [evalFixed?, hfixedLeft, hfixedRight] at hfixed
          subst fixedResult
          cases hexactLeft : exact[left]? with
          | none => simp [evalExact?, hexactLeft] at hexact
          | some exactLeft =>
              cases hexactRight : exact[right]? with
              | none => simp [evalExact?, hexactLeft, hexactRight] at hexact
              | some exactRight =>
                  simp [evalExact?, hexactLeft, hexactRight] at hexact
                  subst exactResult
                  exact FixedDyadicInterval.add_represents
                    (related_get h left hfixedLeft hexactLeft)
                    (related_get h right hfixedRight hexactRight) hok

private theorem eval_neg_related {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (value : ℕ)
    {fixedResult : FixedDyadicInterval width precision}
    {exactResult : DyadicInterval precision}
    (hfixed : evalFixed? fixed (.neg value) = some fixedResult)
    (hexact : evalExact? exact (.neg value) = some exactResult)
    (hok : fixedResult.ok = true) : fixedResult.Represents exactResult := by
  cases hfixedValue : fixed[value]? with
  | none => simp [evalFixed?, hfixedValue] at hfixed
  | some fixedValue =>
      simp [evalFixed?, hfixedValue] at hfixed
      subst fixedResult
      cases hexactValue : exact[value]? with
      | none => simp [evalExact?, hexactValue] at hexact
      | some exactValue =>
          simp [evalExact?, hexactValue] at hexact
          subst exactResult
          exact FixedDyadicInterval.neg_represents
            (related_get h value hfixedValue hexactValue) hok

private theorem eval_mul_related {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (left right : ℕ)
    {fixedResult : FixedDyadicInterval width precision}
    {exactResult : DyadicInterval precision}
    (hfixed : evalFixed? fixed (.mul left right) = some fixedResult)
    (hexact : evalExact? exact (.mul left right) = some exactResult)
    (hok : fixedResult.ok = true) : fixedResult.Represents exactResult := by
  cases hfixedLeft : fixed[left]? with
  | none => simp [evalFixed?, hfixedLeft] at hfixed
  | some fixedLeft =>
      cases hfixedRight : fixed[right]? with
      | none => simp [evalFixed?, hfixedLeft, hfixedRight] at hfixed
      | some fixedRight =>
          simp [evalFixed?, hfixedLeft, hfixedRight] at hfixed
          subst fixedResult
          cases hexactLeft : exact[left]? with
          | none => simp [evalExact?, hexactLeft] at hexact
          | some exactLeft =>
              cases hexactRight : exact[right]? with
              | none => simp [evalExact?, hexactLeft, hexactRight] at hexact
              | some exactRight =>
                  simp [evalExact?, hexactLeft, hexactRight] at hexact
                  subst exactResult
                  exact FixedDyadicInterval.mul_represents
                    (related_get h left hfixedLeft hexactLeft)
                    (related_get h right hfixedRight hexactRight) hok

private theorem eval_related {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) {op : Op}
    {fixedResult : FixedDyadicInterval width precision}
    {exactResult : DyadicInterval precision} (hfixed : evalFixed? fixed op = some fixedResult)
    (hexact : evalExact? exact op = some exactResult) (hok : fixedResult.ok = true) :
    fixedResult.Represents exactResult := by
  cases op with
  | ofRat value =>
      simp only [evalFixed?, Option.some.injEq] at hfixed
      simp only [evalExact?, Option.some.injEq] at hexact
      subst fixedResult
      subst exactResult
      exact FixedDyadicInterval.ofRat_represents width precision value hok
  | ofInterval lower upper =>
      by_cases horder : lower ≤ upper
      · simp only [evalFixed?, evalExact?, horder, dite_true, Option.some.injEq]
          at hfixed hexact
        subst fixedResult
        subst exactResult
        exact fromDyadic_represents _ hok
      · simp [evalFixed?, horder] at hfixed
  | add left right => exact eval_add_related h left right hfixed hexact hok
  | neg value => exact eval_neg_related h value hfixed hexact hok
  | mul left right => exact eval_mul_related h left right hfixed hexact hok

private theorem evalExact_add_exists
    {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact)
    (left right : ℕ)
    {fixedResult : FixedDyadicInterval width precision}
    (hfixed : evalFixed? fixed (.add left right) = some fixedResult) :
    ∃ exactResult, evalExact? exact (.add left right) = some exactResult := by
  cases hfixedLeft : fixed[left]? with
  | none => simp [evalFixed?, hfixedLeft] at hfixed
  | some fixedLeft =>
      cases hfixedRight : fixed[right]? with
      | none => simp [evalFixed?, hfixedLeft, hfixedRight] at hfixed
      | some fixedRight =>
          obtain ⟨exactLeft, hexactLeft⟩ := exact_get_exists h left hfixedLeft
          obtain ⟨exactRight, hexactRight⟩ := exact_get_exists h right hfixedRight
          exact ⟨exactLeft.add exactRight, by
            simp [evalExact?, hexactLeft, hexactRight]⟩

private theorem evalExact_neg_exists
    {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (value : ℕ)
    {fixedResult : FixedDyadicInterval width precision}
    (hfixed : evalFixed? fixed (.neg value) = some fixedResult) :
    ∃ exactResult, evalExact? exact (.neg value) = some exactResult := by
  cases hfixedValue : fixed[value]? with
  | none => simp [evalFixed?, hfixedValue] at hfixed
  | some fixedValue =>
      obtain ⟨exactValue, hexactValue⟩ := exact_get_exists h value hfixedValue
      exact ⟨exactValue.neg, by simp [evalExact?, hexactValue]⟩

private theorem evalExact_mul_exists
    {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact)
    (left right : ℕ) {fixedResult : FixedDyadicInterval width precision}
    (hfixed : evalFixed? fixed (.mul left right) = some fixedResult) :
    ∃ exactResult, evalExact? exact (.mul left right) = some exactResult := by
  cases hfixedLeft : fixed[left]? with
  | none => simp [evalFixed?, hfixedLeft] at hfixed
  | some fixedLeft =>
      cases hfixedRight : fixed[right]? with
      | none => simp [evalFixed?, hfixedLeft, hfixedRight] at hfixed
      | some fixedRight =>
          obtain ⟨exactLeft, hexactLeft⟩ := exact_get_exists h left hfixedLeft
          obtain ⟨exactRight, hexactRight⟩ := exact_get_exists h right hfixedRight
          exact ⟨exactLeft.mul exactRight, by
            simp [evalExact?, hexactLeft, hexactRight]⟩

private theorem evalExact_exists_of_evalFixed
    {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) {op : Op}
    {fixedResult : FixedDyadicInterval width precision}
    (hfixed : evalFixed? fixed op = some fixedResult) :
    ∃ exactResult, evalExact? exact op = some exactResult := by
  cases op with
  | ofRat value => exact ⟨DyadicInterval.ofRat precision value, rfl⟩
  | ofInterval lower upper =>
      by_cases horder : lower ≤ upper
      · exact ⟨DyadicInterval.ofInterval precision ⟨lower, upper, horder⟩, by
          simp [evalExact?, horder]⟩
      · simp [evalFixed?, horder] at hfixed
  | add left right => exact evalExact_add_exists h left right hfixed
  | neg value => exact evalExact_neg_exists h value hfixed
  | mul left right => exact evalExact_mul_exists h left right hfixed

private theorem related_push {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact)
    {fixedValue : FixedDyadicInterval width precision} {exactValue : DyadicInterval precision}
    (hvalue : fixedValue.Represents exactValue) :
    Related (fixed.push fixedValue) (exact.push exactValue) := by
  constructor
  · simp [h.1]
  · intro i fixedResult exactResult hfixed hexact
    by_cases hi : i = fixed.size
    · subst i
      simp only [Array.getElem?_push_size, Option.some.injEq] at hfixed
      rw [h.1, Array.getElem?_push_size] at hexact
      injection hexact with hexactEq
      subst fixedResult
      subst exactResult
      exact hvalue
    · have hiExact : i ≠ exact.size := by simpa [h.1] using hi
      simp only [Array.getElem?_push, hi, hiExact, ↓reduceIte] at hfixed hexact
      exact h.2 i fixedResult exactResult hfixed hexact

/-- Successful fixed and exact runs preserve pointwise representation. -/
theorem run_related {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (ops : List Op)
    {fixedOutput : Array (FixedDyadicInterval width precision)}
    {exactOutput : Array (DyadicInterval precision)}
    (hfixed : runFixed fixed ops = some fixedOutput)
    (hexact : runExact exact ops = some exactOutput) : Related fixedOutput exactOutput := by
  induction ops generalizing fixed exact fixedOutput exactOutput with
  | nil =>
      simp only [runFixed, Option.some.injEq] at hfixed
      simp only [runExact, Option.some.injEq] at hexact
      subst fixedOutput
      subst exactOutput
      exact h
  | cons op ops ih =>
      simp only [runFixed] at hfixed
      cases hfixedResult : evalFixed? fixed op with
      | none => simp [hfixedResult] at hfixed
      | some fixedResult =>
          simp only [hfixedResult] at hfixed
          cases hok : fixedResult.ok with
          | false => simp [hok] at hfixed
          | true =>
              simp only [runExact] at hexact
              cases hexactResult : evalExact? exact op with
              | none => simp [hexactResult] at hexact
              | some exactResult =>
                  simp only [hexactResult] at hexact
                  apply ih (related_push h <| eval_related h hfixedResult hexactResult hok)
                    (by simpa [hok] using hfixed) hexact

/-- A successful fixed run constructs a related exact run without replaying exact numerals. -/
theorem run_related_exists {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (h : Related fixed exact) (ops : List Op)
    {fixedOutput : Array (FixedDyadicInterval width precision)}
    (hfixed : runFixed fixed ops = some fixedOutput) :
    ∃ exactOutput, runExact exact ops = some exactOutput ∧ Related fixedOutput exactOutput := by
  induction ops generalizing fixed exact fixedOutput with
  | nil =>
      simp only [runFixed, Option.some.injEq] at hfixed
      subst fixedOutput
      exact ⟨exact, rfl, h⟩
  | cons op ops ih =>
      simp only [runFixed] at hfixed
      cases hfixedResult : evalFixed? fixed op with
      | none => simp [hfixedResult] at hfixed
      | some fixedResult =>
          simp only [hfixedResult] at hfixed
          cases hok : fixedResult.ok with
          | false => simp [hok] at hfixed
          | true =>
              obtain ⟨exactResult, hexactResult⟩ :=
                evalExact_exists_of_evalFixed h hfixedResult
              have hresult := eval_related h hfixedResult hexactResult hok
              obtain ⟨exactOutput, hexact, hrelated⟩ :=
                ih (related_push h hresult) (by simpa [hok] using hfixed)
              refine ⟨exactOutput, ?_, hrelated⟩
              simp [runExact, hexactResult, hexact]

/-- A live endpoint claim names one output register. -/
structure OutputClaim (width : ℕ) where
  /-- Register exported by the block. -/
  register : ℕ
  /-- Claimed fixed-width value of that register. -/
  value : EncodedInterval width
  deriving Repr

/-- Append decoded live values to an existing fixed-width boundary state. -/
def decodeClaimsFrom (selected : Array (FixedDyadicInterval width precision)) :
    List (OutputClaim width) → Array (FixedDyadicInterval width precision)
  | [] => selected
  | claim :: claims => decodeClaimsFrom (selected.push claim.value.decode) claims

/-- Decode the live fixed-width values exported by a block. -/
def decodeClaims (claims : List (OutputClaim width)) :
    Array (FixedDyadicInterval width precision) :=
  decodeClaimsFrom #[] claims

/-- Append the exact registers named by claims to an existing boundary state. -/
def selectExactFrom (registers : Array (DyadicInterval precision))
    (selected : Array (DyadicInterval precision)) :
    List (OutputClaim width) → Option (Array (DyadicInterval precision))
  | [] => some selected
  | claim :: claims => do
      let value ← registers[claim.register]?
      selectExactFrom registers (selected.push value) claims

/-- Select the exact registers named by the live claims, in claim order. -/
def selectExact? (registers : Array (DyadicInterval precision))
    (claims : List (OutputClaim width)) : Option (Array (DyadicInterval precision)) :=
  selectExactFrom registers #[] claims

/-- Check the live output claims of one block. -/
def checkClaims (registers : Array (FixedDyadicInterval width precision)) :
    List (OutputClaim width) → Bool
  | [] => true
  | claim :: claims =>
      match registers[claim.register]? with
      | some value => matchClaim value claim.value && checkClaims registers claims
      | none => false

private theorem selectExactFrom_related
    {fixedRegisters : Array (FixedDyadicInterval width precision)}
    {exactRegisters : Array (DyadicInterval precision)}
    (hregisters : Related fixedRegisters exactRegisters)
    {fixedSelected : Array (FixedDyadicInterval width precision)}
    {exactSelected : Array (DyadicInterval precision)}
    (hselected : Related fixedSelected exactSelected)
    {claims : List (OutputClaim width)} (hcheck : checkClaims fixedRegisters claims = true) :
    ∃ exactOutput,
      selectExactFrom exactRegisters exactSelected claims = some exactOutput ∧
      Related (decodeClaimsFrom fixedSelected claims) exactOutput := by
  induction claims generalizing fixedSelected exactSelected with
  | nil => exact ⟨exactSelected, rfl, hselected⟩
  | cons claim claims ih =>
      simp only [checkClaims] at hcheck
      cases hfixed : fixedRegisters[claim.register]? with
      | none => simp [hfixed] at hcheck
      | some fixedValue =>
          simp only [hfixed, Bool.and_eq_true] at hcheck
          obtain ⟨exactValue, hexact⟩ :=
            exact_get_exists hregisters claim.register hfixed
          have hvalue : claim.value.decode.Represents exactValue := by
            rw [← eq_decode_of_matches hcheck.1]
            exact related_get hregisters claim.register hfixed hexact
          obtain ⟨exactOutput, hselect, hrelated⟩ :=
            ih (related_push hselected hvalue) hcheck.2
          refine ⟨exactOutput, ?_, ?_⟩
          · simpa [selectExactFrom, hexact] using hselect
          · simpa [decodeClaimsFrom] using hrelated

/-- Checked live claims select a pointwise related exact boundary state. -/
theorem selectExact_related_of_checkClaims
    {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (hrelated : Related fixed exact)
    {claims : List (OutputClaim width)} (hcheck : checkClaims fixed claims = true) :
    ∃ exactSelected,
      selectExact? exact claims = some exactSelected ∧
      Related (decodeClaims claims) exactSelected := by
  have hempty : Related (#[] : Array (FixedDyadicInterval width precision))
      (#[] : Array (DyadicInterval precision)) := by
    constructor <;> simp
  simpa [selectExact?, decodeClaims] using
    selectExactFrom_related hrelated hempty hcheck

/-- Run one guarded block and check all of its live outputs. -/
def checkBlock (inputs : Array (FixedDyadicInterval width precision))
    (ops : List Op) (claims : List (OutputClaim width)) : Bool :=
  match runFixed inputs ops with
  | some output => checkClaims output claims
  | none => false

/-- A checked block constructs an exact run and a related live boundary state. -/
theorem checkBlock_related
    {fixedInputs : Array (FixedDyadicInterval width precision)}
    {exactInputs : Array (DyadicInterval precision)} (hrelated : Related fixedInputs exactInputs)
    {ops : List Op} {claims : List (OutputClaim width)}
    (hcheck : checkBlock fixedInputs ops claims = true) :
    ∃ exactOutput exactSelected,
      runExact exactInputs ops = some exactOutput ∧
      selectExact? exactOutput claims = some exactSelected ∧
      Related (decodeClaims claims) exactSelected := by
  simp only [checkBlock] at hcheck
  cases hfixed : runFixed fixedInputs ops with
  | none => simp [hfixed] at hcheck
  | some fixedOutput =>
      simp only [hfixed] at hcheck
      obtain ⟨exactOutput, hexact, houtput⟩ :=
        run_related_exists hrelated ops hfixed
      obtain ⟨exactSelected, hselect, hselected⟩ :=
        selectExact_related_of_checkClaims houtput hcheck
      exact ⟨exactOutput, exactSelected, hexact, hselect, hselected⟩

/-- Every checked live claim represents the corresponding exact output. -/
theorem claim_represents_of_checkClaims
    {fixed : Array (FixedDyadicInterval width precision)}
    {exact : Array (DyadicInterval precision)} (hrelated : Related fixed exact)
    {claims : List (OutputClaim width)} (hcheck : checkClaims fixed claims = true)
    {claim : OutputClaim width} (hclaim : claim ∈ claims) :
    ∃ exactValue, exact[claim.register]? = some exactValue ∧
      claim.value.decode.Represents exactValue := by
  induction claims with
  | nil => simp at hclaim
  | cons head tail ih =>
      simp only [checkClaims] at hcheck
      cases hfixed : fixed[head.register]? with
      | none => simp [hfixed] at hcheck
      | some fixedValue =>
          simp only [hfixed, Bool.and_eq_true] at hcheck
          simp only [List.mem_cons] at hclaim
          rcases hclaim with hhead | htail
          · subst claim
            obtain ⟨hindex, _⟩ := Array.getElem?_eq_some_iff.mp hfixed
            have hexactIndex : head.register < exact.size := by
              simpa [← hrelated.1] using hindex
            rw [Array.getElem?_eq_getElem hexactIndex]
            refine ⟨exact[head.register], rfl, ?_⟩
            rw [← eq_decode_of_matches hcheck.1]
            exact related_get hrelated head.register hfixed
              (Array.getElem?_eq_getElem hexactIndex)
          · exact ih hcheck.2 htail

/-- A checked block constructs an exact run in which each live claim is represented. -/
theorem claim_represents_of_checkBlock
    {fixedInputs : Array (FixedDyadicInterval width precision)}
    {exactInputs : Array (DyadicInterval precision)} (hrelated : Related fixedInputs exactInputs)
    {ops : List Op} {claims : List (OutputClaim width)}
    (hcheck : checkBlock fixedInputs ops claims = true)
    {claim : OutputClaim width} (hclaim : claim ∈ claims) :
    ∃ exactOutput exactValue,
      runExact exactInputs ops = some exactOutput ∧
      exactOutput[claim.register]? = some exactValue ∧
      claim.value.decode.Represents exactValue := by
  simp only [checkBlock] at hcheck
  cases hfixed : runFixed fixedInputs ops with
  | none => simp [hfixed] at hcheck
  | some fixedOutput =>
      simp only [hfixed] at hcheck
      obtain ⟨exactOutput, hexact, houtput⟩ :=
        run_related_exists hrelated ops hfixed
      obtain ⟨exactValue, hget, hrep⟩ :=
        claim_represents_of_checkClaims houtput hcheck hclaim
      exact ⟨exactOutput, exactValue, hexact, hget, hrep⟩

/-- Check that an encoded lower endpoint is nonnegative in signed order. -/
def EncodedInterval.lowerNonnegative (value : EncodedInterval width) : Bool :=
  (0 : BitVec width).sle value.lower

/-- A nonnegative encoded lower endpoint gives a nonnegative represented dyadic endpoint. -/
theorem dyadic_lowerNonnegative_of_encoded
    {value : EncodedInterval width} {exact : DyadicInterval precision}
    (hrep : value.decode.Represents exact) (hcheck : value.lowerNonnegative = true) :
    exact.lowerNonnegative = true := by
  simp only [EncodedInterval.lowerNonnegative, BitVec.sle_iff_toInt_le] at hcheck
  simp only [FixedDyadicInterval.Represents, EncodedInterval.decode] at hrep
  simp only [DyadicInterval.lowerNonnegative, decide_eq_true_eq]
  rw [← hrep.2.1]
  simpa using hcheck

end Bescovitch.ScalarTraceVerifier

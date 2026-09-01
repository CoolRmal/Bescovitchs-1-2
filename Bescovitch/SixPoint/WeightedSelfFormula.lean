/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelf

/-!
# The reduced weighted-self polynomial formula

The square-root reduction in the weighted self inequality produces two polynomials and one
Gram radicand.  This module records their common straight-line formula independently of the
coefficient type, so exact and interval evaluators use the same fixed expression.
-/

@[expose] public section

namespace Bescovitch

/-- The two reduced polynomials and their Gram radicand. -/
structure WeightedSelfFormula (α : Type*) where
  /-- The constant part after reducing the squared Gram ordinate. -/
  p : α
  /-- The coefficient of the Gram square root. -/
  q : α
  /-- The Gram radicand. -/
  radicand : α

/-- Operations needed to evaluate the reduced weighted-self formula. -/
structure WeightedSelfFormulaOperations (α : Type*) where
  /-- Embed a rational constant. -/
  rational : ℚ → α
  /-- Addition. -/
  add : α → α → α
  /-- Additive inverse. -/
  neg : α → α
  /-- Multiplication. -/
  mul : α → α → α
  /-- Natural powers. -/
  pow : α → ℕ → α

/-- The fixed reduced weighted-self formula in an arbitrary coefficient algebra. -/
def weightedSelfFormula {α : Type*} (o : WeightedSelfFormulaOperations α)
    (atom : Fin 18 → α) (r b t : α) : WeightedSelfFormula α :=
  let c := atom 0
  let B := atom 1
  let D := atom 2
  let A := atom 3
  let C := atom 4
  let lambda := atom 5
  let mu := atom 6
  let aB := atom 7
  let kappaB := atom 8
  let aD := atom 9
  let kappaD := atom 10
  let aA := atom 11
  let kappaA := atom 12
  let aC := atom 13
  let kappaC := atom 14
  let firstPenalty := atom 15
  let secondPenalty := atom 16
  let constantTerm := atom 17
  let sub a b := o.add a (o.neg b)
  let scale := o.mul
  let one := o.rational 1
  let k := scale (o.rational (1 / 2))
    (sub (o.add (o.pow r 2) (o.pow b 2)) (o.pow c 2))
  let radicand := o.mul (sub one (o.pow t 2))
    (sub (o.mul (o.pow r 2) (o.pow b 2)) (o.pow k 2))
  let qB := sub (o.add one (scale (o.rational 4) (o.pow r 2)))
    (scale (o.rational 4) (o.mul r t))
  let qA := sub (o.add one (o.pow r 2))
    (scale (o.rational 2) (o.mul r t))
  let uD := sub
    (o.mul r (sub (o.add one (scale (o.rational 4) (o.pow b 2))) (o.pow D 2)))
    (scale (o.rational 4) (o.mul k t))
  let uC := sub
    (o.mul r (sub
      (o.add (o.add (o.add one (o.pow r 2)) (o.pow b 2))
        (sub (scale (o.rational 2) k) (scale (o.rational 2) (o.mul r t))))
      (o.pow C 2)))
    (scale (o.rational 2) (o.mul k t))
  let FB := sub
    (o.add (scale aB qB)
      (o.mul (o.mul (o.add one lambda) B) (o.rational (1 / 2))))
    (scale kappaB (o.pow (sub qB (o.pow B 2)) 2))
  let FA := sub
    (o.add (scale aA qA) (o.mul (o.mul mu A) (o.rational (1 / 2))))
    (scale kappaA (o.pow (sub qA (o.pow A 2)) 2))
  let FD := sub
    (o.add (scale aD (o.add (scale (o.pow D 2) (o.pow r 2)) (o.mul r uD)))
      (scale (o.mul D (o.rational (1 / 2))) (o.pow r 2)))
    (scale kappaD (o.pow uD 2))
  let FC := sub
    (o.add (scale aC (o.add (scale (o.pow C 2) (o.pow r 2)) (o.mul r uC)))
      (scale (o.mul (o.mul mu C) (o.rational (1 / 2))) (o.pow r 2)))
    (scale kappaC (o.pow uC 2))
  let p := o.add
    (scale one (o.mul (o.pow r 2)
      (sub (sub (sub (o.add FB FA) (o.mul firstPenalty r))
        (o.mul secondPenalty b)) constantTerm)))
    (sub (sub (o.add FD FC)
      (scale (o.mul (o.rational 16) kappaD) radicand))
      (scale (o.mul (o.rational 4) kappaC) radicand))
  let q := o.add
    (scale (o.rational 4)
      (sub (scale aD r) (scale (o.mul (o.rational 2) kappaD) uD)))
    (scale (o.rational 2)
      (sub (scale aC r) (scale (o.mul (o.rational 2) kappaC) uC)))
  ⟨p, q, radicand⟩

/-- A map preserving the five formula operations preserves all three outputs. -/
theorem weightedSelfFormula_map {α β : Type*}
    (source : WeightedSelfFormulaOperations α)
    (target : WeightedSelfFormulaOperations β) (f : α → β)
    (hrational : ∀ q, f (source.rational q) = target.rational q)
    (hadd : ∀ a b, f (source.add a b) = target.add (f a) (f b))
    (hneg : ∀ a, f (source.neg a) = target.neg (f a))
    (hmul : ∀ a b, f (source.mul a b) = target.mul (f a) (f b))
    (hpow : ∀ a n, f (source.pow a n) = target.pow (f a) n)
    (atom : Fin 18 → α) (r b t : α) :
    let sourceFormula := weightedSelfFormula source atom r b t
    let targetFormula := weightedSelfFormula target (f ∘ atom) (f r) (f b) (f t)
    f sourceFormula.p = targetFormula.p ∧
      f sourceFormula.q = targetFormula.q ∧
      f sourceFormula.radicand = targetFormula.radicand := by
  simp only [weightedSelfFormula, Function.comp_apply, hrational, hadd, hneg, hmul, hpow]
  exact ⟨trivial, trivial, trivial⟩

/-- A relation preserved by the five formula operations relates all three outputs. -/
theorem weightedSelfFormula_rel {α β : Type*}
    (source : WeightedSelfFormulaOperations α)
    (target : WeightedSelfFormulaOperations β) (rel : α → β → Prop)
    (hrational : ∀ q, rel (source.rational q) (target.rational q))
    (hadd : ∀ {a a' b b'}, rel a a' → rel b b' →
      rel (source.add a b) (target.add a' b'))
    (hneg : ∀ {a a'}, rel a a' → rel (source.neg a) (target.neg a'))
    (hmul : ∀ {a a' b b'}, rel a a' → rel b b' →
      rel (source.mul a b) (target.mul a' b'))
    (hpow : ∀ {a a'}, rel a a' → ∀ n, rel (source.pow a n) (target.pow a' n))
    {atom : Fin 18 → α} {atom' : Fin 18 → β}
    (hatom : ∀ i, rel (atom i) (atom' i))
    {r b t : α} {r' b' t' : β}
    (hr : rel r r') (hb : rel b b') (ht : rel t t') :
    let sourceFormula := weightedSelfFormula source atom r b t
    let targetFormula := weightedSelfFormula target atom' r' b' t'
    rel sourceFormula.p targetFormula.p ∧
      rel sourceFormula.q targetFormula.q ∧
      rel sourceFormula.radicand targetFormula.radicand := by
  let Related := {pair : α × β // rel pair.1 pair.2}
  let paired : WeightedSelfFormulaOperations Related :=
    ⟨fun q ↦ ⟨(source.rational q, target.rational q), hrational q⟩,
      fun a b ↦ ⟨(source.add a.1.1 b.1.1, target.add a.1.2 b.1.2),
        hadd a.2 b.2⟩,
      fun a ↦ ⟨(source.neg a.1.1, target.neg a.1.2), hneg a.2⟩,
      fun a b ↦ ⟨(source.mul a.1.1 b.1.1, target.mul a.1.2 b.1.2),
        hmul a.2 b.2⟩,
      fun a n ↦ ⟨(source.pow a.1.1 n, target.pow a.1.2 n), hpow a.2 n⟩⟩
  let pairedAtom (i : Fin 18) : Related := ⟨(atom i, atom' i), hatom i⟩
  let pairedR : Related := ⟨(r, r'), hr⟩
  let pairedB : Related := ⟨(b, b'), hb⟩
  let pairedT : Related := ⟨(t, t'), ht⟩
  let pairedFormula := weightedSelfFormula paired pairedAtom pairedR pairedB pairedT
  have hleft := weightedSelfFormula_map paired source
    (fun x : Related ↦ x.1.1) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      pairedAtom pairedR pairedB pairedT
  have hright := weightedSelfFormula_map paired target
    (fun x : Related ↦ x.1.2) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      pairedAtom pairedR pairedB pairedT
  have hp := pairedFormula.p.2
  have hq := pairedFormula.q.2
  have hradicand := pairedFormula.radicand.2
  change rel pairedFormula.p.1.1 pairedFormula.p.1.2 at hp
  change rel pairedFormula.q.1.1 pairedFormula.q.1.2 at hq
  change rel pairedFormula.radicand.1.1 pairedFormula.radicand.1.2 at hradicand
  dsimp only [pairedFormula] at hp hq hradicand
  rw [hleft.1, hright.1] at hp
  rw [hleft.2.1, hright.2.1] at hq
  rw [hleft.2.2, hright.2.2] at hradicand
  exact ⟨hp, hq, hradicand⟩

/-- The three scalar coordinates used by a weighted-self certificate chart. -/
structure WeightedSelfChart (α : Type*) where
  /-- First radius. -/
  r : α
  /-- Second radius. -/
  b : α
  /-- Normalized first projection. -/
  t : α

/-- The affine unit-cube chart for one interval of second radii. -/
noncomputable def weightedSelfRealChart (lower upper x y z : ℝ) : WeightedSelfChart ℝ :=
  let b := lower + (upper - lower) * y
  let r := cStar - b + (1 - cStar + b) * x
  let t := -1 + 2 * z
  ⟨r, b, t⟩

/-- The first radius in the affine chart is positive on every bin below radius one. -/
theorem weightedSelfRealChart_first_pos {lower upper x y z : ℝ}
    (hwidth : lower ≤ upper) (hupper : upper ≤ 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 < (weightedSelfRealChart lower upper x y z).r := by
  let b := lower + (upper - lower) * y
  have hbUpper : b ≤ upper := by
    dsimp only [b]
    calc
      lower + (upper - lower) * y ≤ lower + (upper - lower) * 1 := by
        simpa only [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hy.2 (sub_nonneg.mpr hwidth)) lower
      _ = upper := by ring
  have hcb : 0 < cStar - b := by
    linarith [one_lt_cStar_and_cStar_lt_two.1]
  have hconvex : 0 < (cStar - b) * (1 - x) + x := by
    by_cases hxZero : x = 0
    · simpa [hxZero] using hcb
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg hcb.le (sub_nonneg.mpr hx.2)) (lt_of_le_of_ne hx.1 (Ne.symm hxZero))
  change 0 < cStar - b + (1 - cStar + b) * x
  nlinarith [hconvex]

end Bescovitch

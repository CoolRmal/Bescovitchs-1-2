/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.DyadicTrivariatePolynomial.Evaluation
public import Bescovitch.SixPoint.WeightedSelfCertificateCore
import Mathlib.Tactic.NormNum

/-!
# Exact dyadic evaluation of the weighted-self formula
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfDyadicPolynomial

noncomputable section

open DyadicTrivariatePolynomial

/--
The fixed reduced formula specialized to the finite dyadic constants occurring in
`weightedSelfFormula`.
-/
def formula (atom : Fin 18 → ScaledPolynomial)
    (r b t : ScaledPolynomial) : Bescovitch.WeightedSelfFormula ScaledPolynomial :=
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
  let one := ScaledPolynomial.dyadic 1 0
  let half := ScaledPolynomial.dyadic 1 1
  let two := ScaledPolynomial.dyadic 2 0
  let four := ScaledPolynomial.dyadic 4 0
  let sixteen := ScaledPolynomial.dyadic 16 0
  let k := half * (r ^ 2 + b ^ 2 + -(c ^ 2))
  let radicand := (one + -(t ^ 2)) * (r ^ 2 * b ^ 2 + -(k ^ 2))
  let qB := one + four * r ^ 2 + -(four * (r * t))
  let qA := one + r ^ 2 + -(two * (r * t))
  let uD := r * (one + four * b ^ 2 + -(D ^ 2)) + -(four * (k * t))
  let uC := r * (one + r ^ 2 + b ^ 2 +
      (two * k + -(two * (r * t))) + -(C ^ 2)) + -(two * (k * t))
  let FB := aB * qB + (one + lambda) * B * half +
    -(kappaB * (qB + -(B ^ 2)) ^ 2)
  let FA := aA * qA + mu * A * half + -(kappaA * (qA + -(A ^ 2)) ^ 2)
  let FD := aD * (D ^ 2 * r ^ 2 + r * uD) + D * half * r ^ 2 +
    -(kappaD * uD ^ 2)
  let FC := aC * (C ^ 2 * r ^ 2 + r * uC) + mu * C * half * r ^ 2 +
    -(kappaC * uC ^ 2)
  let p := one * (r ^ 2 *
      (((FB + FA + -(firstPenalty * r)) + -(secondPenalty * b)) + -constantTerm)) +
    ((FD + FC + -(sixteen * kappaD * radicand)) + -(four * kappaC * radicand))
  let q := four * (aD * r + -(two * kappaD * uD)) +
    two * (aC * r + -(two * kappaC * uC))
  ⟨p, q, radicand⟩

/-- Evaluation of the specialized dyadic formula agrees with the real formula. -/
theorem eval_formula (atom : Fin 18 → ScaledPolynomial)
    (r b t : ScaledPolynomial) (x y z : ℝ) :
    let source := formula atom r b t
    let target := Bescovitch.weightedSelfFormula weightedSelfRealFormulaOperations
      (fun i ↦ ScaledPolynomial.eval (atom i) x y z)
      (ScaledPolynomial.eval r x y z) (ScaledPolynomial.eval b x y z)
      (ScaledPolynomial.eval t x y z)
    ScaledPolynomial.eval source.p x y z = target.p ∧
      ScaledPolynomial.eval source.q x y z = target.q ∧
      ScaledPolynomial.eval source.radicand x y z = target.radicand := by
  simp only [formula, Bescovitch.weightedSelfFormula,
    weightedSelfRealFormulaOperations, ScaledPolynomial.eval_add_notation,
    ScaledPolynomial.eval_neg_notation, ScaledPolynomial.eval_mul_notation,
    ScaledPolynomial.eval_pow_notation, ScaledPolynomial.eval_dyadic]
  norm_num

end

end WeightedSelfDyadicPolynomial
end Bescovitch

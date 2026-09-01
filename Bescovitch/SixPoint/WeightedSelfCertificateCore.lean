/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.EndpointTightBounds
public import Bescovitch.Certificates.IntervalBernstein
public import Bescovitch.Certificates.IntervalHorner
public import Bescovitch.SixPoint.WeightedSelfFormula

/-!
# Semantic core of the weighted self certificate

The scalar reduction in `WeightedSelf` is polynomial after the Gram square root is isolated.
This file turns exact endpoint intervals and tensor Bernstein certificates into a bound on one
radius bin.  A later module supplies and assembles the seven bins.
-/

@[expose] public section

open scoped unitInterval

namespace Bescovitch

private abbrev RE := RadicalExpression 18
private abbrev RP := RadicalTrivariate 18

namespace RadicalExpression

/-- Subtraction of radical expressions. -/
def sub {n : ℕ} (a b : RadicalExpression n) : RadicalExpression n := .add a (.neg b)

/-- Division of radical expressions. -/
def div {n : ℕ} (a b : RadicalExpression n) : RadicalExpression n := .mul a (.inv b)

/-- Natural powers of a radical expression. -/
def pow {n : ℕ} (a : RadicalExpression n) : ℕ → RadicalExpression n
  | 0 => .constant 1
  | n + 1 => .mul (pow a n) a

end RadicalExpression

private structure CertifiedCoefficient (input : Fin 18 → ℝ) where
  exact : RE
  enclosure : RationalInterval
  valid : enclosure.Contains (exact.eval input)
  value : ℝ
  evaluates : exact.eval input = value

namespace CertifiedCoefficient

private def rational (input : Fin 18 → ℝ) (q : ℚ) : CertifiedCoefficient input :=
  ⟨.constant q, .singleton q, RationalInterval.singleton_contains q, q, by
    simp [RadicalExpression.eval]⟩

private def atom (input : Fin 18 → ℝ) (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (input i)) (i : Fin 18) : CertifiedCoefficient input :=
  ⟨.var i, box i, hinput i, input i, by simp [RadicalExpression.eval]⟩

private def add {input : Fin 18 → ℝ} (a b : CertifiedCoefficient input) :
    CertifiedCoefficient input :=
  ⟨.add a.exact b.exact, a.enclosure.add b.enclosure,
    RationalInterval.add_contains a.valid b.valid, a.value + b.value, by
      simp [RadicalExpression.eval, a.evaluates, b.evaluates]⟩

private def neg {input : Fin 18 → ℝ} (a : CertifiedCoefficient input) :
    CertifiedCoefficient input :=
  ⟨.neg a.exact, a.enclosure.neg, RationalInterval.neg_contains a.valid, -a.value, by
    simp [RadicalExpression.eval, a.evaluates]⟩

private def mul {input : Fin 18 → ℝ} (a b : CertifiedCoefficient input) :
    CertifiedCoefficient input :=
  ⟨.mul a.exact b.exact, a.enclosure.mul b.enclosure,
    RationalInterval.mul_contains a.valid b.valid, a.value * b.value, by
      simp [RadicalExpression.eval, a.evaluates, b.evaluates]⟩

private def pow {input : Fin 18 → ℝ} (a : CertifiedCoefficient input) :
    ℕ → CertifiedCoefficient input
  | 0 => rational input 1
  | n + 1 => mul (pow a n) a

private theorem eval_rational (input : Fin 18 → ℝ) (q : ℚ) :
    (rational input q).exact.eval input = q := by
  simp [rational, RadicalExpression.eval]

private theorem eval_add {input : Fin 18 → ℝ} (a b : CertifiedCoefficient input) :
    (add a b).exact.eval input = a.exact.eval input + b.exact.eval input := by
  simp [add, RadicalExpression.eval]

private theorem eval_neg {input : Fin 18 → ℝ} (a : CertifiedCoefficient input) :
    (neg a).exact.eval input = -a.exact.eval input := by
  simp [neg, RadicalExpression.eval]

private theorem eval_mul {input : Fin 18 → ℝ} (a b : CertifiedCoefficient input) :
    (mul a b).exact.eval input = a.exact.eval input * b.exact.eval input := by
  simp [mul, RadicalExpression.eval]

private theorem eval_pow {input : Fin 18 → ℝ} (a : CertifiedCoefficient input)
    (n : ℕ) : (pow a n).exact.eval input = a.exact.eval input ^ n := by
  induction n with
  | zero => simp [pow, eval_rational]
  | succ n ih => simp [pow, eval_mul, ih, pow_succ]

private theorem value_rational (input : Fin 18 → ℝ) (q : ℚ) :
    (rational input q).value = q := rfl

private theorem value_add {input : Fin 18 → ℝ} (a b : CertifiedCoefficient input) :
    (add a b).value = a.value + b.value := rfl

private theorem value_neg {input : Fin 18 → ℝ} (a : CertifiedCoefficient input) :
    (neg a).value = -a.value := rfl

private theorem value_mul {input : Fin 18 → ℝ} (a b : CertifiedCoefficient input) :
    (mul a b).value = a.value * b.value := rfl

private theorem value_pow {input : Fin 18 → ℝ} (a : CertifiedCoefficient input)
    (n : ℕ) : (pow a n).value = a.value ^ n := by
  induction n with
  | zero => simp [pow, value_rational]
  | succ n ih => simp [pow, value_mul, ih, pow_succ]

end CertifiedCoefficient

private structure CertifiedPolynomial (input : Fin 18 → ℝ) where
  exact : RP
  enclosure : IntervalTrivariate
  valid : enclosure.Contains input exact
  value : ℝ → ℝ → ℝ → ℝ
  evaluates : ∀ x y z, exact.eval input x y z = value x y z

namespace CertifiedPolynomial

private def constant {input : Fin 18 → ℝ} (a : CertifiedCoefficient input) :
    CertifiedPolynomial input :=
  ⟨.constant a.exact, .constant a.enclosure, IntervalTrivariate.contains_constant a.valid,
    fun _ _ _ ↦ a.value, fun x y z ↦ by simp [a.evaluates]⟩

private def first (input : Fin 18 → ℝ) : CertifiedPolynomial input :=
  ⟨.first, .first, IntervalTrivariate.contains_first input, fun x _ _ ↦ x,
    fun x y z ↦ by simp⟩

private def second (input : Fin 18 → ℝ) : CertifiedPolynomial input :=
  ⟨.second, .second, IntervalTrivariate.contains_second input, fun _ y _ ↦ y,
    fun x y z ↦ by simp⟩

private def third (input : Fin 18 → ℝ) : CertifiedPolynomial input :=
  ⟨RadicalTrivariate.third, .third, IntervalTrivariate.contains_third input,
    fun _ _ z ↦ z, fun x y z ↦ by simp⟩

private def add {input : Fin 18 → ℝ} (p q : CertifiedPolynomial input) :
    CertifiedPolynomial input :=
  ⟨.add p.exact q.exact, .add p.enclosure q.enclosure,
    IntervalTrivariate.contains_add p.valid q.valid,
    fun x y z ↦ p.value x y z + q.value x y z, fun x y z ↦ by
      rw [RadicalTrivariate.eval_add, p.evaluates, q.evaluates]⟩

private def neg {input : Fin 18 → ℝ} (p : CertifiedPolynomial input) :
    CertifiedPolynomial input :=
  ⟨.neg p.exact, .neg p.enclosure, IntervalTrivariate.contains_neg p.valid,
    fun x y z ↦ -p.value x y z, fun x y z ↦ by
      rw [RadicalTrivariate.eval_neg, p.evaluates]⟩

private def mul {input : Fin 18 → ℝ} (p q : CertifiedPolynomial input) :
    CertifiedPolynomial input :=
  ⟨.mul p.exact q.exact, .mul p.enclosure q.enclosure,
    IntervalTrivariate.contains_mul p.valid q.valid,
    fun x y z ↦ p.value x y z * q.value x y z, fun x y z ↦ by
      rw [RadicalTrivariate.eval_mul, p.evaluates, q.evaluates]⟩

private def pow {input : Fin 18 → ℝ} (p : CertifiedPolynomial input) (n : ℕ) :
    CertifiedPolynomial input :=
  ⟨RadicalTrivariate.pow p.exact n, IntervalTrivariate.pow p.enclosure n,
    IntervalTrivariate.contains_pow p.valid n, fun x y z ↦ p.value x y z ^ n,
    fun x y z ↦ by rw [RadicalTrivariate.eval_pow, p.evaluates]⟩

private theorem eval_add {input : Fin 18 → ℝ} (p q : CertifiedPolynomial input)
    (x y z : ℝ) :
    (add p q).exact.eval input x y z =
      p.exact.eval input x y z + q.exact.eval input x y z := by
  simp [add, RadicalTrivariate.eval_add]

private theorem eval_neg {input : Fin 18 → ℝ} (p : CertifiedPolynomial input)
    (x y z : ℝ) :
    (neg p).exact.eval input x y z = -p.exact.eval input x y z := by
  simp [neg, RadicalTrivariate.eval_neg]

private theorem eval_mul {input : Fin 18 → ℝ} (p q : CertifiedPolynomial input)
    (x y z : ℝ) :
    (mul p q).exact.eval input x y z =
      p.exact.eval input x y z * q.exact.eval input x y z := by
  simp [mul, RadicalTrivariate.eval_mul]

private theorem eval_pow {input : Fin 18 → ℝ} (p : CertifiedPolynomial input)
    (n : ℕ) (x y z : ℝ) :
    (pow p n).exact.eval input x y z = p.exact.eval input x y z ^ n := by
  simp [pow, RadicalTrivariate.eval_pow]

private theorem value_add {input : Fin 18 → ℝ} (p q : CertifiedPolynomial input)
    (x y z : ℝ) :
    (add p q).value x y z = p.value x y z + q.value x y z := rfl

private theorem value_neg {input : Fin 18 → ℝ} (p : CertifiedPolynomial input)
    (x y z : ℝ) : (neg p).value x y z = -p.value x y z := rfl

private theorem value_mul {input : Fin 18 → ℝ} (p q : CertifiedPolynomial input)
    (x y z : ℝ) :
    (mul p q).value x y z = p.value x y z * q.value x y z := rfl

private theorem value_pow {input : Fin 18 → ℝ} (p : CertifiedPolynomial input)
    (n : ℕ) (x y z : ℝ) :
    (pow p n).value x y z = p.value x y z ^ n := rfl

end CertifiedPolynomial

private structure WeightedSelfCertifiedPolynomials (input : Fin 18 → ℝ) where
  p : CertifiedPolynomial input
  q : CertifiedPolynomial input
  radicand : CertifiedPolynomial input
  r : CertifiedPolynomial input
  b : CertifiedPolynomial input
  t : CertifiedPolynomial input

private def weightedSelfCertifiedPolynomials (lower upper : ℚ)
    (input : Fin 18 → ℝ) (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (input i)) : WeightedSelfCertifiedPolynomials input :=
  let coefficient i := CertifiedPolynomial.constant
    (CertifiedCoefficient.atom input box hinput i)
  let rational q := CertifiedPolynomial.constant
    (CertifiedCoefficient.rational input q)
  let operations : WeightedSelfFormulaOperations (CertifiedPolynomial input) :=
    ⟨rational, CertifiedPolynomial.add, CertifiedPolynomial.neg,
      CertifiedPolynomial.mul, CertifiedPolynomial.pow⟩
  let x := CertifiedPolynomial.first input
  let y := CertifiedPolynomial.second input
  let z := CertifiedPolynomial.third input
  let sub p q := CertifiedPolynomial.add p (CertifiedPolynomial.neg q)
  let b := CertifiedPolynomial.add (rational lower)
    (CertifiedPolynomial.mul (rational (upper - lower)) y)
  let r := CertifiedPolynomial.add (sub (coefficient 0) b)
    (CertifiedPolynomial.mul
      (CertifiedPolynomial.add (sub (rational 1) (coefficient 0)) b) x)
  let t := CertifiedPolynomial.add (rational (-1))
    (CertifiedPolynomial.mul (rational 2) z)
  let formula := weightedSelfFormula operations coefficient r b t
  ⟨formula.p, formula.q, formula.radicand, r, b, t⟩

private def CertifiedPolynomial.sub {input : Fin 18 → ℝ}
    (p q : CertifiedPolynomial input) : CertifiedPolynomial input :=
  CertifiedPolynomial.add p (CertifiedPolynomial.neg q)

private def CertifiedPolynomial.square {input : Fin 18 → ℝ}
    (p : CertifiedPolynomial input) : CertifiedPolynomial input :=
  CertifiedPolynomial.mul p p

private def WeightedSelfCertifiedPolynomials.negativeP {input : Fin 18 → ℝ}
    (data : WeightedSelfCertifiedPolynomials input) : CertifiedPolynomial input :=
  CertifiedPolynomial.neg data.p

private def WeightedSelfCertifiedPolynomials.discriminant {input : Fin 18 → ℝ}
    (data : WeightedSelfCertifiedPolynomials input) : CertifiedPolynomial input :=
  CertifiedPolynomial.sub data.p.square
    (CertifiedPolynomial.mul data.q.square data.radicand)

private theorem WeightedSelfCertifiedPolynomials.negativeP_enclosure
    {input : Fin 18 → ℝ} (data : WeightedSelfCertifiedPolynomials input) :
    data.negativeP.enclosure = IntervalTrivariate.neg data.p.enclosure := rfl

private theorem WeightedSelfCertifiedPolynomials.discriminant_enclosure
    {input : Fin 18 → ℝ} (data : WeightedSelfCertifiedPolynomials input) :
    data.discriminant.enclosure = IntervalTrivariate.add
      (IntervalTrivariate.mul data.p.enclosure data.p.enclosure)
      (IntervalTrivariate.neg
        (IntervalTrivariate.mul
          (IntervalTrivariate.mul data.q.enclosure data.q.enclosure)
          data.radicand.enclosure)) := rfl

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
private theorem weightedSelfCertifiedPolynomials_fits (lower upper : ℚ)
    (input : Fin 18 → ℝ) (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (input i)) :
    let data := weightedSelfCertifiedPolynomials lower upper input box hinput
    data.negativeP.exact.Fits 12 12 4 ∧ data.q.exact.Fits 12 12 4 ∧
      data.discriminant.exact.Fits 12 12 4 := by
  simp (config := { maxSteps := 1000000 })
    [weightedSelfCertifiedPolynomials, weightedSelfFormula,
    WeightedSelfCertifiedPolynomials.negativeP,
    WeightedSelfCertifiedPolynomials.discriminant, CertifiedCoefficient.atom,
    CertifiedCoefficient.rational, CertifiedPolynomial.constant,
    CertifiedPolynomial.first, CertifiedPolynomial.second, CertifiedPolynomial.third,
    CertifiedPolynomial.add, CertifiedPolynomial.neg, CertifiedPolynomial.mul,
    CertifiedPolynomial.pow, CertifiedPolynomial.sub, CertifiedPolynomial.square,
    RadicalTrivariate.Fits, RadicalTrivariate.add, RadicalTrivariate.neg,
    RadicalTrivariate.mul, RadicalTrivariate.scaleSlice, RadicalTrivariate.constant,
    RadicalTrivariate.first, RadicalTrivariate.second, RadicalTrivariate.third,
    RadicalTrivariate.pow, RadicalBivariate.add, RadicalBivariate.neg,
    RadicalBivariate.mul, RadicalBivariate.scaleRow,
    RadicalUnivariate.add, RadicalUnivariate.neg, RadicalUnivariate.mul,
    RadicalUnivariate.scale]

private noncomputable def endpointCertificateInput : Fin 7 → ℝ
  | 0 => cStar
  | 1 => certifiedEndpointPair.2
  | 2 => endpointSecondDistance cStar certifiedEndpointPair.2
  | 3 => endpointFirstAuxiliaryDistance certifiedEndpointPair.2
  | 4 => endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2
  | 5 => endpointLambda
  | 6 => endpointMu

/-- Tight rational intervals for the seven exact endpoint quantities. -/
def weightedSelfEndpointBox : Fin 7 → RationalInterval
  | 0 => ⟨13866128436518096 / 10 ^ 16, 13866128436518100 / 10 ^ 16, by norm_num⟩
  | 1 => ⟨2873744161801659 / 10 ^ 15, 2873744161801662 / 10 ^ 15, by norm_num⟩
  | 2 => ⟨204381086361534 / 10 ^ 14, 204381086361536 / 10 ^ 14, by norm_num⟩
  | 3 => ⟨190504665395484 / 10 ^ 14, 190504665395485 / 10 ^ 14, by norm_num⟩
  | 4 => ⟨207245964946978 / 10 ^ 14, 207245964946981 / 10 ^ 14, by norm_num⟩
  | 5 => ⟨8947642540845 / 10 ^ 14, 8947642540925 / 10 ^ 14, by norm_num⟩
  | 6 => ⟨92883833887503 / 10 ^ 14, 92883833887577 / 10 ^ 14, by norm_num⟩

private theorem endpointCertificateInput_mem :
    ∀ i, (weightedSelfEndpointBox i).Contains (endpointCertificateInput i) := by
  intro i
  fin_cases i
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      ⟨cStar_mem_isolation_box.1.le, cStar_mem_isolation_box.2.le⟩
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      endpointB_tight_bounds
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      endpointSecondDistance_tight_bounds
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      endpointFirstAuxiliaryDistance_tight_bounds
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      endpointMixedAuxiliaryDistance_tight_bounds
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      endpointLambda_tight_bounds
  · simpa [weightedSelfEndpointBox, endpointCertificateInput, RationalInterval.Contains] using
      endpointMu_tight_bounds

/-- The eighteen exact coefficients in the reduced weighted-self formula. -/
noncomputable def weightedSelfCoefficientInput (upper : ℝ) : Fin 18 → ℝ := ![
  cStar,
  certifiedEndpointPair.2,
  endpointSecondDistance cStar certifiedEndpointPair.2,
  endpointFirstAuxiliaryDistance certifiedEndpointPair.2,
  endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2,
  endpointLambda,
  endpointMu,
  (1 + endpointLambda) / (2 * certifiedEndpointPair.2),
  (1 + endpointLambda) / (2 * certifiedEndpointPair.2) /
    (3 + certifiedEndpointPair.2) ^ 2,
  1 / (2 * endpointSecondDistance cStar certifiedEndpointPair.2),
  1 / (2 * endpointSecondDistance cStar certifiedEndpointPair.2) /
    (1 + 2 * upper + endpointSecondDistance cStar certifiedEndpointPair.2) ^ 2,
  endpointMu / (2 * endpointFirstAuxiliaryDistance certifiedEndpointPair.2),
  endpointMu / (2 * endpointFirstAuxiliaryDistance certifiedEndpointPair.2) /
    (2 + endpointFirstAuxiliaryDistance certifiedEndpointPair.2) ^ 2,
  endpointMu / (2 * endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2),
  endpointMu / (2 * endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2) /
    (2 + upper + endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2) ^ 2,
  weightedFirstPenalty cStar endpointLambda endpointMu,
  weightedSecondPenalty cStar endpointLambda endpointMu,
  weightedConstantTerm cStar endpointLambda endpointMu]

/-- Exact expressions for the eighteen coefficients on a radius bin. -/
def weightedSelfCoefficientExpression (upper : ℚ) : Fin 18 → RadicalExpression 7 := ![
  .var 0,
  .var 1,
  .var 2,
  .var 3,
  .var 4,
  .var 5,
  .var 6,
  RadicalExpression.div (.add (.constant 1) (.var 5)) (.mul (.constant 2) (.var 1)),
  RadicalExpression.div
      (RadicalExpression.div (.add (.constant 1) (.var 5))
        (.mul (.constant 2) (.var 1)))
      (RadicalExpression.pow (.add (.constant 3) (.var 1)) 2),
  RadicalExpression.div (.constant 1) (.mul (.constant 2) (.var 2)),
  RadicalExpression.div
      (RadicalExpression.div (.constant 1) (.mul (.constant 2) (.var 2)))
      (RadicalExpression.pow
        (.add (.add (.constant 1) (.constant (2 * upper))) (.var 2)) 2),
  RadicalExpression.div (.var 6) (.mul (.constant 2) (.var 3)),
  RadicalExpression.div
      (RadicalExpression.div (.var 6) (.mul (.constant 2) (.var 3)))
      (RadicalExpression.pow (.add (.constant 2) (.var 3)) 2),
  RadicalExpression.div (.var 6) (.mul (.constant 2) (.var 4)),
  RadicalExpression.div
      (RadicalExpression.div (.var 6) (.mul (.constant 2) (.var 4)))
      (RadicalExpression.pow
        (.add (.add (.constant 2) (.constant upper)) (.var 4)) 2),
  .mul (RadicalExpression.sub (.var 0) (.constant 1))
      (.add (.mul (.var 5) (.constant (1 / 2))) (.var 6)),
  .add (.mul (.mul (.add (.var 0) (.constant 1)) (.var 5))
      (.constant (1 / 2))) (.mul (.mul (.constant 3) (.var 0)) (.var 6)),
  .add
      (.add (.mul (.mul (.constant 2) (.var 0))
          (RadicalExpression.sub (.mul (.constant 2) (.var 0)) (.constant 1)))
        (.mul (.mul (.var 5) (.constant (1 / 2)))
          (.add (RadicalExpression.sub
            (.mul (.constant 3) (RadicalExpression.pow (.var 0) 2))
            (.mul (.constant 3) (.var 0))) (.constant 2))))
      (.mul (.var 6)
        (RadicalExpression.sub (RadicalExpression.pow (.var 0) 2) (.var 0)))]

private theorem weightedSelfCoefficientExpression_eval (upper : ℚ) :
    ∀ i, (weightedSelfCoefficientExpression upper i).eval endpointCertificateInput =
      weightedSelfCoefficientInput upper i := by
  intro i
  fin_cases i <;>
    simp [weightedSelfCoefficientExpression, weightedSelfCoefficientInput,
      endpointCertificateInput, RadicalExpression.div, RadicalExpression.sub,
      RadicalExpression.pow, RadicalExpression.eval,
      weightedFirstPenalty, weightedSecondPenalty, weightedConstantTerm, div_eq_mul_inv,
      pow_two]
  all_goals ring_nf
  all_goals simp

/-- Coefficient intervals obtained after supplying the two bin-dependent curvatures. -/
def weightedSelfCoefficientBox
    (kappaDBox kappaCBox : RationalInterval) : Fin 18 → RationalInterval := ![
  weightedSelfEndpointBox 0,
  weightedSelfEndpointBox 1,
  weightedSelfEndpointBox 2,
  weightedSelfEndpointBox 3,
  weightedSelfEndpointBox 4,
  weightedSelfEndpointBox 5,
  weightedSelfEndpointBox 6,
  ⟨189556961939 / 10 ^ 12, 189556961942 / 10 ^ 12, by norm_num⟩,
  ⟨5494266065 / 10 ^ 12, 5494266068 / 10 ^ 12, by norm_num⟩,
  ⟨244641032543 / 10 ^ 12, 244641032546 / 10 ^ 12, by norm_num⟩,
  kappaDBox,
  ⟨243783619929 / 10 ^ 12, 243783619933 / 10 ^ 12, by norm_num⟩,
  ⟨15986451260 / 10 ^ 12, 15986451263 / 10 ^ 12, by norm_num⟩,
  ⟨224090813808 / 10 ^ 12, 224090813812 / 10 ^ 12, by norm_num⟩,
  kappaCBox,
  ⟨376397199117 / 10 ^ 12, 376397199121 / 10 ^ 12, by norm_num⟩,
  ⟨39705903040 / 10 ^ 10, 39705903043 / 10 ^ 10, by norm_num⟩,
  ⟨55769153722 / 10 ^ 10, 55769153727 / 10 ^ 10, by norm_num⟩]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- The certified coefficient box contains every exact weighted-self coefficient. -/
theorem weightedSelfCoefficientInput_mem (upper : ℚ)
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression upper 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression upper 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true) :
    ∀ i, (weightedSelfCoefficientBox kappaDBox kappaCBox i).Contains
      (weightedSelfCoefficientInput upper i) := by
  intro i
  have heval := weightedSelfCoefficientExpression_eval upper i
  have hcertificate : (weightedSelfCoefficientExpression upper i).certifiesWithin
      weightedSelfEndpointBox (weightedSelfCoefficientBox kappaDBox kappaCBox i) = true := by
    fin_cases i
    case «10» =>
      exact hD
    case «14» =>
      exact hC
    all_goals
      norm_num [weightedSelfCoefficientExpression, weightedSelfCoefficientBox,
        weightedSelfEndpointBox, RadicalExpression.certifiesWithin,
        RadicalExpression.enclosure, RadicalExpression.div, RadicalExpression.sub,
        RadicalExpression.pow, RationalInterval.singleton,
        RationalInterval.add, RationalInterval.neg, RationalInterval.mul,
        RationalInterval.inv]
  have hsound := RadicalExpression.certifiesWithin_sound endpointCertificateInput_mem
    hcertificate
  rwa [heval] at hsound

private noncomputable def certificateSecondRadius (lower upper y : ℝ) : ℝ :=
  lower + (upper - lower) * y

private noncomputable def certificateFirstRadius (b x : ℝ) : ℝ :=
  cStar - b + (1 - cStar + b) * x

private noncomputable def certificateProjection (z : ℝ) : ℝ :=
  -1 + 2 * z

private noncomputable def certificatePolynomialPLegacyAtoms
    (a : Fin 18 → ℝ) (r b t : ℝ) : ℝ :=
  let c := a 0
  let B := a 1
  let D := a 2
  let A := a 3
  let C := a 4
  let lambda := a 5
  let mu := a 6
  let k := chordInnerProduct c r b
  let R := chordProjectionRadicand c r b t
  let qB := 1 + 4 * r ^ 2 - 4 * r * t
  let qA := 1 + r ^ 2 - 2 * r * t
  let uD := r * (1 + 4 * b ^ 2 - D ^ 2) - 4 * k * t
  let uC := r * (1 + r ^ 2 + b ^ 2 + 2 * k - 2 * r * t - C ^ 2) -
    2 * k * t
  let FB := a 7 * qB + (1 + lambda) * B / 2 - a 8 * (qB - B ^ 2) ^ 2
  let FA := a 11 * qA + mu * A / 2 - a 12 * (qA - A ^ 2) ^ 2
  let FD := a 9 * (D ^ 2 * r ^ 2 + r * uD) + D / 2 * r ^ 2 - a 10 * uD ^ 2
  let FC := a 13 * (C ^ 2 * r ^ 2 + r * uC) + mu * C / 2 * r ^ 2 - a 14 * uC ^ 2
  r ^ 2 * (FB + FA - a 15 * r - a 16 * b - a 17) +
    FD + FC - 16 * a 10 * R - 4 * a 14 * R

private noncomputable def certificatePolynomialQLegacyAtoms
    (a : Fin 18 → ℝ) (r b t : ℝ) : ℝ :=
  let c := a 0
  let D := a 2
  let C := a 4
  let k := chordInnerProduct c r b
  let uD := r * (1 + 4 * b ^ 2 - D ^ 2) - 4 * k * t
  let uC := r * (1 + r ^ 2 + b ^ 2 + 2 * k - 2 * r * t - C ^ 2) -
    2 * k * t
  4 * (a 9 * r - 2 * a 10 * uD) + 2 * (a 13 * r - 2 * a 14 * uC)

private noncomputable def certificatePolynomialPLegacy (r b t upper : ℝ) : ℝ :=
  certificatePolynomialPLegacyAtoms (weightedSelfCoefficientInput upper) r b t

private noncomputable def certificatePolynomialQLegacy (r b t upper : ℝ) : ℝ :=
  certificatePolynomialQLegacyAtoms (weightedSelfCoefficientInput upper) r b t

/-- The five scalar operations used to evaluate the reduced formula over the reals. -/
def weightedSelfRealFormulaOperations : WeightedSelfFormulaOperations ℝ :=
  ⟨fun q ↦ q, fun a b ↦ a + b, fun a ↦ -a,
    fun a b ↦ a * b, fun a n ↦ a ^ n⟩

/-- The fixed reduced formula evaluated at its exact real coefficients. -/
noncomputable def weightedSelfRealFormula (r b t upper : ℝ) : WeightedSelfFormula ℝ :=
  weightedSelfFormula weightedSelfRealFormulaOperations
    (weightedSelfCoefficientInput upper) r b t

private noncomputable def certificatePolynomialP (r b t upper : ℝ) : ℝ :=
  (weightedSelfRealFormula r b t upper).p

private noncomputable def certificatePolynomialQ (r b t upper : ℝ) : ℝ :=
  (weightedSelfRealFormula r b t upper).q

private theorem weightedSelfFormula_certified_values (input : Fin 18 → ℝ)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (input i))
    (r b t : CertifiedPolynomial input) (x y z : ℝ) :
    let coefficient i := CertifiedPolynomial.constant
      (CertifiedCoefficient.atom input box hinput i)
    let rational q := CertifiedPolynomial.constant
      (CertifiedCoefficient.rational input q)
    let operations : WeightedSelfFormulaOperations (CertifiedPolynomial input) :=
      ⟨rational, CertifiedPolynomial.add, CertifiedPolynomial.neg,
        CertifiedPolynomial.mul, CertifiedPolynomial.pow⟩
    let certified := weightedSelfFormula operations coefficient r b t
    let value := weightedSelfFormula weightedSelfRealFormulaOperations input
      (r.value x y z) (b.value x y z) (t.value x y z)
    certified.p.value x y z = value.p ∧ certified.q.value x y z = value.q ∧
      certified.radicand.value x y z = value.radicand := by
  constructor
  · rfl
  constructor <;> rfl

private theorem weightedSelfCertified_chart_values (lower upper : ℚ)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (x y z : ℝ) :
    let data := weightedSelfCertifiedPolynomials lower upper
      (weightedSelfCoefficientInput upper) box hinput
    data.r.value x y z =
        certificateFirstRadius (certificateSecondRadius lower upper y) x ∧
      data.b.value x y z = certificateSecondRadius lower upper y ∧
      data.t.value x y z = certificateProjection z := by
  simp only [weightedSelfCertifiedPolynomials, CertifiedCoefficient.atom,
    CertifiedCoefficient.rational, CertifiedPolynomial.constant, CertifiedPolynomial.first,
    CertifiedPolynomial.second, CertifiedPolynomial.third, CertifiedPolynomial.add,
    CertifiedPolynomial.neg, CertifiedPolynomial.mul, certificateFirstRadius,
    certificateSecondRadius, certificateProjection, weightedSelfCoefficientInput]
  push_cast
  constructor
  · ring
  constructor <;> ring

private theorem weightedSelfCertified_formula_values (lower upper : ℚ)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (x y z : ℝ) :
    let data := weightedSelfCertifiedPolynomials lower upper
      (weightedSelfCoefficientInput upper) box hinput
    data.p.value x y z = certificatePolynomialP
        (data.r.value x y z) (data.b.value x y z) (data.t.value x y z) upper ∧
      data.q.value x y z = certificatePolynomialQ
        (data.r.value x y z) (data.b.value x y z) (data.t.value x y z) upper ∧
      data.radicand.value x y z =
        (weightedSelfRealFormula (data.r.value x y z) (data.b.value x y z)
          (data.t.value x y z) upper).radicand := by
  simpa only [weightedSelfCertifiedPolynomials, certificatePolynomialP,
    certificatePolynomialQ, weightedSelfRealFormula] using
    weightedSelfFormula_certified_values (weightedSelfCoefficientInput upper)
      box hinput
      (weightedSelfCertifiedPolynomials lower upper (weightedSelfCoefficientInput upper)
        box hinput).r
      (weightedSelfCertifiedPolynomials lower upper (weightedSelfCoefficientInput upper)
        box hinput).b
      (weightedSelfCertifiedPolynomials lower upper (weightedSelfCoefficientInput upper)
        box hinput).t x y z

private theorem certificateFormula_radicand (r b t upper : ℝ) :
    (weightedSelfRealFormula r b t upper).radicand =
      chordProjectionRadicand cStar r b t := by
  simp [weightedSelfRealFormula, weightedSelfFormula, weightedSelfRealFormulaOperations,
    weightedSelfCoefficientInput, chordProjectionRadicand, chordInnerProduct]
  ring

set_option maxHeartbeats 2000000 in
private theorem certificateLegacyPolynomials_eq_weightedSelf
    (r b t upper : ℝ) (hr : r ≠ 0) :
    certificatePolynomialPLegacy r b t upper = weightedSelfPolynomialP r b t upper ∧
      certificatePolynomialQLegacy r b t upper = weightedSelfPolynomialQ r b t upper := by
  have hB : certifiedEndpointPair.2 ≠ 0 := by
    linarith [endpointB_tight_bounds.1]
  have hD : endpointSecondDistance cStar certifiedEndpointPair.2 ≠ 0 := by
    linarith [endpointSecondDistance_tight_bounds.1]
  have hA : endpointFirstAuxiliaryDistance certifiedEndpointPair.2 ≠ 0 := by
    linarith [endpointFirstAuxiliaryDistance_tight_bounds.1]
  have hC : endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2 ≠ 0 := by
    linarith [endpointMixedAuxiliaryDistance_tight_bounds.1]
  simp only [certificatePolynomialPLegacy, certificatePolynomialQLegacy,
    certificatePolynomialPLegacyAtoms, certificatePolynomialQLegacyAtoms,
    weightedSelfCoefficientInput, weightedSelfPolynomialP, weightedSelfPolynomialQ,
    weightedSelfCoordinateExpression, quarticNormTangent, chordProjectionRadicand,
    chordInnerProduct]
  simp
  field_simp [hr, hB, hD, hA, hC]
  constructor <;> ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
private theorem certificatePolynomials_eq_legacy (r b t upper : ℝ) :
    certificatePolynomialP r b t upper = certificatePolynomialPLegacy r b t upper ∧
      certificatePolynomialQ r b t upper = certificatePolynomialQLegacy r b t upper := by
  simp only [certificatePolynomialP, certificatePolynomialQ, weightedSelfRealFormula,
    weightedSelfFormula, weightedSelfRealFormulaOperations, certificatePolynomialPLegacy,
    certificatePolynomialQLegacy, certificatePolynomialPLegacyAtoms,
    certificatePolynomialQLegacyAtoms, chordInnerProduct, chordProjectionRadicand]
  constructor <;> ring

private theorem certificatePolynomials_eq_weightedSelf (r b t upper : ℝ)
    (hr : r ≠ 0) :
    certificatePolynomialP r b t upper = weightedSelfPolynomialP r b t upper ∧
      certificatePolynomialQ r b t upper = weightedSelfPolynomialQ r b t upper := by
  obtain ⟨hp, hq⟩ := certificatePolynomials_eq_legacy r b t upper
  obtain ⟨hp', hq'⟩ := certificateLegacyPolynomials_eq_weightedSelf r b t upper hr
  exact ⟨hp.trans hp', hq.trans hq'⟩

/-- The fixed real formula computes the two reduced polynomials and their Gram radicand. -/
theorem weightedSelfRealFormula_eq_weightedSelf (r b t upper : ℝ) (hr : r ≠ 0) :
    (weightedSelfRealFormula r b t upper).p =
        weightedSelfPolynomialP r b t upper ∧
      (weightedSelfRealFormula r b t upper).q =
        weightedSelfPolynomialQ r b t upper ∧
      (weightedSelfRealFormula r b t upper).radicand =
        chordProjectionRadicand cStar r b t := by
  obtain ⟨hp, hq⟩ := certificatePolynomials_eq_weightedSelf r b t upper hr
  exact ⟨hp, hq, certificateFormula_radicand r b t upper⟩

private theorem weightedSelfCertifiedValues_eval (lower upper : ℚ)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (x y z : ℝ)
    (hr : certificateFirstRadius (certificateSecondRadius lower upper y) x ≠ 0) :
    let data := weightedSelfCertifiedPolynomials lower upper
      (weightedSelfCoefficientInput upper) box hinput
    let b := certificateSecondRadius lower upper y
    let r := certificateFirstRadius b x
    let t := certificateProjection z
    data.p.value x y z = weightedSelfPolynomialP r b t upper ∧
      data.q.value x y z = weightedSelfPolynomialQ r b t upper ∧
      data.radicand.value x y z = chordProjectionRadicand cStar r b t := by
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  change data.p.value x y z = _ ∧ data.q.value x y z = _ ∧
    data.radicand.value x y z = _
  obtain ⟨hp, hq, hR⟩ :=
    weightedSelfCertified_formula_values lower upper box hinput x y z
  obtain ⟨hrValue, hbValue, htValue⟩ :=
    weightedSelfCertified_chart_values lower upper box hinput x y z
  rw [hrValue, hbValue, htValue] at hp hq hR
  obtain ⟨hpFormula, hqFormula⟩ := certificatePolynomials_eq_weightedSelf
    (certificateFirstRadius (certificateSecondRadius lower upper y) x)
    (certificateSecondRadius lower upper y) (certificateProjection z) upper hr
  exact ⟨hp.trans hpFormula, hq.trans hqFormula,
    hR.trans (certificateFormula_radicand _ _ _ _)⟩

private theorem weightedSelfCertifiedDiscriminant_value (lower upper : ℚ)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (x y z : ℝ)
    (hr : certificateFirstRadius (certificateSecondRadius lower upper y) x ≠ 0) :
    let data := weightedSelfCertifiedPolynomials lower upper
      (weightedSelfCoefficientInput upper) box hinput
    data.discriminant.value x y z =
      weightedSelfDiscriminant
        (certificateFirstRadius (certificateSecondRadius lower upper y) x)
        (certificateSecondRadius lower upper y) (certificateProjection z) upper := by
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  change data.discriminant.value x y z = _
  simp only [WeightedSelfCertifiedPolynomials.discriminant, CertifiedPolynomial.sub,
    CertifiedPolynomial.square, CertifiedPolynomial.add, CertifiedPolynomial.neg,
    CertifiedPolynomial.mul]
  rw [weightedSelfDiscriminant]
  obtain ⟨hp, hq, hR⟩ :=
    weightedSelfCertifiedValues_eval lower upper box hinput x y z hr
  rw [hp, hq, hR]
  ring

private theorem exists_firstRadius_chart {r b : ℝ}
    (hb : cStar - 1 ≤ b) (hrLower : cStar - b ≤ r) (hrUpper : r ≤ 1) :
    ∃ x : I, certificateFirstRadius b x = r := by
  have hden : 0 ≤ 1 - cStar + b := by linarith
  by_cases hzero : 1 - cStar + b = 0
  · have hr : r = 1 := by linarith
    refine ⟨⟨0, by constructor <;> norm_num⟩, ?_⟩
    simp [certificateFirstRadius, hzero, hr]
    linarith
  · have hdenPos : 0 < 1 - cStar + b := lt_of_le_of_ne hden (Ne.symm hzero)
    let x : ℝ := (r - (cStar - b)) / (1 - cStar + b)
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hrLower) hden
      · rw [div_le_one hdenPos]
        linarith
    refine ⟨⟨x, hx⟩, ?_⟩
    dsimp [x, certificateFirstRadius]
    field_simp [hzero]
    ring

private theorem exists_secondRadius_chart {lower upper b : ℝ}
    (hwidth : lower < upper) (hbLower : lower ≤ b) (hbUpper : b ≤ upper) :
    ∃ y : I, certificateSecondRadius lower upper y = b := by
  have hden : 0 < upper - lower := sub_pos.mpr hwidth
  let y : ℝ := (b - lower) / (upper - lower)
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hbLower) hden.le
    · rw [div_le_one hden]
      linarith
  refine ⟨⟨y, hy⟩, ?_⟩
  dsimp [y, certificateSecondRadius]
  field_simp [hden.ne']
  ring

private theorem exists_projection_chart {t : ℝ} (htLower : -1 ≤ t) (htUpper : t ≤ 1) :
    ∃ z : I, certificateProjection z = t := by
  let z : ℝ := (t + 1) / 2
  have hz : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [z] <;> linarith
  refine ⟨⟨z, hz⟩, ?_⟩
  dsimp [z, certificateProjection]
  ring

set_option maxHeartbeats 10000000 in
private theorem radiusBinBound_of_cube_signs (lower upper : ℚ)
    (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (hnegativeP :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      ∀ x y z : I,
        0 ≤ data.negativeP.exact.eval (weightedSelfCoefficientInput upper) x y z)
    (hq :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      ∀ x y z : I, 0 ≤ data.q.exact.eval (weightedSelfCoefficientInput upper) x y z)
    (hdiscriminant :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      ∀ x y z : I,
        0 ≤ data.discriminant.exact.eval (weightedSelfCoefficientInput upper) x y z) :
    WeightedSelfRadiusBinBound lower upper := by
  intro r b t hbLower hbUpper hrLower hrUpper htLower htUpper
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hbPhysical : cStar - 1 ≤ b := by linarith
  obtain ⟨x, hx⟩ := exists_firstRadius_chart hbPhysical hrLower hrUpper
  obtain ⟨y, hy⟩ := exists_secondRadius_chart hwidth hbLower hbUpper
  obtain ⟨z, hz⟩ := exists_projection_chart htLower htUpper
  have hnegativePValue :
      0 ≤ data.negativeP.exact.eval (weightedSelfCoefficientInput upper) x y z :=
    hnegativeP x y z
  have hqValue : 0 ≤ data.q.exact.eval (weightedSelfCoefficientInput upper) x y z :=
    hq x y z
  have hdiscriminantValue :
      0 ≤ data.discriminant.exact.eval (weightedSelfCoefficientInput upper) x y z :=
    hdiscriminant x y z
  have hrPos : 0 < r := by
    have hc := one_lt_cStar_and_cStar_lt_two.1
    linarith
  have hchartR :
      certificateFirstRadius (certificateSecondRadius lower upper y) x = r := by
    rw [hy, hx]
  obtain ⟨hpValue, hqValue', hRValue⟩ :=
    weightedSelfCertifiedValues_eval lower upper box hinput x y z
      (by rw [hchartR]; exact hrPos.ne')
  have hdiscriminantValue' :=
    weightedSelfCertifiedDiscriminant_value lower upper box hinput x y z
      (by rw [hchartR]; exact hrPos.ne')
  rw [data.negativeP.evaluates] at hnegativePValue
  rw [data.q.evaluates] at hqValue
  rw [data.discriminant.evaluates] at hdiscriminantValue
  rw [hchartR, hy, hz] at hpValue hqValue' hRValue hdiscriminantValue'
  have hp : weightedSelfPolynomialP r b t upper ≤ 0 := by
    change 0 ≤ -data.p.value x y z at hnegativePValue
    rw [hpValue] at hnegativePValue
    linarith
  rw [hqValue'] at hqValue
  rw [hdiscriminantValue'] at hdiscriminantValue
  exact weightedSelfCoordinateMajorant_nonpos_of_polynomial_signs hrPos
    (chordProjectionRadicand_nonneg_of_bounds hrLower hrUpper (hbUpper.trans hupper)
      htLower htUpper)
    hp hqValue hdiscriminantValue

set_option maxHeartbeats 10000000 in
private theorem radiusBinBound_of_certificates (lower upper : ℚ)
    (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (negativePTree qTree discriminantTree : TensorSubdivision)
    (hnegativeP :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalTensorSubdivisionCertifiesNonnegative negativePTree
        data.negativeP.enclosure.bernsteinCoefficients = true)
    (hq :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalTensorSubdivisionCertifiesNonnegative qTree
        data.q.enclosure.bernsteinCoefficients = true)
    (hdiscriminant :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalTensorSubdivisionCertifiesNonnegative discriminantTree
        data.discriminant.enclosure.bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound lower upper := by
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hfits := weightedSelfCertifiedPolynomials_fits lower upper
    (weightedSelfCoefficientInput upper) box hinput
  apply radiusBinBound_of_cube_signs lower upper hwidth hupper box hinput
  · exact data.negativeP.exact.nonneg_of_interval_bernstein_certificate hfits.1
      data.negativeP.enclosure (weightedSelfCoefficientInput upper)
      data.negativeP.valid negativePTree hnegativeP
  · exact data.q.exact.nonneg_of_interval_bernstein_certificate hfits.2.1
      data.q.enclosure (weightedSelfCoefficientInput upper)
      data.q.valid qTree hq
  · exact data.discriminant.exact.nonneg_of_interval_bernstein_certificate hfits.2.2
      data.discriminant.enclosure (weightedSelfCoefficientInput upper)
      data.discriminant.valid discriminantTree hdiscriminant

set_option maxHeartbeats 10000000 in
private theorem radiusBinBound_of_horner_bernstein_certificates_with_q_sign
    (lower upper : ℚ)
    (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (negativePTree discriminantTree : TensorSubdivision)
    (hnegativeP :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
        data.negativeP.enclosure .unit .unit .unit = true)
    (hq :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      ∀ x y z : I, 0 ≤ data.q.exact.eval (weightedSelfCoefficientInput upper) x y z)
    (hdiscriminant :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalTensorSubdivisionCertifiesNonnegative discriminantTree
        data.discriminant.enclosure.bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound lower upper := by
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hfits := weightedSelfCertifiedPolynomials_fits lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hunit (x : I) : RationalInterval.unit.Contains (x : ℝ) := by
    simpa only [RationalInterval.unit, RationalInterval.Contains, Rat.cast_zero,
      Rat.cast_one, Set.mem_Icc] using x.property
  apply radiusBinBound_of_cube_signs lower upper hwidth hupper box hinput
  · change ∀ x y z : I,
      0 ≤ data.negativeP.exact.eval (weightedSelfCoefficientInput upper) x y z
    intro x y z
    exact data.negativeP.exact.nonneg_of_interval_box_certificate data.negativeP.enclosure
      (weightedSelfCoefficientInput upper) data.negativeP.valid negativePTree hnegativeP
      (hunit x) (hunit y) (hunit z)
  · change ∀ x y z : I, 0 ≤ data.q.exact.eval (weightedSelfCoefficientInput upper) x y z
    exact hq
  · exact data.discriminant.exact.nonneg_of_interval_bernstein_certificate hfits.2.2
      data.discriminant.enclosure (weightedSelfCoefficientInput upper)
      data.discriminant.valid discriminantTree hdiscriminant

set_option maxHeartbeats 10000000 in
private theorem radiusBinBound_of_horner_bernstein_certificates (lower upper : ℚ)
    (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i))
    (negativePTree qTree discriminantTree : TensorSubdivision)
    (hnegativeP :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
        data.negativeP.enclosure .unit .unit .unit = true)
    (hq :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalPolynomialSubdivisionCertifiesNonnegative qTree
        data.q.enclosure .unit .unit .unit = true)
    (hdiscriminant :
      let data := weightedSelfCertifiedPolynomials lower upper
        (weightedSelfCoefficientInput upper) box hinput
      intervalTensorSubdivisionCertifiesNonnegative discriminantTree
        data.discriminant.enclosure.bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound lower upper := by
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hunit (x : I) : RationalInterval.unit.Contains (x : ℝ) := by
    simpa only [RationalInterval.unit, RationalInterval.Contains, Rat.cast_zero,
      Rat.cast_one, Set.mem_Icc] using x.property
  apply radiusBinBound_of_horner_bernstein_certificates_with_q_sign lower upper hwidth hupper
    box hinput negativePTree discriminantTree hnegativeP
  · change ∀ x y z : I, 0 ≤ data.q.exact.eval (weightedSelfCoefficientInput upper) x y z
    intro x y z
    exact data.q.exact.nonneg_of_interval_box_certificate data.q.enclosure
      (weightedSelfCoefficientInput upper) data.q.valid qTree hq
      (hunit x) (hunit y) (hunit z)
  · exact hdiscriminant

/-- Rational interval operations on dense trivariate polynomials. -/
def intervalPolynomialOperations :
    WeightedSelfFormulaOperations IntervalTrivariate :=
  ⟨fun q ↦ .constant (.singleton q), IntervalTrivariate.add,
    IntervalTrivariate.neg, IntervalTrivariate.mul, IntervalTrivariate.pow⟩

/-- The affine unit-cube chart for one second-radius bin. -/
def weightedSelfIntervalChart (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : WeightedSelfChart IntervalTrivariate :=
  let coefficient i := IntervalTrivariate.constant (box i)
  let rational q := IntervalTrivariate.constant (RationalInterval.singleton q)
  let sub p q := IntervalTrivariate.add p (IntervalTrivariate.neg q)
  let b := IntervalTrivariate.add (rational lower)
    (IntervalTrivariate.mul (rational (upper - lower)) .second)
  let r := IntervalTrivariate.add (sub (coefficient 0) b)
    (IntervalTrivariate.mul
      (IntervalTrivariate.add (sub (rational 1) (coefficient 0)) b) .first)
  let t := IntervalTrivariate.add (rational (-1))
    (IntervalTrivariate.mul (rational 2) .third)
  ⟨r, b, t⟩

/-- The interval-coefficient reduced formula on one affine radius chart. -/
def weightedSelfIntervalFormula (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : WeightedSelfFormula IntervalTrivariate :=
  let chart := weightedSelfIntervalChart lower upper box
  weightedSelfFormula intervalPolynomialOperations
    (fun i ↦ .constant (box i)) chart.r chart.b chart.t

/-- The interval enclosure of `-P` in the reduced weighted-self formula. -/
def weightedSelfNegativePIntervalPolynomial (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  IntervalTrivariate.neg (weightedSelfIntervalFormula lower upper box).p

/-- The interval enclosure of `Q` in the reduced weighted-self formula. -/
def weightedSelfQIntervalPolynomial (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  (weightedSelfIntervalFormula lower upper box).q

/-- The interval enclosure of `P² - Q²R` in the reduced weighted-self formula. -/
def weightedSelfDiscriminantIntervalPolynomial (lower upper : ℚ)
    (box : Fin 18 → RationalInterval) : IntervalTrivariate :=
  let formula := weightedSelfIntervalFormula lower upper box
  IntervalTrivariate.add
    (IntervalTrivariate.mul formula.p formula.p)
    (IntervalTrivariate.neg
      (IntervalTrivariate.mul
        (IntervalTrivariate.mul formula.q formula.q) formula.radicand))

private theorem weightedSelfCertified_enclosures (lower upper : ℚ)
    (box : Fin 18 → RationalInterval)
    (hinput : ∀ i, (box i).Contains (weightedSelfCoefficientInput upper i)) :
    let data := weightedSelfCertifiedPolynomials lower upper
      (weightedSelfCoefficientInput upper) box hinput
    let value := weightedSelfIntervalFormula lower upper box
    data.p.enclosure = value.p ∧ data.q.enclosure = value.q ∧
      data.radicand.enclosure = value.radicand := by
  let input := weightedSelfCoefficientInput upper
  let data := weightedSelfCertifiedPolynomials lower upper input box hinput
  let coefficient i := CertifiedPolynomial.constant
    (CertifiedCoefficient.atom input box hinput i)
  let rational q := CertifiedPolynomial.constant (CertifiedCoefficient.rational input q)
  let operations : WeightedSelfFormulaOperations (CertifiedPolynomial input) :=
    ⟨rational, CertifiedPolynomial.add, CertifiedPolynomial.neg,
      CertifiedPolynomial.mul, CertifiedPolynomial.pow⟩
  have hmap := weightedSelfFormula_map operations intervalPolynomialOperations
    CertifiedPolynomial.enclosure (fun q ↦ rfl) (fun a b ↦ rfl) (fun a ↦ rfl)
    (fun a b ↦ rfl) (fun a n ↦ rfl) coefficient data.r data.b data.t
  have hr : data.r.enclosure = (weightedSelfIntervalChart lower upper box).r := by
    rfl
  have hb : data.b.enclosure = (weightedSelfIntervalChart lower upper box).b := by
    rfl
  have ht : data.t.enclosure = (weightedSelfIntervalChart lower upper box).t := by
    rfl
  have hcoefficient : CertifiedPolynomial.enclosure ∘ coefficient =
      fun i ↦ IntervalTrivariate.constant (box i) := by
    funext i
    rfl
  have hp : (weightedSelfFormula operations coefficient data.r data.b data.t).p = data.p := by
    rfl
  have hq : (weightedSelfFormula operations coefficient data.r data.b data.t).q = data.q := by
    rfl
  have hR : (weightedSelfFormula operations coefficient data.r data.b data.t).radicand =
      data.radicand := by
    rfl
  dsimp only at hmap
  rw [hp, hq, hR, hcoefficient, hr, hb, ht] at hmap
  change data.p.enclosure = (weightedSelfIntervalFormula lower upper box).p ∧
    data.q.enclosure = (weightedSelfIntervalFormula lower upper box).q ∧
    data.radicand.enclosure = (weightedSelfIntervalFormula lower upper box).radicand
  simpa only [weightedSelfIntervalFormula] using hmap

/-- Exact interval Bernstein certificates imply the weighted-self estimate on one radius bin. -/
theorem weightedSelfRadiusBinBound_of_interval_certificates
    (lower upper : ℚ) (hwidth : (lower : ℝ) < upper)
    (hupper : (upper : ℝ) ≤ 1)
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression upper 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression upper 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (negativePTree qTree discriminantTree : TensorSubdivision)
    (hnegativeP : intervalTensorSubdivisionCertifiesNonnegative negativePTree
      (weightedSelfNegativePIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true)
    (hq : intervalTensorSubdivisionCertifiesNonnegative qTree
      (weightedSelfQIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true)
    (hdiscriminant : intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      (weightedSelfDiscriminantIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound lower upper := by
  let box := weightedSelfCoefficientBox kappaDBox kappaCBox
  have hinput := weightedSelfCoefficientInput_mem upper kappaDBox kappaCBox hD hC
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hformula := weightedSelfCertified_enclosures lower upper box hinput
  apply radiusBinBound_of_certificates lower upper hwidth hupper box hinput
    negativePTree qTree discriminantTree
  · change intervalTensorSubdivisionCertifiesNonnegative negativePTree
      data.negativeP.enclosure.bernsteinCoefficients = true
    rw [WeightedSelfCertifiedPolynomials.negativeP_enclosure, hformula.1]
    simpa only [weightedSelfNegativePIntervalPolynomial, box] using hnegativeP
  · change intervalTensorSubdivisionCertifiesNonnegative qTree
      data.q.enclosure.bernsteinCoefficients = true
    rw [hformula.2.1]
    simpa only [weightedSelfQIntervalPolynomial, box] using hq
  · change intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      data.discriminant.enclosure.bernsteinCoefficients = true
    rw [WeightedSelfCertifiedPolynomials.discriminant_enclosure,
      hformula.1, hformula.2.1, hformula.2.2]
    simpa only [weightedSelfDiscriminantIntervalPolynomial, box] using hdiscriminant

set_option maxHeartbeats 5000000 in
/-- Horner checks for `-P`, a pointwise proof of `Q ≥ 0`, and a Bernstein discriminant
check imply the weighted-self estimate on one radius bin. -/
theorem weightedSelfRadiusBinBound_of_horner_bernstein_and_q_sign
    (lower upper : ℚ) (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression upper 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression upper 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (negativePTree discriminantTree : TensorSubdivision)
    (hnegativeP : intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
      (weightedSelfNegativePIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      .unit .unit .unit = true)
    (hq : ∀ x y z : I,
      0 ≤ weightedSelfPolynomialQ (weightedSelfRealChart lower upper x y z).r
        (weightedSelfRealChart lower upper x y z).b
        (weightedSelfRealChart lower upper x y z).t upper)
    (hdiscriminant : intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      (weightedSelfDiscriminantIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound lower upper := by
  let box := weightedSelfCoefficientBox kappaDBox kappaCBox
  have hinput := weightedSelfCoefficientInput_mem upper kappaDBox kappaCBox hD hC
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hformula := weightedSelfCertified_enclosures lower upper box hinput
  apply radiusBinBound_of_horner_bernstein_certificates_with_q_sign lower upper hwidth hupper
    box hinput negativePTree discriminantTree
  · change intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
      data.negativeP.enclosure .unit .unit .unit = true
    rw [WeightedSelfCertifiedPolynomials.negativeP_enclosure, hformula.1]
    simpa only [weightedSelfNegativePIntervalPolynomial, box] using hnegativeP
  · change ∀ x y z : I, 0 ≤ data.q.exact.eval (weightedSelfCoefficientInput upper) x y z
    intro x y z
    have hr : certificateFirstRadius (certificateSecondRadius lower upper y) x ≠ 0 := by
      apply ne_of_gt
      simpa only [weightedSelfRealChart, certificateFirstRadius, certificateSecondRadius,
        Rat.cast_sub, Rat.cast_one] using
        weightedSelfRealChart_first_pos (z := (z : ℝ)) hwidth.le hupper x.property y.property
    rw [data.q.evaluates]
    have hvalues := weightedSelfCertifiedValues_eval lower upper box hinput x y z hr
    rw [hvalues.2.1]
    simpa only [weightedSelfRealChart, certificateFirstRadius, certificateSecondRadius,
      certificateProjection, Rat.cast_sub, Rat.cast_one] using hq x y z
  · change intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      data.discriminant.enclosure.bernsteinCoefficients = true
    rw [WeightedSelfCertifiedPolynomials.discriminant_enclosure,
      hformula.1, hformula.2.1, hformula.2.2]
    simpa only [weightedSelfDiscriminantIntervalPolynomial, box] using hdiscriminant

set_option maxHeartbeats 5000000 in
/-- Interval-Horner checks for `-P` and `Q`, together with a Bernstein discriminant check,
imply the weighted-self estimate on one radius bin. -/
theorem weightedSelfRadiusBinBound_of_horner_bernstein_certificates
    (lower upper : ℚ) (hwidth : (lower : ℝ) < upper) (hupper : (upper : ℝ) ≤ 1)
    (kappaDBox kappaCBox : RationalInterval)
    (hD : (weightedSelfCoefficientExpression upper 10).certifiesWithin
      weightedSelfEndpointBox kappaDBox = true)
    (hC : (weightedSelfCoefficientExpression upper 14).certifiesWithin
      weightedSelfEndpointBox kappaCBox = true)
    (negativePTree qTree discriminantTree : TensorSubdivision)
    (hnegativeP : intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
      (weightedSelfNegativePIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      .unit .unit .unit = true)
    (hq : intervalPolynomialSubdivisionCertifiesNonnegative qTree
      (weightedSelfQIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox))
      .unit .unit .unit = true)
    (hdiscriminant : intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      (weightedSelfDiscriminantIntervalPolynomial lower upper
        (weightedSelfCoefficientBox kappaDBox kappaCBox)).bernsteinCoefficients = true) :
    WeightedSelfRadiusBinBound lower upper := by
  let box := weightedSelfCoefficientBox kappaDBox kappaCBox
  have hinput := weightedSelfCoefficientInput_mem upper kappaDBox kappaCBox hD hC
  let data := weightedSelfCertifiedPolynomials lower upper
    (weightedSelfCoefficientInput upper) box hinput
  have hformula := weightedSelfCertified_enclosures lower upper box hinput
  apply radiusBinBound_of_horner_bernstein_certificates lower upper hwidth hupper box hinput
    negativePTree qTree discriminantTree
  · change intervalPolynomialSubdivisionCertifiesNonnegative negativePTree
      data.negativeP.enclosure .unit .unit .unit = true
    rw [WeightedSelfCertifiedPolynomials.negativeP_enclosure, hformula.1]
    simpa only [weightedSelfNegativePIntervalPolynomial, box] using hnegativeP
  · change intervalPolynomialSubdivisionCertifiesNonnegative qTree
      data.q.enclosure .unit .unit .unit = true
    rw [hformula.2.1]
    simpa only [weightedSelfQIntervalPolynomial, box] using hq
  · change intervalTensorSubdivisionCertifiesNonnegative discriminantTree
      data.discriminant.enclosure.bernsteinCoefficients = true
    rw [WeightedSelfCertifiedPolynomials.discriminant_enclosure,
      hformula.1, hformula.2.1, hformula.2.2]
    simpa only [weightedSelfDiscriminantIntervalPolynomial, box] using hdiscriminant

end Bescovitch

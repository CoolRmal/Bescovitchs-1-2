/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.EndpointWeights

/-!
# Tight endpoint bounds

This file gives narrow exact rational enclosures for the scalar data used in the sharp analytic
certificates.
-/

@[expose] public section

noncomputable section

namespace Bescovitch

private abbrev RE := RadicalExpression 2

private def reSub (f g : RE) : RE := .add f (.neg g)

private def reDiv (f g : RE) : RE := .mul f (.inv g)

private def tightC : RE := .var 0

private def tightB : RE := .var 1

private def tightD : RE :=
  reSub (reSub (.mul (.constant 4) (.mul tightC tightC)) (.mul (.constant 2) tightC)) tightB

private def tightOuterRadius : RE :=
  reDiv
    (reSub
      (.add (reSub (.mul (.constant 2) tightB)
        (.mul (.constant 3) (.mul tightC tightC))) (.mul (.constant 2) tightC))
      (.constant 1))
    (.add tightC (.constant 1))

private def tightInput : Fin 2 → ℝ
  | 0 => cStar
  | 1 => certifiedEndpointPair.2

private def tightInputBox : Fin 2 → RationalInterval
  | 0 => ⟨13866128436518096 / 10 ^ 16, 13866128436518100 / 10 ^ 16, by norm_num⟩
  | 1 => ⟨2873744161801659 / 10 ^ 15, 2873744161801662 / 10 ^ 15, by norm_num⟩

private theorem tightInput_mem : ∀ i, (tightInputBox i).Contains (tightInput i) := by
  intro i
  fin_cases i
  · simpa [tightInputBox, tightInput, RationalInterval.Contains] using
      ⟨cStar_mem_isolation_box.1.le, cStar_mem_isolation_box.2.le⟩
  · simpa [tightInputBox, tightInput, RationalInterval.Contains] using
      ⟨certifiedEndpointPair_second_mem_isolation_box.1.le,
        certifiedEndpointPair_second_mem_isolation_box.2.le⟩

private theorem tightBounds (f : RE) (target : RationalInterval)
    (h : f.certifiesWithin tightInputBox target = true) :
    target.Contains (f.eval tightInput) :=
  RadicalExpression.certifiesWithin_sound tightInput_mem h

section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The endpoint's second algebraic coordinate is enclosed to fourteen decimal places. -/
theorem endpointB_tight_bounds :
    (2873744161801659 : ℝ) / 10 ^ 15 ≤ certifiedEndpointPair.2 ∧
      certifiedEndpointPair.2 ≤ 2873744161801662 / 10 ^ 15 :=
  ⟨certifiedEndpointPair_second_mem_isolation_box.1.le,
    certifiedEndpointPair_second_mem_isolation_box.2.le⟩

/-- The outer endpoint radius is enclosed to thirteen decimal places. -/
theorem endpointOuterRadius_tight_bounds :
    (73435810128496 : ℝ) / 10 ^ 14 ≤
        endpointOuterRadius cStar certifiedEndpointPair.2 ∧
      endpointOuterRadius cStar certifiedEndpointPair.2 ≤ 73435810128498 / 10 ^ 14 := by
  let target : RationalInterval :=
    ⟨73435810128496 / 10 ^ 14, 73435810128498 / 10 ^ 14, by norm_num⟩
  have hcert : tightOuterRadius.certifiesWithin tightInputBox target = true := by
    norm_num [tightOuterRadius, tightC, tightB, reSub, reDiv, tightInputBox,
      RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := tightBounds tightOuterRadius target hcert
  simpa [tightOuterRadius, tightC, tightB, reSub, reDiv, tightInput, target,
    endpointOuterRadius, RadicalExpression.eval, RationalInterval.Contains,
    div_eq_mul_inv, sub_eq_add_neg, pow_two, add_assoc] using h

/-- The second endpoint distance is enclosed to thirteen decimal places. -/
theorem endpointSecondDistance_tight_bounds :
    (204381086361534 : ℝ) / 10 ^ 14 ≤
        endpointSecondDistance cStar certifiedEndpointPair.2 ∧
      endpointSecondDistance cStar certifiedEndpointPair.2 ≤ 204381086361536 / 10 ^ 14 := by
  let target : RationalInterval :=
    ⟨204381086361534 / 10 ^ 14, 204381086361536 / 10 ^ 14, by norm_num⟩
  have hcert : tightD.certifiesWithin tightInputBox target = true := by
    norm_num [tightD, tightC, tightB, reSub, tightInputBox,
      RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := tightBounds tightD target hcert
  simpa [tightD, tightC, tightB, reSub, tightInput, target, endpointSecondDistance,
    RadicalExpression.eval, RationalInterval.Contains, sub_eq_add_neg, pow_two] using h

/-- The first auxiliary endpoint distance is enclosed to thirteen decimal places. -/
theorem endpointFirstAuxiliaryDistance_tight_bounds :
    (190504665395484 : ℝ) / 10 ^ 14 ≤
        endpointFirstAuxiliaryDistance certifiedEndpointPair.2 ∧
      endpointFirstAuxiliaryDistance certifiedEndpointPair.2 ≤
        190504665395485 / 10 ^ 14 := by
  have hB_lower := endpointB_tight_bounds.1
  have hB_upper := endpointB_tight_bounds.2
  have hB_pos : 0 < certifiedEndpointPair.2 := by positivity
  rw [endpointFirstAuxiliaryDistance]
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num at hB_lower ⊢
    nlinarith
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num at hB_upper ⊢
      nlinarith

/-- The mixed auxiliary endpoint distance is enclosed to thirteen decimal places. -/
theorem endpointMixedAuxiliaryDistance_tight_bounds :
    (207245964946978 : ℝ) / 10 ^ 14 ≤
        endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2 ∧
      endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2 ≤
        207245964946981 / 10 ^ 14 := by
  have hc_lower := cStar_mem_isolation_box.1.le
  have hc_upper := cStar_mem_isolation_box.2.le
  have hB_lower := endpointB_tight_bounds.1
  have hB_upper := endpointB_tight_bounds.2
  have hD_lower := endpointSecondDistance_tight_bounds.1
  have hD_upper := endpointSecondDistance_tight_bounds.2
  have hc_pos : 0 < cStar := cStar_pos
  have hB_pos : 0 < certifiedEndpointPair.2 := by positivity
  have hD_pos : 0 < endpointSecondDistance cStar certifiedEndpointPair.2 := by
    norm_num at hD_lower ⊢
    linarith
  rw [endpointMixedAuxiliaryDistance]
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num at hc_upper hB_lower hD_lower ⊢
    nlinarith
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num at hc_lower hB_upper hD_upper ⊢
      nlinarith

private theorem endpointUnitAbscissa_tight_bounds :
    (-81460137687229 : ℝ) / 10 ^ 14 ≤ endpointUnitAbscissa certifiedEndpointPair.2 ∧
      endpointUnitAbscissa certifiedEndpointPair.2 ≤ -81460137687227 / 10 ^ 14 := by
  have hB_lower := endpointB_tight_bounds.1
  have hB_upper := endpointB_tight_bounds.2
  have hB_pos : 0 < certifiedEndpointPair.2 := by positivity
  rw [endpointUnitAbscissa]
  constructor <;> norm_num at hB_lower hB_upper ⊢ <;> nlinarith

private theorem endpointOuterAbscissa_tight_bounds :
    (-25500889063519 : ℝ) / 10 ^ 14 ≤
        endpointOuterAbscissa cStar certifiedEndpointPair.2 ∧
      endpointOuterAbscissa cStar certifiedEndpointPair.2 ≤
        -25500889063513 / 10 ^ 14 := by
  have hb_lower := endpointOuterRadius_tight_bounds.1
  have hb_upper := endpointOuterRadius_tight_bounds.2
  have hD_lower := endpointSecondDistance_tight_bounds.1
  have hD_upper := endpointSecondDistance_tight_bounds.2
  have hb_pos : 0 < endpointOuterRadius cStar certifiedEndpointPair.2 := by
    norm_num at hb_lower ⊢
    linarith
  have hD_pos : 0 < endpointSecondDistance cStar certifiedEndpointPair.2 := by
    norm_num at hD_lower ⊢
    linarith
  rw [endpointOuterAbscissa]
  constructor <;> norm_num at hb_lower hb_upper hD_lower hD_upper ⊢ <;> nlinarith

private theorem endpointUnitOrdinate_tight_bounds :
    (58002120374842 : ℝ) / 10 ^ 14 ≤ endpointUnitOrdinate certifiedEndpointPair.2 ∧
      endpointUnitOrdinate certifiedEndpointPair.2 ≤ 58002120374846 / 10 ^ 14 := by
  have hx_lower := endpointUnitAbscissa_tight_bounds.1
  have hx_upper := endpointUnitAbscissa_tight_bounds.2
  have hx_neg : endpointUnitAbscissa certifiedEndpointPair.2 < 0 := by
    norm_num at hx_upper ⊢
    linarith
  rw [endpointUnitOrdinate]
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num at hx_lower ⊢
    nlinarith
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num at hx_upper ⊢
      nlinarith

private theorem endpointOuterOrdinate_tight_bounds :
    (-68865977566570 : ℝ) / 10 ^ 14 ≤
        endpointOuterOrdinate cStar certifiedEndpointPair.2 ∧
      endpointOuterOrdinate cStar certifiedEndpointPair.2 ≤
        -68865977566564 / 10 ^ 14 := by
  have hb_lower := endpointOuterRadius_tight_bounds.1
  have hb_upper := endpointOuterRadius_tight_bounds.2
  have hz_lower := endpointOuterAbscissa_tight_bounds.1
  have hz_upper := endpointOuterAbscissa_tight_bounds.2
  have hb_pos : 0 < endpointOuterRadius cStar certifiedEndpointPair.2 := by
    norm_num at hb_lower ⊢
    linarith
  have hz_neg : endpointOuterAbscissa cStar certifiedEndpointPair.2 < 0 := by
    norm_num at hz_upper ⊢
    linarith
  rw [endpointOuterOrdinate]
  constructor
  · rw [le_neg]
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num at hb_upper hz_upper ⊢
      nlinarith
  · rw [neg_le]
    apply Real.le_sqrt_of_sq_le
    norm_num at hb_lower hz_lower ⊢
    nlinarith

private theorem endpointChordAbscissa_tight_bounds :
    (-19170667862866 : ℝ) / 10 ^ 14 ≤
        endpointChordAbscissa cStar certifiedEndpointPair.2 ∧
      endpointChordAbscissa cStar certifiedEndpointPair.2 ≤
        -19170667862863 / 10 ^ 14 := by
  have hc_lower := cStar_mem_isolation_box.1.le
  have hc_upper := cStar_mem_isolation_box.2.le
  have hb_lower := endpointOuterRadius_tight_bounds.1
  have hb_upper := endpointOuterRadius_tight_bounds.2
  have hc_pos : 0 < cStar := cStar_pos
  have hb_pos : 0 < endpointOuterRadius cStar certifiedEndpointPair.2 := by
    norm_num at hb_lower ⊢
    linarith
  rw [endpointChordAbscissa]
  constructor <;> norm_num at hc_lower hc_upper hb_lower hb_upper ⊢ <;> nlinarith

private theorem endpointChordOrdinate_tight_bounds :
    (70889376516655 : ℝ) / 10 ^ 14 ≤
        endpointChordOrdinate cStar certifiedEndpointPair.2 ∧
      endpointChordOrdinate cStar certifiedEndpointPair.2 ≤ 70889376516659 / 10 ^ 14 := by
  have hb_lower := endpointOuterRadius_tight_bounds.1
  have hb_upper := endpointOuterRadius_tight_bounds.2
  have hk_lower := endpointChordAbscissa_tight_bounds.1
  have hk_upper := endpointChordAbscissa_tight_bounds.2
  have hb_pos : 0 < endpointOuterRadius cStar certifiedEndpointPair.2 := by
    norm_num at hb_lower ⊢
    linarith
  have hk_neg : endpointChordAbscissa cStar certifiedEndpointPair.2 < 0 := by
    norm_num at hk_upper ⊢
    linarith
  rw [endpointChordOrdinate]
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num at hb_lower hk_lower ⊢
    nlinarith
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num at hb_upper hk_upper ⊢
      nlinarith

private theorem endpointAngularRate_tight_bounds :
    (123451424854987 : ℝ) / 10 ^ 14 ≤
        endpointAngularRate cStar certifiedEndpointPair.2 ∧
      endpointAngularRate cStar certifiedEndpointPair.2 ≤ 123451424855002 / 10 ^ 14 := by
  let f : RadicalExpression 3 :=
    .mul (.mul (.var 0) (.add (.constant 1) (.neg (.var 1)))) (.inv (.var 2))
  let X : Fin 3 → RationalInterval
    | 0 => ⟨73435810128496 / 10 ^ 14, 73435810128498 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨-19170667862866 / 10 ^ 14, -19170667862863 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨70889376516655 / 10 ^ 14, 70889376516659 / 10 ^ 14, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointChordAbscissa cStar certifiedEndpointPair.2,
      endpointChordOrdinate cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨123451424854987 / 10 ^ 14, 123451424855002 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointChordAbscissa_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointChordOrdinate_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointAngularRate, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointOuterAbscissaDerivative_tight_bounds :
    (-131425356091268 : ℝ) / 10 ^ 14 ≤
        endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2 ∧
      endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2 ≤
        -131425356091250 / 10 ^ 14 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨73435810128496 / 10 ^ 14, 73435810128498 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨-81460137687229 / 10 ^ 14, -81460137687227 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨123451424854987 / 10 ^ 14, 123451424855002 / 10 ^ 14, by norm_num⟩
    | 3 => ⟨58002120374842 / 10 ^ 14, 58002120374846 / 10 ^ 14, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointUnitAbscissa certifiedEndpointPair.2,
      endpointAngularRate cStar certifiedEndpointPair.2,
      endpointUnitOrdinate certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨-131425356091268 / 10 ^ 14, -131425356091250 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointUnitAbscissa_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointAngularRate_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointOuterAbscissaDerivative, RationalInterval.Contains,
    RadicalExpression.eval, sub_eq_add_neg] using h

private theorem endpointSecondDistanceDerivative_tight_bounds :
    (272331438591097 : ℝ) / 10 ^ 14 ≤
        endpointSecondDistanceDerivative cStar certifiedEndpointPair.2 ∧
      endpointSecondDistanceDerivative cStar certifiedEndpointPair.2 ≤
        272331438591122 / 10 ^ 14 := by
  let f : RadicalExpression 3 :=
    .mul
      (.add (.mul (.constant 4) (.var 0)) (.neg (.mul (.constant 2) (.var 1))))
      (.inv (.var 2))
  let X : Fin 3 → RationalInterval
    | 0 => ⟨73435810128496 / 10 ^ 14, 73435810128498 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨-131425356091268 / 10 ^ 14, -131425356091250 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨204381086361534 / 10 ^ 14, 204381086361536 / 10 ^ 14, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2,
      endpointSecondDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨272331438591097 / 10 ^ 14, 272331438591122 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointOuterAbscissaDerivative_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointSecondDistance_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointSecondDistanceDerivative, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointMixedDistanceDerivative_tight_bounds :
    (134283423283747 : ℝ) / 10 ^ 14 ≤
        endpointMixedDistanceDerivative cStar certifiedEndpointPair.2 ∧
      endpointMixedDistanceDerivative cStar certifiedEndpointPair.2 ≤
        134283423283761 / 10 ^ 14 := by
  let f : RadicalExpression 3 :=
    .mul (.add (.mul (.constant 2) (.var 0)) (.neg (.var 1))) (.inv (.var 2))
  let X : Fin 3 → RationalInterval
    | 0 => ⟨73435810128496 / 10 ^ 14, 73435810128498 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨-131425356091268 / 10 ^ 14, -131425356091250 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨207245964946978 / 10 ^ 14, 207245964946981 / 10 ^ 14, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2,
      endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨134283423283747 / 10 ^ 14, 134283423283761 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointOuterAbscissaDerivative_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointMixedAuxiliaryDistance_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointMixedDistanceDerivative, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointBaseAngularCoefficient_tight_bounds :
    (-27022841492817 : ℝ) / 10 ^ 14 ≤
        endpointBaseAngularCoefficient cStar certifiedEndpointPair.2 ∧
      endpointBaseAngularCoefficient cStar certifiedEndpointPair.2 ≤
        -27022841492806 / 10 ^ 14 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.mul (.constant 2) (.var 0)) (.inv (.var 1)))
      (.mul (.mul (.constant 2) (.var 2)) (.inv (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨58002120374842 / 10 ^ 14, 58002120374846 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨2873744161801659 / 10 ^ 15, 2873744161801662 / 10 ^ 15, by norm_num⟩
    | 2 => ⟨-68865977566570 / 10 ^ 14, -68865977566564 / 10 ^ 14, by norm_num⟩
    | 3 => ⟨204381086361534 / 10 ^ 14, 204381086361536 / 10 ^ 14, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointUnitOrdinate certifiedEndpointPair.2, certifiedEndpointPair.2,
      endpointOuterOrdinate cStar certifiedEndpointPair.2,
      endpointSecondDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨-27022841492817 / 10 ^ 14, -27022841492806 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointB_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointOuterOrdinate_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointSecondDistance_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.mul,
      RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointBaseAngularCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv] using h

private theorem endpointLambdaAngularCoefficient_tight_bounds :
    (40366933943401 : ℝ) / 10 ^ 14 ≤
        endpointLambdaAngularCoefficient certifiedEndpointPair.2 ∧
      endpointLambdaAngularCoefficient certifiedEndpointPair.2 ≤
        40366933943405 / 10 ^ 14 := by
  let f : RadicalExpression 2 :=
    .mul (.mul (.constant 2) (.var 0)) (.inv (.var 1))
  let X : Fin 2 → RationalInterval
    | 0 => ⟨58002120374842 / 10 ^ 14, 58002120374846 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨2873744161801659 / 10 ^ 15, 2873744161801662 / 10 ^ 15, by norm_num⟩
  let value : Fin 2 → ℝ :=
    ![endpointUnitOrdinate certifiedEndpointPair.2, certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨40366933943401 / 10 ^ 14, 40366933943405 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointB_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointLambdaAngularCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv] using h

private theorem endpointMuAngularCoefficient_tight_bounds :
    (25204550198888 : ℝ) / 10 ^ 14 ≤
        endpointMuAngularCoefficient cStar certifiedEndpointPair.2 ∧
      endpointMuAngularCoefficient cStar certifiedEndpointPair.2 ≤
        25204550198896 / 10 ^ 14 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.var 0) (.inv (.var 1)))
      (.mul (.add (.var 0) (.var 2)) (.inv (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨58002120374842 / 10 ^ 14, 58002120374846 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨190504665395484 / 10 ^ 14, 190504665395485 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨-68865977566570 / 10 ^ 14, -68865977566564 / 10 ^ 14, by norm_num⟩
    | 3 => ⟨207245964946978 / 10 ^ 14, 207245964946981 / 10 ^ 14, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointUnitOrdinate certifiedEndpointPair.2,
      endpointFirstAuxiliaryDistance certifiedEndpointPair.2,
      endpointOuterOrdinate cStar certifiedEndpointPair.2,
      endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨25204550198888 / 10 ^ 14, 25204550198896 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointFirstAuxiliaryDistance_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using endpointOuterOrdinate_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointMixedAuxiliaryDistance_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.mul,
      RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointMuAngularCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv] using h

private theorem endpointLambdaRadialCoefficient_tight_bounds :
    (-119330642182591 : ℝ) / 10 ^ 14 ≤ endpointLambdaRadialCoefficient cStar ∧
      endpointLambdaRadialCoefficient cStar ≤ -119330642182590 / 10 ^ 14 := by
  have hc_lower := cStar_mem_isolation_box.1.le
  have hc_upper := cStar_mem_isolation_box.2.le
  rw [endpointLambdaRadialCoefficient]
  constructor <;> norm_num at hc_lower hc_upper ⊢ <;> linarith

private theorem endpointMuRadialCoefficient_tight_bounds :
    (-281700429811796 : ℝ) / 10 ^ 14 ≤
        endpointMuRadialCoefficient cStar certifiedEndpointPair.2 ∧
      endpointMuRadialCoefficient cStar certifiedEndpointPair.2 ≤
        -281700429811781 / 10 ^ 14 := by
  have hc_lower := cStar_mem_isolation_box.1.le
  have hc_upper := cStar_mem_isolation_box.2.le
  have hC_lower := endpointMixedDistanceDerivative_tight_bounds.1
  have hC_upper := endpointMixedDistanceDerivative_tight_bounds.2
  rw [endpointMuRadialCoefficient]
  constructor <;> norm_num at hc_lower hc_upper hC_lower hC_upper ⊢ <;> linarith

private theorem endpointStationarityDeterminant_tight_bounds :
    (-83637074808850 : ℝ) / 10 ^ 14 ≤
        endpointStationarityDeterminant cStar certifiedEndpointPair.2 ∧
      endpointStationarityDeterminant cStar certifiedEndpointPair.2 ≤
        -83637074808822 / 10 ^ 14 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨40366933943401 / 10 ^ 14, 40366933943405 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨-281700429811796 / 10 ^ 14, -281700429811781 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨25204550198888 / 10 ^ 14, 25204550198896 / 10 ^ 14, by norm_num⟩
    | 3 => ⟨-119330642182591 / 10 ^ 14, -119330642182590 / 10 ^ 14, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointLambdaAngularCoefficient certifiedEndpointPair.2,
      endpointMuRadialCoefficient cStar certifiedEndpointPair.2,
      endpointMuAngularCoefficient cStar certifiedEndpointPair.2,
      endpointLambdaRadialCoefficient cStar]
  let target : RationalInterval :=
    ⟨-83637074808850 / 10 ^ 14, -83637074808822 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaAngularCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuRadialCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuAngularCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaRadialCoefficient_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointStationarityDeterminant, RationalInterval.Contains,
    RadicalExpression.eval, sub_eq_add_neg] using h

/-- The first endpoint weight is enclosed in an interval of width `8 · 10⁻¹⁴`. -/
theorem endpointLambda_tight_bounds :
    (8947642540845 : ℝ) / 10 ^ 14 ≤ endpointLambda ∧
      endpointLambda ≤ 8947642540925 / 10 ^ 14 := by
  let f : RadicalExpression 5 :=
    .mul
      (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
      (.inv (.var 4))
  let X : Fin 5 → RationalInterval
    | 0 => ⟨-27022841492817 / 10 ^ 14, -27022841492806 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨-281700429811796 / 10 ^ 14, -281700429811781 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨25204550198888 / 10 ^ 14, 25204550198896 / 10 ^ 14, by norm_num⟩
    | 3 => ⟨272331438591097 / 10 ^ 14, 272331438591122 / 10 ^ 14, by norm_num⟩
    | 4 => ⟨-83637074808850 / 10 ^ 14, -83637074808822 / 10 ^ 14, by norm_num⟩
  let value : Fin 5 → ℝ :=
    ![endpointBaseAngularCoefficient cStar certifiedEndpointPair.2,
      endpointMuRadialCoefficient cStar certifiedEndpointPair.2,
      endpointMuAngularCoefficient cStar certifiedEndpointPair.2,
      endpointSecondDistanceDerivative cStar certifiedEndpointPair.2,
      endpointStationarityDeterminant cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨8947642540845 / 10 ^ 14, 8947642540925 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointBaseAngularCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuRadialCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuAngularCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointSecondDistanceDerivative_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointStationarityDeterminant_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointLambda, endpointCramerLambda,
    RationalInterval.Contains, RadicalExpression.eval, div_eq_mul_inv,
    sub_eq_add_neg] using h

/-- The second endpoint weight is enclosed in an interval of width `7.4 · 10⁻¹³`. -/
theorem endpointMu_tight_bounds :
    (92883833887503 : ℝ) / 10 ^ 14 ≤ endpointMu ∧
      endpointMu ≤ 92883833887577 / 10 ^ 14 := by
  let f : RadicalExpression 5 :=
    .mul
      (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
      (.inv (.var 4))
  let X : Fin 5 → RationalInterval
    | 0 => ⟨40366933943401 / 10 ^ 14, 40366933943405 / 10 ^ 14, by norm_num⟩
    | 1 => ⟨272331438591097 / 10 ^ 14, 272331438591122 / 10 ^ 14, by norm_num⟩
    | 2 => ⟨-27022841492817 / 10 ^ 14, -27022841492806 / 10 ^ 14, by norm_num⟩
    | 3 => ⟨-119330642182591 / 10 ^ 14, -119330642182590 / 10 ^ 14, by norm_num⟩
    | 4 => ⟨-83637074808850 / 10 ^ 14, -83637074808822 / 10 ^ 14, by norm_num⟩
  let value : Fin 5 → ℝ :=
    ![endpointLambdaAngularCoefficient certifiedEndpointPair.2,
      endpointSecondDistanceDerivative cStar certifiedEndpointPair.2,
      endpointBaseAngularCoefficient cStar certifiedEndpointPair.2,
      endpointLambdaRadialCoefficient cStar,
      endpointStationarityDeterminant cStar certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨92883833887503 / 10 ^ 14, 92883833887577 / 10 ^ 14, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaAngularCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointSecondDistanceDerivative_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointBaseAngularCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaRadialCoefficient_tight_bounds
    · simpa [X, value, RationalInterval.Contains] using
        endpointStationarityDeterminant_tight_bounds
  have hcert : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hcert
  simpa [f, value, target, endpointMu, endpointCramerMu, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

end

end Bescovitch

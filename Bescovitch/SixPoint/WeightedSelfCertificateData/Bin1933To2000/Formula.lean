/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedSelfDyadicPolynomial

/-!
# Nominal formula for the radius bin `[1933/5000, 2/5]`
-/

@[expose] public section

namespace Bescovitch
namespace WeightedSelfBin1933Div5000TwoFifths
namespace Internal

open DyadicTrivariatePolynomial

noncomputable section

/-- The numerators of the common-denominator nominal coefficient vector. -/
def nominalNumerators : Fin 18 → ℤ := ![
  1524596944819,
  3159715121154,
  2247193809520,
  2094620947479,
  2278693482689,
  98380370149,
  1021268553918,
  208420083779,
  6041009426,
  268985659914,
  18205604670,
  268042924775,
  17577289049,
  246390455462,
  12317739585,
  413853097094,
  4365710208548,
  6131883299131]

/-- The common-denominator dyadic coefficient vector for the nominal formula. -/
def atoms (i : Fin 18) : ScaledPolynomial :=
  .dyadic (nominalNumerators i) 40

/-- The dyadic affine chart for the nominal radius bin. -/
def chart : WeightedSelfChart ScaledPolynomial :=
  let lower := ScaledPolynomial.dyadic 425071195298 40
  let upper := ScaledPolynomial.dyadic 439804651110 40
  let b := lower + (upper + -lower) * ScaledPolynomial.second
  let r := atoms 0 + -b +
    (ScaledPolynomial.dyadic 1 0 + -atoms 0 + b) * ScaledPolynomial.first
  let t := ScaledPolynomial.dyadic (-1) 0 +
    ScaledPolynomial.dyadic 2 0 * ScaledPolynomial.third
  ⟨r, b, t⟩

/-- The specialized dyadic weighted-self formula on the nominal chart. -/
def formula : Bescovitch.WeightedSelfFormula ScaledPolynomial :=
  WeightedSelfDyadicPolynomial.formula atoms chart.r chart.b chart.t

/-- The negation of the nominal polynomial P. -/
def negativeP : ScaledPolynomial := -formula.p

end

end Internal
end WeightedSelfBin1933Div5000TwoFifths
end Bescovitch

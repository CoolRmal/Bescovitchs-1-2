/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.RationalEndpointData
public import Bescovitch.Certificates.BernsteinPass
public import Bescovitch.SixPoint.WeightedMixedPolynomial

/-!
# Coordinatewise Bernstein conversion for the weighted mixed chart
-/

@[expose] public section

namespace Bescovitch.MultivariateDensePolynomial

open WeightedMixedPolynomial

/-- The six chart-specific coordinate passes equal its recursive Bernstein conversion. -/
theorem rationalCenteredBernsteinAt_degreeProfile
    (p : MultivariateDensePolynomial 6) :
    rationalCenteredBernsteinAt 0 (degreeProfile 0)
      (rationalCenteredBernsteinAt 1 (degreeProfile 1)
        (rationalCenteredBernsteinAt 2 (degreeProfile 2)
          (rationalCenteredBernsteinAt 3 (degreeProfile 3)
            (rationalCenteredBernsteinAt 4 (degreeProfile 4)
              (rationalCenteredBernsteinAt 5 (degreeProfile 5) p))))) =
      centeredBernstein degreeProfile p := by
  convert rationalCenteredBernsteinAt_six
    .quadratic .quadratic .quartic .quadratic .quadratic .quartic p using 1 <;>
    simp [degreeProfile]
  congr 1
  funext i
  fin_cases i <;> rfl

end Bescovitch.MultivariateDensePolynomial

/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEqualityComplement

/-!
# Data constructors for the equality-complement certificate

The generated midpoint trees store the same q12 tangent and slack numerators as the strict
mixed certificate.
-/

@[expose] public section

namespace Bescovitch

/-- Assemble one certified equality-complement leaf from its exact integer numerators. -/
def weightedMixedEqualityCertified
    (r0 r1 r2 r3 r4 r5 : ℕ) (s0 s1 s2 s3 : ℤ) (e0 e1 e2 e3 : ℕ) :
    WeightedMixedEqualityComplementTree :=
  .certified {
    rhoNumerator
      | 0 => r0
      | 1 => r1
      | 2 => r2
      | 3 => r3
      | 4 => r4
      | 5 => r5
    supportSlopeNumerator
      | 0 => s0
      | 1 => s1
      | 2 => s2
      | 3 => s3
    slackNumerator
      | 0 => e0
      | 1 => e1
      | 2 => e2
      | 3 => e3 }

end Bescovitch

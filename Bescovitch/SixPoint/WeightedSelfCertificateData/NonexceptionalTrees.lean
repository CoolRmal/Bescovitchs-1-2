/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.Certificates.RadicalBernstein

/-!
# Subdivision data for the nonexceptional weighted-self bins

These values contain only subdivision topology. Their sign checks are stated and proved where
the exact fixed-width checker is run.
-/

@[expose] public section

namespace Bescovitch

/-- Discriminant subdivision for weighted-self bin 2. -/
def weightedSelfDiscriminantTreeBin2 : TensorSubdivision :=
  .splitThird
    (.splitThird
      (.splitThird
        .leaf
        .leaf)
      .leaf)
    .leaf

/-- Discriminant subdivision for weighted-self bin 3. -/
def weightedSelfDiscriminantTreeBin3 : TensorSubdivision :=
  .splitThird
    (.splitThird
      (.splitThird
        (.splitFirst
          .leaf
          (.splitFirst
            .leaf
            (.splitThird
              .leaf
              .leaf)))
        .leaf)
      .leaf)
    .leaf

/-- Discriminant subdivision shared by weighted-self bins 4, 6, and 7. -/
def weightedSelfDiscriminantTreeBin4 : TensorSubdivision :=
  .splitThird
    (.splitThird
      (.splitThird
        (.splitFirst
          .leaf
          (.splitFirst
            .leaf
            (.splitThird
              .leaf
              (.splitFirst
                .leaf
                (.splitFirst
                  .leaf
                  (.splitThird
                    .leaf
                    .leaf))))))
        .leaf)
      .leaf)
    .leaf

/-- Interval-Horner subdivision for `-P` on weighted-self bin 1. -/
def weightedSelfNegativePTreeBin1 : TensorSubdivision :=
  (.splitFirst
    .leaf
    (.splitSecond
      .leaf
      (.splitThird
        .leaf
        .leaf)))

/-- Interval-Horner subdivision for `-P` on weighted-self bin 2. -/
def weightedSelfNegativePTreeBin2 : TensorSubdivision :=
  (.splitFirst
    (.splitSecond
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            .leaf
            .leaf))
        .leaf)
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            (.splitThird
              .leaf
              .leaf)
            (.splitThird
              .leaf
              .leaf)))
        .leaf))
    (.splitSecond
      (.splitThird
        (.splitFirst
          (.splitSecond
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  .leaf))
              .leaf)
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  .leaf))
              .leaf))
          (.splitSecond
            (.splitThird
              (.splitFirst
                (.splitSecond
                  .leaf
                  .leaf)
                (.splitSecond
                  .leaf
                  (.splitThird
                    .leaf
                    .leaf)))
              .leaf)
            (.splitThird
              (.splitFirst
                (.splitSecond
                  .leaf
                  .leaf)
                (.splitSecond
                  (.splitThird
                    .leaf
                    .leaf)
                  (.splitThird
                    .leaf
                    .leaf)))
              .leaf)))
        .leaf)
      (.splitThird
        (.splitFirst
          (.splitSecond
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  .leaf))
              .leaf)
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  .leaf))
              .leaf))
          (.splitSecond
            (.splitThird
              (.splitFirst
                (.splitSecond
                  .leaf
                  (.splitThird
                    .leaf
                    .leaf))
                (.splitSecond
                  (.splitThird
                    .leaf
                    .leaf)
                  (.splitThird
                    .leaf
                    .leaf)))
              .leaf)
            (.splitThird
              (.splitFirst
                (.splitSecond
                  (.splitThird
                    .leaf
                    .leaf)
                  (.splitThird
                    .leaf
                    .leaf))
                (.splitSecond
                  (.splitThird
                    (.splitFirst
                      .leaf
                      (.splitSecond
                        .leaf
                        .leaf))
                    .leaf)
                  (.splitThird
                    (.splitFirst
                      .leaf
                      (.splitSecond
                        .leaf
                        .leaf))
                    .leaf)))
              .leaf)))
        .leaf)))

/-- Interval-Horner subdivision for `-P` on weighted-self bin 3. -/
def weightedSelfNegativePTreeBin3 : TensorSubdivision :=
  (.splitFirst
    (.splitSecond
      .leaf
      (.splitThird
        .leaf
        .leaf))
    (.splitSecond
      (.splitThird
        .leaf
        .leaf)
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            (.splitThird
              .leaf
              .leaf)
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  .leaf))
              .leaf)))
        .leaf)))

/-- Interval-Horner subdivision for `-P` on weighted-self bin 4. -/
def weightedSelfNegativePTreeBin4 : TensorSubdivision :=
  (.splitFirst
    .leaf
    (.splitSecond
      (.splitThird
        .leaf
        .leaf)
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            (.splitThird
              .leaf
              .leaf)
            (.splitThird
              .leaf
              .leaf)))
        .leaf)))

/-- Interval-Horner subdivision for `-P` on weighted-self bin 5. -/
def weightedSelfNegativePTreeBin5 : TensorSubdivision :=
  (.splitFirst
    .leaf
    (.splitSecond
      (.splitThird
        .leaf
        .leaf)
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            .leaf
            (.splitThird
              .leaf
              .leaf)))
        .leaf)))

/-- Interval-Horner subdivision for `-P` on weighted-self bin 6. -/
def weightedSelfNegativePTreeBin6 : TensorSubdivision :=
  (.splitFirst
    .leaf
    (.splitSecond
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            .leaf
            (.splitThird
              .leaf
              .leaf)))
        .leaf)
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            (.splitThird
              .leaf
              .leaf)
            (.splitThird
              .leaf
              .leaf)))
        .leaf)))

/-- Interval-Horner subdivision for `-P` on weighted-self bin 7. -/
def weightedSelfNegativePTreeBin7 : TensorSubdivision :=
  (.splitFirst
    .leaf
    (.splitSecond
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            (.splitThird
              .leaf
              .leaf)
            (.splitThird
              .leaf
              .leaf)))
        .leaf)
      (.splitThird
        (.splitFirst
          .leaf
          (.splitSecond
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  .leaf))
              .leaf)
            (.splitThird
              (.splitFirst
                .leaf
                (.splitSecond
                  .leaf
                  (.splitThird
                    .leaf
                    .leaf)))
              .leaf)))
        .leaf)))

end Bescovitch

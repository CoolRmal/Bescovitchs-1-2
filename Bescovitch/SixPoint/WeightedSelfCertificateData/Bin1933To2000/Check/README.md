# Row-level certificate checks

Each `R00` through `R12` module checks one first-axis row of one exact tensor identity or
Bernstein sign certificate. The split is resource-driven: combining two computed rows made the
Lean child exceed the project's 512 MB peak-footprint gate, while isolated rows pass it.

The directories correspond to the six certified objects:

- `PF`: coefficient identity for `-P`;
- `PS`: Bernstein sign margin for `-P`;
- `QF`: coefficient identity for `Q`;
- `RF`: coefficient identity for the radicand;
- `DF`: coefficient identity for the discriminant; and
- `DS`: Bernstein sign margin for the discriminant.

The six topic aggregators in the parent directory combine their thirteen opaque row theorems into
the semantic factor or sign certificate used by `NominalSigns.lean`.

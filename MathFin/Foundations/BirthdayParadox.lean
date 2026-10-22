/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
import Archive.Wiedijk100Theorems.BirthdayProblem

/-! # Birthday paradox

Mathlib already proves this exactly (`Archive/Wiedijk100Theorems/BirthdayProblem.lean`,
Theorem 93 of Freek Wiedijk's 100-theorems list): with 23 people and 365 equally likely
birthdays, the probability of at least one shared birthday exceeds `1/2`. Mathlib formalizes
the "smallest such k" claim only as the two data points k = 23 (holds) and k = 22 (fails) —
minimality over every k < 23 is not separately stated, since it would additionally need
monotonicity of the match probability in k, which neither Mathlib nor this file formalizes.
This file is a thin citation, not a reproof.

This file does not use the Lean module system (`module` header): the file it cites,
`Archive/Wiedijk100Theorems/BirthdayProblem.lean`, predates the module system and cannot be
`public import`ed from one. Its declarations below are plain top-level declarations
(no `@[expose] public section` needed outside the module system).

Consequently, no `module`-header file anywhere in this library (`Foundations/`, `Bridges/`,
or any pricing section) can import this one: Lean rejects `import MathFin.Foundations.
BirthdayParadox` from a `module` file with "cannot import non-`module` ... from `module`". The
restriction is one-directional, though: a non-module file (this one) *can* import a module file
— `import MathFin.Foundations.StandardNormal` here would compile fine alongside the Archive
import. A benchmark entry citing this file (added 2026-10-22) satisfies
`tests/test_architecture.py`'s `test_every_module_is_used`, but **not**
`test_every_module_is_connected` (import-graph edges only, by that test's own design — a corpus
citation is not one). Unlike the other modules `STAGING` (issue #3) admits, this one's bridge
has to be built *in this file*, not in a separate `Bridges/` module: import a Foundations module
here and prove a genuine tie to it. That has not been done yet, and was investigated and found
not currently possible without busywork (2026-10-22, the rest of issue #3's batch): no
Foundations module shares genuine combinatorial or probabilistic structure with this discrete
collision computation. The honest candidate is a Poisson/normal approximation limit theorem —
`P(no match)` for `k` people and `n` days tends to `exp(-k(k-1)/(2n))` as the ratio `k²/n` is
held fixed, tying the discrete count here to `StandardNormal`/`Real.exp` — but that is a real new
piece of analysis (a limit argument on falling factorials), not a bridge, and has not been
attempted. This file stays staged until that work (or some other genuine tie) is actually done. -/

namespace MathFin
namespace BirthdayParadox

open Theorems100 MeasureTheory ProbabilityTheory

local notation "‖" x "‖" => Fintype.card x

/-- **Birthday paradox**, probabilistic form: among 23 people with birthdays drawn
uniformly from 365 days, the probability that all birthdays are distinct is below `1/2`
(equivalently, the probability of a shared birthday exceeds `1/2`). Cites
`Theorems100.birthday_measure` verbatim. -/
theorem birthday_probability_of_match_exceeds_half :
    ℙ ({f | f.Injective} : Set (Fin 23 → Fin 365)) < 1 / 2 :=
  birthday_measure

/-- **Birthday paradox**, threshold form: among 365 days, a shared birthday is more likely
than not at group size 23 but not at group size 22 (minimality over every smaller k is not
claimed here — see the module doc comment). Cites `Theorems100.birthday` verbatim. -/
theorem birthday_23_exceeds_half_and_22_does_not :
    2 * ‖Fin 23 ↪ Fin 365‖ < ‖Fin 23 → Fin 365‖ ∧
      2 * ‖Fin 22 ↪ Fin 365‖ > ‖Fin 22 → Fin 365‖ :=
  birthday

end BirthdayParadox
end MathFin

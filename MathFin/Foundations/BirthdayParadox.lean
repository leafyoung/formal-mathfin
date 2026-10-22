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
BirthdayParadox` from a `module` file with "cannot import non-`module` ... from `module`".
This file can only be consumed by other non-module files — benchmark-corpus snippets and the
aggregators (`AxiomAudit`, `Blueprint`, `Examples`) — never by a library bridge. A benchmark
entry citing it (added 2026-10-22) satisfies `tests/test_architecture.py`'s
`test_every_module_is_used`, but **not** `test_every_module_is_connected`: that test counts
only import-graph edges, by its own design, and a corpus citation is not one. This file has no
route to `test_every_module_is_connected` passing for real short of a change to that test
itself, so it is expected to stay in `STAGING` (issue #3) indefinitely, unlike the library's
other staged modules.
-/

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

/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.MacaulayModified

/-!
# Key-rate duration: the partition-of-unity identity

Key-rate duration (KRD) decomposes a bond's (or portfolio's) effective dollar
duration across a set of curve nodes, so that shocking one key rate at a time
reproduces the total sensitivity to a parallel shock when the shocks are
summed. The decomposition is built from **hat-function weights** `w n i`: for
each curve node `n` and each cashflow `i` (at some maturity), `w n i` is the
fraction of cashflow `i`'s dollar duration attributed to node `n`. The nodes'
weights form a **partition of unity** across every cashflow maturity,

  `Σ_n w n i = 1`     for every cashflow `i`,

which is exactly how the standard triangular/hat key-rate basis is built: at
any maturity, the weights of the (at most two) bracketing nodes sum to one and
every other node's weight is zero.

Writing `d i` for cashflow `i`'s dollar-duration contribution (price times
modified duration), the key-rate duration at node `n` is

  `KRD_n = Σ_i d i · w n i`,

and the **partition-of-unity identity** is the sum-interchange fact that
summing key-rate durations over every node recovers the parallel effective
duration:

  `Σ_n KRD_n = Σ_i d i · (Σ_n w n i) = Σ_i d i · 1 = Σ_i d i`.

This module states the identity abstractly, parametrized by an arbitrary
per-cashflow dollar-duration contribution `d : ι → ℝ`, under exactly the
partition-of-unity hypothesis above — making explicit that the identity is a
genuine consequence of partition of unity, not a restatement of it. It is
then instantiated below with `MacaulayModified`'s own per-cashflow modified-
duration term (`sum_keyRateDuration_modifiedNumerator_eq_modifiedNumerator`).

## Result

* `keyRateDuration`: the key-rate duration at node `n`, `Σ_i d i · w n i`.
* `effectiveDuration`: the parallel (total) dollar duration, `Σ_i d i`.
* `sum_keyRateDuration_eq_effectiveDuration`: the partition-of-unity identity
  `Σ_n KRD_n = effectiveDuration`, given `∀ i ∈ s, Σ_n w n i = 1`.
* `sum_keyRateDuration_modifiedNumerator_eq_modifiedNumerator`: the concrete
  instance promised above — `d` specialized to `MacaulayModified`'s own
  per-cashflow modified-duration term, `Σ_n KRD_n = modifiedNumerator`.
-/

@[expose] public section

namespace MathFin

variable {ι κ : Type*}

/-- Key-rate duration at node `n`: the dollar-duration contributions `d i` of
every cashflow `i ∈ s`, weighted by node `n`'s hat-function weight `w n i`. -/
noncomputable def keyRateDuration (s : Finset ι) (d : ι → ℝ) (w : κ → ι → ℝ) (n : κ) : ℝ :=
  ∑ i ∈ s, d i * w n i

/-- Parallel effective duration: the total dollar-duration contribution
across every cashflow, with no key-rate decomposition. -/
noncomputable def effectiveDuration (s : Finset ι) (d : ι → ℝ) : ℝ := ∑ i ∈ s, d i

/-- **The partition-of-unity identity.** If the key-rate weights `w` form a
partition of unity across every cashflow in `s` (the hat-function property:
at each cashflow's maturity, the node weights sum to one), then summing the
key-rate durations over every node `κ` recovers the parallel effective
duration. The proof is a sum interchange (`Finset.sum_comm`) followed by
substituting the partition-of-unity hypothesis under the sum. -/
theorem sum_keyRateDuration_eq_effectiveDuration (s : Finset ι) (κs : Finset κ)
    (d : ι → ℝ) (w : κ → ι → ℝ) (hpou : ∀ i ∈ s, ∑ n ∈ κs, w n i = 1) :
    ∑ n ∈ κs, keyRateDuration s d w n = effectiveDuration s d := by
  unfold keyRateDuration effectiveDuration
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← Finset.mul_sum, hpou i hi, mul_one]

/-- **The concrete instance**: specializing `d` to `MacaulayModified`'s own
per-cashflow modified-duration term `(t i : ℝ) · c i / (1 + y)^(t i + 1)`
makes `effectiveDuration` definitionally (`rfl`) `modifiedNumerator` — both
are the same sum — so the abstract partition-of-unity identity directly
decomposes the real modified-duration numerator across key-rate nodes. -/
theorem sum_keyRateDuration_modifiedNumerator_eq_modifiedNumerator
    (s : Finset ι) (κs : Finset κ) (t : ι → ℕ) (c : ι → ℝ) (w : κ → ι → ℝ) (y : ℝ)
    (hpou : ∀ i ∈ s, ∑ n ∈ κs, w n i = 1) :
    ∑ n ∈ κs, keyRateDuration s (fun i ↦ (t i : ℝ) * c i / (1 + y) ^ (t i + 1)) w n
      = modifiedNumerator s t c y := by
  rw [sum_keyRateDuration_eq_effectiveDuration s κs _ w hpou]
  rfl

end MathFin

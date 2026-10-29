/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.TemperedT
public import MathFin.BlackScholes.GarmanNormalForm

/-!
# Tempered Asian moments: the exact `E[A]` and `E[A²]` identities

The FMGD case-study model: an arithmetic Asian average over `n` fixing dates,
`A = (S₀/n) · Σᵢ exp(Σ_{j ≤ i} X_j)`, driven by i.i.d. exponentially tempered
Student-t increments `X_j ~ temperedTMeasure ν λ` (see `TemperedT.lean`).

## The moment strip (the design discovery the proofs force)

`E[A]` needs each increment's exponential moment at `θ = 1`, `E[A²]` needs it at
`θ = 2` (the shared increments of a pair of fixings enter with multiplicity 2):
matching the second moment is strictly more demanding than matching the first —

* `E[A]` finite for `λ ≤ 1` (`integral_temperedAsian_eq`),
* `E[A²]` finite for `λ ≤ 1/2` (`integral_temperedAsianSq_eq`),

and by `TemperedT.temperedT_expMoment_eq_top` these are sharp from above. At the
boundary `λ = 1/2` the `θ = 2` moment is finite (the strip edge belongs to the
finite side), so `E[A²]` is exact at `λ = 1/2` as well.

## Main results

* `integral_temperedExpProd_eq`: the factorization engine — for i.i.d. tempered
  increments and coefficients `c j` in the strip, the expectation of a product
  `∏ⱼ e^{cⱼ Xⱼ}` over any fixing subset is the product of the moments
  `m(cⱼ) = temperedExpMoment ν λ (cⱼ)`.
* `integral_temperedAsian_eq`: **exact `E[A]`** = `(S₀/n) Σᵢ m₁^{i+1}` with
  `m₁ = m(1)` (exact theorem; no approximation).
* `integral_temperedAsianPair_eq`, `integral_temperedAsianSq_eq`: **exact
  `E[A²]`** = `(S₀/n)² Σᵢ Σₗ m₂^{min(i,l)+1} · m₁^{|i−l|}` with `m₂ = m(2)` (the
  pair lemma states it as a product over `Iic (max i l)` of `m₂` below
  `min i l` and `m₁` above).
* `twEffVol`, `twLognormalAnsatzPrice`: the Turnbull–Wakeman moment-matched
  lognormal ansatz fed with these moments. **Approximation, disclosed**: only
  the moments above are exact; the matched price is the TW approximation, not a
  closed form of the true price. Unlike the one-asset Gaussian basket
  (`BasketMomentMatching.lean`), even a single fixing is not lognormal under
  tempered increments, so no single-name exactness theorem exists here — that
  gap is the point of the FMGD narrative.
-/

@[expose] public section

namespace MathFin

open Real Finset MeasureTheory ProbabilityTheory

/-! ### Independence factorization engine -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν lam : ℝ}

private lemma ofReal_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∏ j ∈ s, ENNReal.ofReal (f j) = ENNReal.ofReal (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j t hj ihs =>
    have hprod : (0:ℝ) ≤ ∏ k ∈ t, f k :=
      Finset.prod_nonneg fun k _ => hf k
    rw [Finset.prod_cons, ihs, Finset.prod_cons, ENNReal.ofReal_mul (hf j), mul_comm]

/-- Product-integral factorization over a `Finset` for an independent real family,
by extension to the full product (`iIndepFun.integral_fun_prod_eq_prod_integral`).
Measurability hypotheses only. -/
private lemma integral_prod_eq_prod_integral_of_indepFun {n : ℕ} (s : Finset (Fin n))
    (Y : Fin n → Ω → ℝ) (hY : iIndepFun Y P) (hmea : ∀ i, Measurable (Y i)) :
    ∫ ω, ∏ i ∈ s, Y i ω ∂P = ∏ i ∈ s, ∫ ω, Y i ω ∂P := by
  classical
  have hprob : IsProbabilityMeasure P := hY.isProbabilityMeasure
  set f : Fin n → Ω → ℝ := fun i ω => if i ∈ s then Y i ω else 1 with hfdef
  have hmeaf : ∀ i, Measurable (f i) := by
    intro i
    by_cases hi : i ∈ s
    · simp only [hfdef, hi, if_true]
      exact hmea i
    · simp only [hfdef, hi, if_false]
      exact measurable_const
  have hfiid : iIndepFun f P :=
    hY.comp (fun i x => if i ∈ s then x else 1) fun i => by
      by_cases hi : i ∈ s
      · simp only [hi, if_true]
        exact measurable_id
      · simp only [hi, if_false]
        exact measurable_const
  have hfull := hfiid.integral_fun_prod_eq_prod_integral
    fun i => (hmeaf i).aestronglyMeasurable
  have hL : ∀ ω, ∏ i ∈ s, Y i ω = ∏ i, f i ω := by
    intro ω
    calc ∏ i ∈ s, Y i ω = ∏ i ∈ s, (if i ∈ s then Y i ω else 1) :=
          Finset.prod_congr rfl fun i hi => (if_pos hi).symm
      _ = ∏ i, (if i ∈ s then Y i ω else 1) :=
          Finset.prod_subset (Finset.subset_univ s) fun i _ hi => if_neg hi
  have hR : (∏ i ∈ s, ∫ ω, Y i ω ∂P) = ∏ i, (∫ ω, f i ω ∂P) := by
    calc (∏ i ∈ s, ∫ ω, Y i ω ∂P)
        = ∏ i ∈ s, (∫ ω, f i ω ∂P) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hif : (fun ω => if i ∈ s then Y i ω else 1) = fun ω => Y i ω :=
            funext fun ω => if_pos hi
          rw [hfdef, hif]
      _ = ∏ i, (∫ ω, f i ω ∂P) := by
          refine Finset.prod_subset (Finset.subset_univ s) fun i _ hi => ?_
          have hif : (fun ω => if i ∈ s then Y i ω else 1) = fun _ => 1 :=
            funext fun ω => if_neg hi
          rw [hfdef, hif, integral_const]
          simp
  rw [integral_congr_ae (ae_of_all _ fun ω => hL ω), hfull, ← hR]

end Engine

/-! ### Exact expectations of tempered-exponential products -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν lam : ℝ}

/-- The exponential moment of a `HasLaw` copy of the tempered law, as a lower
integral: finite (equal to `ofReal m(θ)`) on the strip. -/
lemma lintegral_ofReal_exp_comp_eq (hν : 0 < ν) (hlam : 0 < lam) {θ : ℝ}
    (h : |θ| ≤ 1 / lam) {X : Ω → ℝ} (hXmeas : Measurable X)
    (hX : HasLaw X (temperedTMeasure ν lam) P) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂P
      = ENNReal.ofReal (temperedExpMoment ν lam θ) := by
  have h1 : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂P)
      = ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂temperedTMeasure ν lam := by
    rw [← hX.map_eq, ← lintegral_map
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))) hXmeas]
  rw [h1, temperedTMeasure,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_temperedTPDF ν lam)
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))),
    lintegral_congr fun x => by
      rw [Pi.mul_apply, temperedTPDF,
        ← ENNReal.ofReal_mul (temperedTPDFReal_pos hν hlam x).le, mul_comm],
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_temperedTPDFReal hν hlam h)
      (ae_of_all _ fun x =>
        mul_nonneg (Real.exp_pos _).le (temperedTPDFReal_pos hν hlam x).le)]
  rfl

/-- On the strip, `e^{θX}` is integrable for any `HasLaw` copy of the tempered law. -/
lemma integrable_exp_comp_temperedT (hν : 0 < ν) (hlam : 0 < lam) {θ : ℝ}
    (h : |θ| ≤ 1 / lam) {X : Ω → ℝ} (hXmeas : Measurable X)
    (hX : HasLaw X (temperedTMeasure ν lam) P) :
    Integrable (fun ω => Real.exp (θ * X ω)) P := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hrew : ∀ ω, ‖Real.exp (θ * X ω)‖ₑ
      = ENNReal.ofReal (Real.exp (θ * X ω)) := fun ω =>
    Real.enorm_eq_ofReal (Real.exp_pos _).le
  rw [lintegral_congr hrew, lintegral_ofReal_exp_comp_eq hν hlam h hXmeas hX]
  exact ENNReal.ofReal_lt_top

variable {n : ℕ} {X : Fin n → Ω → ℝ}

/-- **The factorization engine.** For i.i.d. tempered increments with coefficients
`c j` in the strip, the expectation of a product of tempered exponentials over any
fixing subset factorizes into the product of the exponential moments. -/
lemma integral_temperedExpProd_eq (hν : 0 < ν) (hlam : 0 < lam)
    (hlaw : ∀ j, HasLaw (X j) (temperedTMeasure ν lam) P)
    (hiid : iIndepFun X P) {c : Fin n → ℝ} (_hcs : ∀ j, |c j| ≤ 1 / lam)
    (hmea : ∀ j, Measurable (X j)) (s : Finset (Fin n)) :
    (∫ ω, ∏ j ∈ s, Real.exp (c j * X j ω) ∂P)
      = ∏ j ∈ s, temperedExpMoment ν lam (c j) := by
  have hiid' : iIndepFun (fun j ω => Real.exp (c j * X j ω)) P :=
    hiid.comp (fun j x => Real.exp (c j * x))
      (fun j => Real.measurable_exp.comp (measurable_id.const_mul (c j)))
  have hmea' : ∀ j, Measurable (fun ω => Real.exp (c j * X j ω)) := fun j =>
    Real.measurable_exp.comp ((hmea j).const_mul (c j))
  rw [integral_prod_eq_prod_integral_of_indepFun s _ hiid' hmea']
  exact Finset.prod_congr rfl fun j _ =>
    integral_exp_comp_eq_temperedExpMoment hν hlam (hlaw j) (c j)

/-- Integrability of the tempered-exponential products (needed to exchange sums and
integrals). -/
lemma integrable_temperedExpProd (hν : 0 < ν) (hlam : 0 < lam)
    (hlaw : ∀ j, HasLaw (X j) (temperedTMeasure ν lam) P)
    (hiid : iIndepFun X P) {c : Fin n → ℝ} (hcs : ∀ j, |c j| ≤ 1 / lam)
    (hmea : ∀ j, Measurable (X j)) (s : Finset (Fin n)) :
    Integrable (fun ω => ∏ j ∈ s, Real.exp (c j * X j ω)) P := by
  have hiid' : iIndepFun (fun j ω => Real.exp (c j * X j ω)) P :=
    hiid.comp (fun j x => Real.exp (c j * x))
      (fun j => Real.measurable_exp.comp (measurable_id.const_mul (c j)))
  have hmea' : ∀ j, Measurable (fun ω => Real.exp (c j * X j ω)) := fun j =>
    Real.measurable_exp.comp ((hmea j).const_mul (c j))
  refine ⟨(Finset.measurable_prod s (fun j _ => hmea' j)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hrew : ∀ ω, ‖∏ j ∈ s, Real.exp (c j * X j ω)‖ₑ
      = ∏ j ∈ s, ENNReal.ofReal (Real.exp (c j * X j ω)) := fun ω => by
    rw [Real.enorm_eq_ofReal (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
      ofReal_prod s _ fun _ => (Real.exp_pos _).le]
  have hiid'' : iIndepFun (fun j ω => ENNReal.ofReal (Real.exp (c j * X j ω))) P :=
    hiid.comp (fun j x => ENNReal.ofReal (Real.exp (c j * x)))
      fun j => (Real.measurable_exp.comp (measurable_id.const_mul (c j))).ennreal_ofReal
  have hmea'' : ∀ j, Measurable (fun ω => ENNReal.ofReal (Real.exp (c j * X j ω))) :=
    fun j => (hmea' j).ennreal_ofReal
  rw [lintegral_congr hrew,
    lintegral_prod_eq_prod_lintegral_of_indepFun s _ hiid'' hmea'',
    Finset.prod_congr rfl fun j _ =>
      lintegral_ofReal_exp_comp_eq hν hlam (hcs j) (hmea j) (hlaw j),
    ofReal_prod s _ fun j => (temperedExpMoment_pos hν hlam (hcs j)).le]
  exact ENNReal.ofReal_lt_top

end Moments
/-! ### The exact first and second moments of the tempered Asian average -/

section Asian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν lam : ℝ} {n : ℕ}
  {X : Fin n → Ω → ℝ}

private lemma one_le_one_div_of_lt_one (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (1 : ℝ) ≤ 1 / lam := by
  simpa using (one_div_le_one_div (a := (1 : ℝ)) (b := lam) one_pos hlam).2 hlam1

private lemma two_le_one_div_of_le_half (hlam : 0 < lam) (hlam2 : lam ≤ 2⁻¹) :
    (2 : ℝ) ≤ 1 / lam := by
  have h1 : lam * 2 ≤ 2⁻¹ * 2 := mul_le_mul_of_nonneg_right hlam2 (le_of_lt two_pos)
  rw [inv_mul_cancel₀ two_ne_zero] at h1
  rw [le_div_iff₀ hlam, mul_comm]
  exact h1

/-- **Exact `E[A]`** for the arithmetic average of `n` fixings under i.i.d. tempered
increments, on the strip `λ ≤ 1` (which makes `m₁ = m(1)` finite). Exact theorem:
`E[A] = (S₀/n) Σᵢ m₁^{i+1}` with `m₁ = temperedExpMoment ν λ 1` — the same
`m₁^{fixings}` structure the desk formulas use, now with the moment well-posed. -/
theorem integral_temperedAsian_eq (hν : 0 < ν) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlaw : ∀ j, HasLaw (X j) (temperedTMeasure ν lam) P) (hiid : iIndepFun X P)
    (hmea : ∀ j, Measurable (X j)) (S₀ : ℝ) :
    (∫ ω, S₀ / (n : ℝ) * ∑ i : Fin n, ∏ j ∈ Finset.Iic i, Real.exp (X j ω) ∂P)
      = S₀ / (n : ℝ) * ∑ i : Fin n, (temperedExpMoment ν lam 1) ^ (i.val + 1) := by
  have hone : ∀ j : Fin n, |(1 : ℝ)| ≤ 1 / lam := fun _ => by
    rw [abs_one]
    exact one_le_one_div_of_lt_one hlam hlam1
  have hkey : ∀ i : Fin n, (∫ ω, ∏ j ∈ Finset.Iic i, Real.exp (1 * X j ω) ∂P)
      = (temperedExpMoment ν lam 1) ^ (i.val + 1) := by
    intro i
    rw [integral_temperedExpProd_eq hν hlam hlaw hiid hone hmea (Finset.Iic i),
      Finset.prod_const, Fin.card_Iic]
  have hpub : (fun ω => S₀ / (n : ℝ) * ∑ i : Fin n, ∏ j ∈ Finset.Iic i, Real.exp (X j ω))
      = fun ω => S₀ / (n : ℝ) * ∑ i : Fin n, ∏ j ∈ Finset.Iic i, Real.exp (1 * X j ω) := by
    funext ω
    refine congrArg (S₀ / (n : ℝ) * ·) ?_
    exact Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [one_mul]
  have hsplit : (fun ω => S₀ / (n : ℝ) * ∑ i : Fin n, ∏ j ∈ Finset.Iic i, Real.exp (1 * X j ω))
      = fun ω => ∑ i : Fin n, S₀ / (n : ℝ) * ∏ j ∈ Finset.Iic i, Real.exp (1 * X j ω) := by
    funext ω
    exact Finset.mul_sum Finset.univ (fun i => ∏ j ∈ Finset.Iic i, Real.exp (1 * X j ω))
      (S₀ / (n : ℝ))
  rw [hpub, hsplit,
    integral_finsetSum
      (f := fun i ω => S₀ / (n : ℝ) * ∏ j ∈ Finset.Iic i, Real.exp (1 * X j ω))
      Finset.univ fun i _ =>
      Integrable.const_mul (integrable_temperedExpProd hν hlam hlaw hiid hone hmea
        (Finset.Iic i)) (S₀ / (n : ℝ)),
    Finset.mul_sum Finset.univ _ (S₀ / (n : ℝ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, hkey i]

private lemma prod_eq_prod_ite {M ι : Type*} [CommMonoid M] [DecidableEq ι]
    (s t : Finset ι) (hst : s ⊆ t) (f : ι → M) :
    (∏ j ∈ s, f j) = ∏ j ∈ t, (if j ∈ s then f j else 1) := by
  classical
  calc (∏ j ∈ s, f j) = ∏ j ∈ s, (if j ∈ s then f j else 1) :=
        Finset.prod_congr rfl fun j hj => (if_pos hj).symm
    _ = ∏ j ∈ t, (if j ∈ s then f j else 1) :=
        Finset.prod_subset hst fun j _ hj => if_neg hj

omit [MeasurableSpace Ω] in
/-- Pointwise pair identity: a product of two prefix exponentials is a single product
over the longer prefix with doubled exponents on the shared fixings. -/
private lemma temperedAsianPair_prod_eq (i l : Fin n) (ω : Ω) :
    (∏ j ∈ Finset.Iic i, Real.exp (X j ω)) * (∏ j ∈ Finset.Iic l, Real.exp (X j ω))
      = ∏ j ∈ Finset.Iic (max i l),
          Real.exp ((if j ≤ min i l then (2 : ℝ) else 1) * X j ω) := by
  classical
  rw [prod_eq_prod_ite (Finset.Iic i) (Finset.Iic (max i l))
      (Finset.Iic_subset_Iic.2 (le_max_left i l)) _,
    prod_eq_prod_ite (Finset.Iic l) (Finset.Iic (max i l))
      (Finset.Iic_subset_Iic.2 (le_max_right i l)) _,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  by_cases h1 : j ≤ i
  · by_cases h2 : j ≤ l
    · rw [if_pos (Finset.mem_Iic.2 h1), if_pos (Finset.mem_Iic.2 h2),
        if_pos (le_min_iff.2 ⟨h1, h2⟩), ← Real.exp_add,
        show X j ω + X j ω = (2 : ℝ) * X j ω from by ring]
    · rw [if_pos (Finset.mem_Iic.2 h1), if_neg (fun h => h2 (Finset.mem_Iic.1 h)),
        mul_one, if_neg (fun h => h2 (h.trans (min_le_right i l))), one_mul]
  · by_cases h2 : j ≤ l
    · rw [if_neg (fun h => h1 (Finset.mem_Iic.1 h)), if_pos (Finset.mem_Iic.2 h2),
        one_mul, if_neg (fun h => h1 (h.trans (min_le_left i l))), one_mul]
    · exfalso
      rcases le_max_iff.1 (Finset.mem_Iic.1 hj) with h | h
      · exact h1 h
      · exact h2 h

/-- **Exact pair moment** `E[S_{tᵢ} S_{tₗ}]` for i.i.d. tempered increments: a product
over the longer prefix of `m₂ = m(2)` below `min i l` and `m₁ = m(1)` above — in
closed form, `S₀² · m₂^{min(i,l)+1} · m₁^{|i−l|}`. Valid on the strip `λ ≤ 1/2`. -/
lemma integral_temperedAsianPair_eq (hν : 0 < ν) (hlam : 0 < lam) (hlam2 : lam ≤ 2⁻¹)
    (hlaw : ∀ j, HasLaw (X j) (temperedTMeasure ν lam) P) (hiid : iIndepFun X P)
    (hmea : ∀ j, Measurable (X j)) (i l : Fin n) :
    (∫ ω, (∏ j ∈ Finset.Iic i, Real.exp (X j ω)) * (∏ j ∈ Finset.Iic l, Real.exp (X j ω)) ∂P)
      = ∏ j ∈ Finset.Iic (max i l),
          (if j ≤ min i l then temperedExpMoment ν lam 2 else temperedExpMoment ν lam 1) := by
  have hone : ∀ j : Fin n, |(1 : ℝ)| ≤ 1 / lam := fun _ => by
    rw [abs_one]
    have h21 : lam ≤ 1 := le_trans hlam2 (by norm_num : (2⁻¹ : ℝ) ≤ 1)
    exact one_le_one_div_of_lt_one hlam h21
  have htwo : ∀ j : Fin n, |(2 : ℝ)| ≤ 1 / lam := fun _ => by
    rw [abs_two]
    exact two_le_one_div_of_le_half hlam hlam2
  have hc : ∀ j, |(if j ≤ min i l then (2 : ℝ) else 1)| ≤ 1 / lam := by
    intro j
    by_cases hj : j ≤ min i l
    · rw [if_pos hj]
      exact htwo j
    · rw [if_neg hj]
      exact hone j
  rw [integral_congr_ae (ae_of_all _ fun ω => temperedAsianPair_prod_eq i l ω),
    integral_temperedExpProd_eq hν hlam hlaw hiid hc hmea (Finset.Iic (max i l))]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ≤ min i l
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]

/-- **Exact `E[A²]`** for the arithmetic average of `n` fixings under i.i.d. tempered
increments, on the strip `λ ≤ 1/2`. In closed form the summand is
`S₀² · m₂^{min(i,l)+1} · m₁^{|i−l|}` with `m₂ = m(2)`, `m₁ = m(1)`.

**The strip tightening is the point**: `E[A]` needs only `λ ≤ 1` (each increment
enters at `θ = 1`), but the shared fixings of a pair enter at `θ = 2`, so matching
the second moment requires `λ ≤ 1/2` — strictly more tempering than matching the
first. At `λ = 1/2` exactly, `m(2)` is finite (the strip edge belongs to the finite
side, `TemperedT.integrable_exp_mul_temperedTPDFReal`), so the boundary is included. -/
theorem integral_temperedAsianSq_eq (hν : 0 < ν) (hlam : 0 < lam) (hlam2 : lam ≤ 2⁻¹)
    (hlaw : ∀ j, HasLaw (X j) (temperedTMeasure ν lam) P) (hiid : iIndepFun X P)
    (hmea : ∀ j, Measurable (X j)) (S₀ : ℝ) :
    (∫ ω, (S₀ / (n : ℝ) * ∑ i : Fin n, ∏ j ∈ Finset.Iic i, Real.exp (X j ω)) ^ 2 ∂P)
      = (S₀ / (n : ℝ)) ^ 2 * ∑ i : Fin n, ∑ l : Fin n, ∏ j ∈ Finset.Iic (max i l),
          (if j ≤ min i l then temperedExpMoment ν lam 2 else temperedExpMoment ν lam 1) := by
  have h21 : lam ≤ 1 := le_trans hlam2 (by norm_num : (2⁻¹ : ℝ) ≤ 1)
  have hone : ∀ j : Fin n, |(1 : ℝ)| ≤ 1 / lam := fun _ => by
    rw [abs_one]
    exact one_le_one_div_of_lt_one hlam h21
  set g : Fin n → Ω → ℝ :=
    fun i ω => ∏ j ∈ Finset.Iic i, Real.exp (X j ω) with hgdef
  have hint : ∀ i l : Fin n, Integrable (fun ω => g i ω * g l ω) P := by
    intro i l
    have htwo : ∀ j : Fin n, |(2 : ℝ)| ≤ 1 / lam := fun _ => by
      rw [abs_two]
      exact two_le_one_div_of_le_half hlam hlam2
    have hc : ∀ j, |(if j ≤ min i l then (2 : ℝ) else 1)| ≤ 1 / lam := by
      intro j
      by_cases hj : j ≤ min i l
      · rw [if_pos hj]
        exact htwo j
      · rw [if_neg hj]
        exact hone j
    have h := integrable_temperedExpProd hν hlam hlaw hiid hc hmea (Finset.Iic (max i l))
    refine h.congr (ae_of_all _ fun ω => ?_)
    rw [hgdef]
    exact (temperedAsianPair_prod_eq i l ω).symm
  have hexpand : (fun ω => (S₀ / (n : ℝ) * ∑ i : Fin n, g i ω) ^ 2)
      = fun ω => ∑ i : Fin n, ∑ l : Fin n,
          S₀ / (n : ℝ) * (S₀ / (n : ℝ) * (g i ω * g l ω)) := by
    funext ω
    rw [pow_two, Finset.mul_sum Finset.univ _ (S₀ / (n : ℝ)), Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun l _ => by ring
  rw [hexpand, integral_finsetSum
      (f := fun i ω => ∑ l : Fin n, S₀ / (n : ℝ) * (S₀ / (n : ℝ) * (g i ω * g l ω)))
      Finset.univ fun i _ => integrable_finsetSum
        (f := fun l ω => S₀ / (n : ℝ) * (S₀ / (n : ℝ) * (g i ω * g l ω)))
        Finset.univ fun l _ =>
        Integrable.const_mul (Integrable.const_mul (hint i l) (S₀ / (n : ℝ)))
          (S₀ / (n : ℝ)),
    Finset.mul_sum Finset.univ (fun i => ∑ l : Fin n, ∏ j ∈ Finset.Iic (max i l),
          (if j ≤ min i l then temperedExpMoment ν lam 2 else temperedExpMoment ν lam 1))
      ((S₀ / (n : ℝ)) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum
      (f := fun l ω => S₀ / (n : ℝ) * (S₀ / (n : ℝ) * (g i ω * g l ω)))
      Finset.univ fun l _ =>
      Integrable.const_mul (Integrable.const_mul (hint i l) (S₀ / (n : ℝ)))
        (S₀ / (n : ℝ))]
  rw [Finset.mul_sum Finset.univ _ ((S₀ / (n : ℝ)) ^ 2)]
  refine Finset.sum_congr rfl fun l (_ : l ∈ (Finset.univ : Finset (Fin n))) => ?_
  rw [hgdef]
  simp only []
  rw [integral_const_mul, integral_const_mul,
    integral_temperedAsianPair_eq hν hlam hlam2 hlaw hiid hmea i l, ← mul_assoc,
    ← pow_two]

/-! ### The Turnbull–Wakeman moment-matched ansatz -/

/-- The moment-matched effective volatility: solving `E[A²] = E[A]² · e^{σ²T}` for
`σ`. Meaningful when `E[A²] ≥ E[A]² > 0` and `T > 0`; otherwise the value follows
Mathlib's `Real.log`/`Real.sqrt` conventions and carries no pricing meaning. -/
noncomputable def twEffVol (EA EA2 T : ℝ) : ℝ :=
  Real.sqrt (Real.log (EA2 / EA ^ 2) / T)

/-- **The Turnbull–Wakeman moment-matched price** for the tempered Asian average:
the Garman normal form (`bsVGarman`) at forward `E[A]`, discount factor `DF`, and
the matched effective volatility from `E[A]` and `E[A²]`.

**Approximation, disclosed**: the moments `E[A]`, `E[A²]` are exact
(`integral_temperedAsian_eq`, `integral_temperedAsianSq_eq`) but the true average is
*not* lognormal under tempered increments, so this price is the TW approximation —
the standard practice move — and no exactness claim is made at any `n` (in particular
`n = 1`: a single tempered fixing is already non-lognormal, unlike the Gaussian
basket case of `BasketMomentMatching.lean` where the one-asset matching is exact). -/
noncomputable def twLognormalAnsatzPrice (EA EA2 K DF T : ℝ) : ℝ :=
  bsVGarman (DF * EA) K DF (twEffVol EA EA2 T) T

end Asian

end MathFin

/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.LocalVol.ForwardSmile
public import MathFin.Probability.Gaussian.GaussianCDFDeriv
public import MathFin.Models.BlackScholes.American.AmericanQDPlusLimits
public import MathFin.Probability.Gaussian.NormalTail
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The premium-adjusted call delta has a unique maximum in the strike

When the premium of an FX option is paid in the foreign currency, the
**premium-adjusted** forward delta of a call struck at `K` on forward `F` is the Black
delta net of the premium, `Δ(K) = (K/F)·Φ(d₋(K))`. Inverting it for a strike, given a
delta `δ`, is where its shape matters: the adjusted delta has a single interior maximum
(proved below). Hence a delta below the maximum has at most one strike on each side of the
maximiser, a delta equal to the maximum has exactly one, and a delta above it has none;
choosing the strike to the right of the maximiser is one way to make the inversion
single-valued, and the facts proved here are what make that choice well posed.

This file proves that picture on the flat Black slice, in the library's `(k, w)`
coordinates (log-strike `k = log(K/F)`, total variance `w = σ²T`, as in
`MathFin.Models.LocalVol.ForwardSmile`), where `paDelta k w = e^k·Φ(dmi k w)`.

* The stationarity equation `√w·Φ(x) = φ(x)` (the zero of `paStat √w`) in the lower
  normal argument `x = d₋` has exactly one root, and it lies above `−√w`
  (`paStat_neg_of_le`, `exists_paStat_root`, `paStat_sign_of_root`, `paStat_root_unique`).
* Hence the adjusted delta has a unique stationary log-strike `k*` (`exists_isPaMax`,
  `IsPaMax.unique`), below `w/2`, that is `K* < F·e^{w/2}`, a bracket that does not depend
  on any requested delta; the adjusted delta is strictly increasing on `(−∞, k*]` and
  strictly decreasing on `[k*, ∞)` (`IsPaMax.strictMonoOn`, `IsPaMax.strictAntiOn`), so
  `k*` is the global maximiser (`IsPaMax.le`).
* The adjusted delta is positive and tends to `0` as `k → ∞` (`paDelta_pos`,
  `paDelta_le_of_ge`, `tendsto_paDelta_atTop`), so a quoted delta `δ > 0` has a strike on
  the right branch **iff** `δ ≤ Δ(k*)`, that strike is unique, and above the maximum there
  is no strike at all (`IsPaMax.exists_right_iff`, `IsPaMax.right_unique`,
  `IsPaMax.no_strike_of_gt`); `paDelta_domain` bundles the statement.

## Scope

What is proved is the shape of the delta function over the reals, with `w > 0` as the
only hypothesis. Not proved: the lognormal dynamics behind the Black delta (the slice is
taken as the Gaussian argument `d₋`); the bound of the adjusted delta by the unadjusted
delta `Φ(d₊)`; the put branch; the spot-delta variant (the same function scaled by a
foreign discount factor); and the numerical root-finding that a library routine runs on
this function.

## Tags

premium-adjusted delta, FX smile, delta strike, unimodality, strike from delta,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real Filter Topology ProbabilityTheory Set
open MathFin.ForwardSmile (dmi dmi_eq)

/-! ## The stationarity function in the normal argument -/

/-- The sign of the derivative of the adjusted delta, in the lower normal argument `x`:
`paStat s x = s·Φ(x) − φ(x)`, with `s = √w`. -/
noncomputable def paStat (s x : ℝ) : ℝ := s * Phi x - gaussianPDFReal 0 1 x

theorem hasDerivAt_paStat (s x : ℝ) :
    HasDerivAt (paStat s) (gaussianPDFReal 0 1 x * (s + x)) x := by
  have h := ((hasDerivAt_Phi x).const_mul s).sub (hasDerivAt_gaussianPDFReal_zero_one x)
  exact h.congr_deriv (by ring)

theorem continuous_paStat (s : ℝ) : Continuous (paStat s) :=
  continuous_iff_continuousAt.2 fun x ↦ (hasDerivAt_paStat s x).continuousAt

/-- `paStat s` is strictly decreasing on `(−∞, −s]`. -/
theorem paStat_strictAntiOn {s : ℝ} : StrictAntiOn (paStat s) (Iic (-s)) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic _) (continuous_paStat s).continuousOn ?_
  intro y hy
  rw [interior_Iic] at hy
  rw [(hasDerivAt_paStat s y).deriv]
  exact mul_neg_of_pos_of_neg (gaussianPDFReal_pos 0 1 y one_ne_zero) (by simp at hy; linarith)

/-- `paStat s` is strictly increasing on `[−s, ∞)`. -/
theorem paStat_strictMonoOn {s : ℝ} : StrictMonoOn (paStat s) (Ici (-s)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (continuous_paStat s).continuousOn ?_
  intro y hy
  rw [interior_Ici] at hy
  rw [(hasDerivAt_paStat s y).deriv]
  exact mul_pos (gaussianPDFReal_pos 0 1 y one_ne_zero) (by simp at hy; linarith)

/-- **`paStat` is negative on `(−∞, −s]`**: the Mills bound gives `paStat s x ≤ (s+x)Φ(x)`,
and the strict monotonicity on the left of `−s` turns that into strictness at `−s`. -/
theorem paStat_neg_of_le {s x : ℝ} (hx : x ≤ -s) : paStat s x < 0 := by
  have hmills : ∀ y : ℝ, y < -s → paStat s y < 0 := by
    intro y hy
    have h1 := neg_mul_Phi_le_gaussianPDFReal y
    have h2 := Phi_pos y
    unfold paStat
    nlinarith
  rcases hx.lt_or_eq with h | h
  · exact hmills x h
  · have hlt : paStat s (-s) < paStat s (-s - 1) :=
      paStat_strictAntiOn (mem_Iic.2 (by linarith : -s - 1 ≤ -s)) (mem_Iic.2 le_rfl)
        (by linarith)
    rw [h]
    exact lt_trans hlt (hmills _ (by linarith))

theorem tendsto_paStat_atTop {s : ℝ} : Tendsto (paStat s) atTop (𝓝 s) := by
  have h := (tendsto_Phi_atTop.const_mul s).sub tendsto_gaussianPDFReal_zero_one_atTop
  have e : paStat s = fun x ↦ s * Phi x - gaussianPDFReal 0 1 x := rfl
  rw [e]
  simpa using h

/-- **Existence of the root**: for `s > 0`, `paStat s` has a zero. -/
theorem exists_paStat_root {s : ℝ} (hs : 0 < s) : ∃ x, paStat s x = 0 := by
  have hev : ∀ᶠ x in atTop, 0 < paStat s x := tendsto_paStat_atTop.eventually (lt_mem_nhds hs)
  obtain ⟨x₁, hx₁, hx₁'⟩ := (hev.and (eventually_ge_atTop (-s))).exists
  have hneg := paStat_neg_of_le (s := s) (le_refl (-s))
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hx₁'
    (continuous_paStat s).continuousOn ⟨hneg.le, hx₁.le⟩
  exact ⟨x, hx⟩

/-- **The sign pattern around a root**: a zero `x₀` of `paStat s` lies above `−s`, and
`paStat s` is negative to its left and positive to its right. In particular the root is
unique. -/
theorem paStat_sign_of_root {s x₀ : ℝ} (h0 : paStat s x₀ = 0) :
    -s < x₀ ∧ (∀ y, y < x₀ → paStat s y < 0) ∧ (∀ y, x₀ < y → 0 < paStat s y) := by
  have hx₀ : -s < x₀ := by
    by_contra hcon
    have := paStat_neg_of_le (s := s) (not_lt.mp hcon)
    linarith
  refine ⟨hx₀, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · rcases le_or_gt y (-s) with h | h
    · exact paStat_neg_of_le h
    · have := paStat_strictMonoOn (s := s) (by simp; linarith : y ∈ Ici (-s))
        (by simp; linarith : x₀ ∈ Ici (-s)) hy
      linarith
  · have := paStat_strictMonoOn (s := s) (by simp; linarith : x₀ ∈ Ici (-s))
      (by simp; linarith : y ∈ Ici (-s)) hy
    linarith

theorem paStat_root_unique {s x₁ x₂ : ℝ} (h₁ : paStat s x₁ = 0) (h₂ : paStat s x₂ = 0) :
    x₁ = x₂ := by
  obtain ⟨-, hl₁, hr₁⟩ := paStat_sign_of_root h₁
  rcases lt_trichotomy x₁ x₂ with h | h | h
  · have := hr₁ x₂ h
    linarith
  · exact h
  · have := hl₁ x₂ h
    linarith

/-! ## The adjusted delta in log-strike coordinates -/

/-- **The premium-adjusted forward call delta** on the flat slice, in `(k, w)` coordinates:
`Δ(k, w) = e^k·Φ(d₋)` with `d₋ = dmi k w` (`K/F = e^k`). -/
noncomputable def paDelta (k w : ℝ) : ℝ := exp k * Phi (dmi k w)

theorem paDelta_pos (k w : ℝ) : 0 < paDelta k w := mul_pos (exp_pos k) (Phi_pos _)

theorem hasDerivAt_dmi (w k : ℝ) :
    HasDerivAt (fun k ↦ dmi k w) (-1 / √w) k := by
  have e : (fun k ↦ dmi k w) = fun k ↦ -k / √w - √w / 2 := funext fun k ↦ dmi_eq k w
  rw [e]
  exact (((hasDerivAt_id k).neg.div_const (√w)).sub_const (√w / 2)).congr_deriv (by simp)

/-- **The derivative of the adjusted delta** is `(e^k/√w)·paStat √w (d₋)`: its sign is the sign
of `paStat`, whose unique zero is the stationarity condition `√w·Φ(d₋) = φ(d₋)`. -/
theorem hasDerivAt_paDelta {w : ℝ} (hw : 0 < w) (k : ℝ) :
    HasDerivAt (fun k ↦ paDelta k w) (exp k / √w * paStat (√w) (dmi k w)) k := by
  have hs : √w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have h := (hasDerivAt_exp k).mul ((hasDerivAt_Phi (dmi k w)).comp k (hasDerivAt_dmi w k))
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, paStat]
  field_simp
  ring

theorem continuous_paDelta {w : ℝ} (hw : 0 < w) : Continuous (fun k ↦ paDelta k w) :=
  continuous_iff_continuousAt.2 fun k ↦ (hasDerivAt_paDelta hw k).continuousAt

theorem dmi_strictAnti {w : ℝ} (hw : 0 < w) : StrictAnti (fun k ↦ dmi k w) := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  intro a b hab
  simp only [dmi_eq]
  have h : -a / √w - -b / √w = (b - a) / √w := by ring
  have := div_pos (sub_pos.2 hab) hs
  linarith

/-- **`k` is the stationary log-strike of the adjusted delta**: the lower normal argument
at `k` is a zero of `paStat √w`, i.e. `√w·Φ(d₋) = φ(d₋)`. -/
def IsPaMax (w k : ℝ) : Prop := paStat (√w) (dmi k w) = 0

/-- **The stationary log-strike exists, below `w/2`**: `K* < F·e^{w/2}`, whatever delta
is requested. -/
theorem exists_isPaMax {w : ℝ} (hw : 0 < w) : ∃ k, IsPaMax w k ∧ k < w / 2 := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  have hs2 : √w * √w = w := Real.mul_self_sqrt hw.le
  obtain ⟨x₀, hx₀⟩ := exists_paStat_root hs
  have hk : dmi (-√w * x₀ - w / 2) w = x₀ := by
    rw [dmi_eq]
    field_simp
    nlinarith [hs2]
  refine ⟨-√w * x₀ - w / 2, ?_, ?_⟩
  · unfold IsPaMax
    rw [hk]
    exact hx₀
  · have hgt := (paStat_sign_of_root hx₀).1
    have key : (dmi (-√w * x₀ - w / 2) w + √w) * √w = w / 2 - (-√w * x₀ - w / 2) := by
      rw [dmi_eq]
      field_simp
      nlinarith [hs2]
    rw [hk] at key
    have : 0 < (x₀ + √w) * √w := mul_pos (by linarith) hs
    linarith

theorem IsPaMax.unique {w k₁ k₂ : ℝ} (hw : 0 < w) (h₁ : IsPaMax w k₁) (h₂ : IsPaMax w k₂) :
    k₁ = k₂ :=
  (dmi_strictAnti hw).injective (paStat_root_unique h₁ h₂)

theorem IsPaMax.strictMonoOn {w k₀ : ℝ} (hw : 0 < w) (h : IsPaMax w k₀) :
    StrictMonoOn (fun k ↦ paDelta k w) (Iic k₀) := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  refine strictMonoOn_of_deriv_pos (convex_Iic _) (continuous_paDelta hw).continuousOn ?_
  intro k hk
  rw [interior_Iic] at hk
  rw [(hasDerivAt_paDelta hw k).deriv]
  have hlt : dmi k₀ w < dmi k w := dmi_strictAnti hw (mem_Iio.1 hk)
  exact mul_pos (div_pos (exp_pos k) hs) ((paStat_sign_of_root h).2.2 _ hlt)

theorem IsPaMax.strictAntiOn {w k₀ : ℝ} (hw : 0 < w) (h : IsPaMax w k₀) :
    StrictAntiOn (fun k ↦ paDelta k w) (Ici k₀) := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  refine strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_paDelta hw).continuousOn ?_
  intro k hk
  rw [interior_Ici] at hk
  rw [(hasDerivAt_paDelta hw k).deriv]
  have hlt : dmi k w < dmi k₀ w := dmi_strictAnti hw (mem_Ioi.1 hk)
  exact mul_neg_of_pos_of_neg (div_pos (exp_pos k) hs) ((paStat_sign_of_root h).2.1 _ hlt)

/-- **The stationary strike is the global maximiser**. -/
theorem IsPaMax.le {w k₀ : ℝ} (hw : 0 < w) (h : IsPaMax w k₀) (k : ℝ) :
    paDelta k w ≤ paDelta k₀ w := by
  rcases le_total k k₀ with hk | hk
  · exact (h.strictMonoOn hw).monotoneOn (mem_Iic.2 hk) (mem_Iic.2 le_rfl) hk
  · exact (h.strictAntiOn hw).antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk) hk

/-! ## The right branch and the domain of the strike solve -/

/-- **A Gaussian tail bound on the adjusted delta**: for `k ≥ w + 1` the Mills bound gives
`Δ(k, w) ≤ (√(2π))⁻¹·e^{−k/(2w)}`. -/
theorem paDelta_le_of_ge {w k : ℝ} (hw : 0 < w) (hk : w + 1 ≤ k) :
    paDelta k w ≤ (√(2 * π))⁻¹ * exp (-k / (2 * w)) := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  have hs2 : √w * √w = w := Real.mul_self_sqrt hw.le
  have hks : √w ≤ k := by nlinarith [sq_nonneg (√w - 1)]
  have hxle : dmi k w ≤ -1 := by
    rw [dmi_eq]
    have : 1 ≤ k / √w := (one_le_div hs).2 hks
    rw [neg_div]
    linarith
  have hΦ : Phi (dmi k w) ≤ gaussianPDFReal 0 1 (dmi k w) := by
    have h1 := neg_mul_Phi_le_gaussianPDFReal (dmi k w)
    nlinarith [Phi_nonneg (dmi k w)]
  have hn : gaussianPDFReal 0 1 (dmi k w) = (√(2 * π))⁻¹ * exp (-(dmi k w) ^ 2 / 2) := by
    simp [gaussianPDFReal]
  have hx2 : (dmi k w) ^ 2 = k ^ 2 / w + k + w / 4 := by
    have hs3 : √w ^ 2 = w := Real.sq_sqrt hw.le
    rw [dmi_eq]
    field_simp
    rw [hs3]
    ring
  have hexp : k + -(dmi k w) ^ 2 / 2 ≤ -k / (2 * w) := by
    rw [hx2]
    have key : k * (w + 1) ≤ k ^ 2 + w ^ 2 / 4 := by nlinarith
    have : k + -(k ^ 2 / w + k + w / 4) / 2 + k / (2 * w)
        = (k * (w + 1) - k ^ 2 - w ^ 2 / 4) / (2 * w) := by
      field_simp
      ring
    have h2 : (k * (w + 1) - k ^ 2 - w ^ 2 / 4) / (2 * w) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h3 : -k / (2 * w) = -(k / (2 * w)) := neg_div _ _
    linarith
  unfold paDelta
  calc exp k * Phi (dmi k w) ≤ exp k * gaussianPDFReal 0 1 (dmi k w) :=
        mul_le_mul_of_nonneg_left hΦ (exp_pos k).le
    _ = (√(2 * π))⁻¹ * exp (k + -(dmi k w) ^ 2 / 2) := by
        rw [hn, exp_add]; ring
    _ ≤ (√(2 * π))⁻¹ * exp (-k / (2 * w)) := by
        gcongr

/-- **The adjusted delta vanishes at large strikes.** -/
theorem tendsto_paDelta_atTop {w : ℝ} (hw : 0 < w) :
    Tendsto (fun k ↦ paDelta k w) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k : ℝ ↦ -k / (2 * w)) atTop atBot := by
    have h : Tendsto (fun x : ℝ ↦ x / (2 * w)) atTop atTop :=
      tendsto_id.atTop_div_const (by positivity : 0 < 2 * w)
    exact (tendsto_neg_atTop_atBot.comp h).congr fun x ↦ by simp [neg_div]
  have hup : Tendsto (fun k : ℝ ↦ (√(2 * π))⁻¹ * exp (-k / (2 * w))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hlim).const_mul (√(2 * π))⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun k ↦ (paDelta_pos k w).le) ?_
  filter_upwards [eventually_ge_atTop (w + 1)] with k hk using paDelta_le_of_ge hw hk

/-- **A delta has a strike on the right branch iff it is at most the maximum**: for `δ > 0`,
the equation `Δ(k, w) = δ` has a solution `k ≥ k*` exactly when `δ ≤ Δ(k*, w)`. -/
theorem IsPaMax.exists_right_iff {w k₀ δ : ℝ} (hw : 0 < w) (h : IsPaMax w k₀) (hδ : 0 < δ) :
    (∃ k, k₀ ≤ k ∧ paDelta k w = δ) ↔ δ ≤ paDelta k₀ w := by
  constructor
  · rintro ⟨k, -, rfl⟩
    exact h.le hw k
  · intro hle
    have hev := (tendsto_paDelta_atTop hw).eventually (gt_mem_nhds hδ)
    obtain ⟨M, hM, hM'⟩ := (hev.and (eventually_ge_atTop k₀)).exists
    obtain ⟨k, hk, hkδ⟩ := intermediate_value_Icc' hM'
      (continuous_paDelta hw).continuousOn ⟨hM.le, hle⟩
    exact ⟨k, hk.1, hkδ⟩

/-- **The right-branch strike is unique.** -/
theorem IsPaMax.right_unique {w k₀ k₁ k₂ : ℝ} (hw : 0 < w) (h : IsPaMax w k₀)
    (h₁ : k₀ ≤ k₁) (h₂ : k₀ ≤ k₂) (e : paDelta k₁ w = paDelta k₂ w) : k₁ = k₂ :=
  (h.strictAntiOn hw).injOn (mem_Ici.2 h₁) (mem_Ici.2 h₂) e

/-- **Above the maximum there is no strike at all**, on either branch. -/
theorem IsPaMax.no_strike_of_gt {w k₀ δ : ℝ} (hw : 0 < w) (h : IsPaMax w k₀)
    (hδ : paDelta k₀ w < δ) (k : ℝ) : paDelta k w ≠ δ :=
  fun e ↦ absurd (e ▸ h.le hw k) (not_le.2 hδ)

/-- **The domain of the premium-adjusted strike solve** (headline). For every total variance
`w > 0` there is a log-strike `k₀ < w/2` (`K* < F·e^{w/2}`, independently of any delta) that is
the unique stationary point of the adjusted delta (`IsPaMax`), with the delta strictly
increasing on `(−∞, k₀]`, strictly decreasing on `[k₀, ∞)`, tending to `0` at large strikes and
never exceeding its value at `k₀`; a delta `δ > 0` has a strike at or right of `k₀` iff
`δ ≤ Δ(k₀, w)`, that strike is unique, and a delta above `Δ(k₀, w)` has no strike at all. -/
theorem paDelta_domain {w : ℝ} (hw : 0 < w) :
    ∃ k₀ : ℝ, k₀ < w / 2 ∧ IsPaMax w k₀ ∧ (∀ k, IsPaMax w k → k = k₀) ∧
      StrictMonoOn (fun k ↦ paDelta k w) (Iic k₀) ∧
      StrictAntiOn (fun k ↦ paDelta k w) (Ici k₀) ∧
      Tendsto (fun k ↦ paDelta k w) atTop (𝓝 0) ∧
      (∀ k, paDelta k w ≤ paDelta k₀ w) ∧
      (∀ δ, 0 < δ → ((∃ k, k₀ ≤ k ∧ paDelta k w = δ) ↔ δ ≤ paDelta k₀ w)) ∧
      (∀ k₁ k₂, k₀ ≤ k₁ → k₀ ≤ k₂ → paDelta k₁ w = paDelta k₂ w → k₁ = k₂) ∧
      (∀ δ, paDelta k₀ w < δ → ∀ k, paDelta k w ≠ δ) := by
  obtain ⟨k₀, h, hlt⟩ := exists_isPaMax hw
  exact ⟨k₀, hlt, h, fun k hk ↦ hk.unique hw h, h.strictMonoOn hw, h.strictAntiOn hw,
    tendsto_paDelta_atTop hw, h.le hw, fun δ hδ ↦ h.exists_right_iff hw hδ,
    fun _ _ h₁ h₂ e ↦ h.right_unique hw h₁ h₂ e, fun _ hδ k ↦ h.no_strike_of_gt hw hδ k⟩

end MathFin

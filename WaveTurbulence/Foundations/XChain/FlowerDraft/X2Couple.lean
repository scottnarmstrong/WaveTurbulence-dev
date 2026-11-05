/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Est
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Gates
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Params
public import WaveTurbulence.Foundations.XChain.FlowerDraft.GateProbes

/-!
# X2, part 3: the couple second moments of `fixedpoint` Part 1

TARGET L2309–L2312, (trterm1):
- `𝔼_p|a^tr_k(t)|² ≤ L²⟨k⟩^{−4Λ_{p+1}}`;
- the same for `ℒ₀` with an extra `e^{−100N_{p+1}}`;
- the same for `∂_t a^tr` and `∂_t ℒ₀` with an extra `L^{100d}`.

Here `∂_t` is the Duhamel integrand at the root, `𝒞₊(𝒥_l(t), 𝒥̄_m(t), 𝒥_r(t))`: the "extra `δ(t_𝔯 − t)`"
of T L2312. X3 (`fixedpoint`) proves that it is the time derivative.

The proof has two layers.
1. **The expansion** `𝔼_p|X|² = ∑_{N ≤ N_{p+1}^4} coupleSum_N + 𝓔`, by T.cmattr. It is the **obligation
   `OX3Cpl`** (O-X3-CPL), stated exactly below.
2. **The bounds** (`cplMoments_of_gates`, proved).
   - `a^tr`: `coupleSum_tr` gives B1.2's `truncSumC`. B1.2 (2)(b) bounds it by the Taylor term `𝒰_{N/2}` plus
     `≤ ⟨k⟩^{−4Λ}δ^{2νN}`, and B1.5 bounds `𝒰_n ≤ C₂(C₁δ)^n ⟨k⟩^{−4Λ}`.
   - `ℒ₀` and the derivatives: B1.12 clause (2), with `δ^{νN}` and the kind `ℒ₀` forcing `N ≥ 2(N_{p+1}+1)`.
   - The losses `C₂`, `L^{100d}` are absorbed by `L` large, and `e^{−N_{p+1}}` beats `L^{100d}` (`N_ge_log`).
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence

namespace X2E

/-! ## `∂_t a^tr`, `∂_t ℒ₀` -/

section Dt

variable (L γ δ : ℝ) {d : ℕ}

/-- `∂_t 𝒥_𝒯(t)`: for `𝒯 = node l m r`, the Duhamel integrand `𝒞₊(𝒥_l(t), 𝒥̄_m(t), 𝒥_r(t))`; `0` for `•`. -/
noncomputable def treeTermDt (p : ℕ) : TTree → ((Fin d → ℤ) → ℂ) → ℝ → (Fin d → ℤ) → ℂ
  | .leaf, _, _, _ => 0
  | .node l m r, b, t, n => aNonlin L γ δ 1 t (treeTerm L γ δ p l b t)
      (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b t k)) (treeTerm L γ δ p r b t) n

/-- `∂_t a^tr = ∑_{N ≤ Ntr} ∑_{n(𝒯) = N} ∂_t 𝒥_𝒯`. -/
noncomputable def aTrDt (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑ N ∈ Finset.range (Ntr + 1), ∑ᶠ (T : TTree) (_ : T.order = N), treeTermDt L γ δ p T b t n

/-- The `𝒥`-slots of `ℒ₀` at time `t`. -/
noncomputable def slotValAt (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) : Slot Ntr → ℝ → (Fin d → ℤ) → ℂ
  | none, _ => 0
  | some N, t => treeTermN L γ δ p N b t

/-- `∂_t ℒ₀`: the integrand of `ℒ₀` (`Lop … 0`) at time `t`. -/
noncomputable def L0Dt (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = 0 ∧ (0 = 0 → Ntr ≤ slotOrder x)),
    aNonlin L γ δ 1 t (slotValAt L γ δ p Ntr b x.1 t)
      (fun m => (starRingEnd ℂ) (slotValAt L γ δ p Ntr b x.2.1 t m)) (slotValAt L γ δ p Ntr b x.2.2 t) n

end Dt

/-- The four couple quantities of `fixedpoint` Part 1. -/
inductive CplVar : Type
  | aTr | L0 | aTrDt | L0Dt

/-- The tree kind of a couple quantity. -/
def CplVar.kind : CplVar → TreeKind
  | .aTr => .tr | .L0 => .L0 | .aTrDt => .tr | .L0Dt => .L0

/-- Whether a couple quantity carries `∂_t`. -/
def CplVar.dt : CplVar → Bool
  | .aTr => false | .L0 => false | .aTrDt => true | .L0Dt => true

/-- The couple quantity built from `a(p)`. -/
noncomputable def cplRand (P : WTParams) (aP : (Fin P.d → ℤ) → ℂ) (p : ℕ) (v : CplVar) (t : ℝ)
    (n : Fin P.d → ℤ) : ℂ :=
  match v with
  | .aTr => aTr P.L P.γ P.δ p (P.N (p + 1)) aP t n
  | .L0 => Lop P.L P.γ P.δ p (P.N (p + 1)) aP 0 (fun _ _ => 0) t n
  | .aTrDt => aTrDt P.L P.γ P.δ p (P.N (p + 1)) aP t n
  | .L0Dt => L0Dt P.L P.γ P.δ p (P.N (p + 1)) aP t n

/-! ## The obligation O-X3-CPL -/

/-- The body of O-X3-CPL. -/
def OX3CplBody.{u} (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ (n : Fin P.d → ℤ) (v : CplVar),
    Integrable (fun ω => ‖cplRand P (a ω p) p v t n‖ ^ 2) (μ.restrict (Fev p)) ∧
    ‖(((∫ ω in Fev p, ‖cplRand P (a ω p) p v t n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          coupleSum P (inputsF P R) p N v.kind v.dt t (latticePoint P.L n)‖ ≤
      jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) * Real.exp (-(101 * P.N (p + 1) : ℝ))

/-- **Obligation O-X3-CPL** (T L2309–L2312, the moment expansions of T.fp.part1, following T.cmattr). For
`a^tr`, `ℒ₀`, `∂_t a^tr` and `∂_t ℒ₀` built from `a(p)`:
- `|X_k(t)|²` is integrable on `F_p`;
- `𝔼_p|X_k(t)|² = ∑_{N ≤ N_{p+1}^4} coupleSum_N(t, k) + 𝓔` with `|𝓔| ≤ ⟨k⟩^{−4Λ_{p+1}} e^{−101N_{p+1}}`. Here
  `coupleSum` is the couple sum of B1.12 clause (2), and of B1.2 through `coupleSum_tr` for `a^tr`.

Proof plan as for O-X2-EXP, with couples (two trees, signature `(+,−)`) in place of flower gardens. It is **not**
assumed as an axiom: `cplMoments_of_gates` takes it as a hypothesis. -/
def OX3Cpl.{u} : Prop := WTPrefix OX3CplBody.{u}

end X2E

/-! ## `WTPrefix` combinators -/

/-- `WTPrefixP` gives `WTPrefix` for some `P`. -/
theorem WTPrefixP.toWTPrefix {Q : ℕ → WTParams → Prop} (h : WTPrefixP Q) : WTPrefix fun P => ∃ Pm, Q Pm P := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  obtain ⟨δ₀, hδ₀, H⟩ := H P₀ le_rfl
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => ⟨P₀, H L hL⟩⟩

/-- Two `WTPrefix` statements combine when the first does not depend on `C₁, C₂`. -/
theorem WTPrefix.and {Q₁ Q₂ : WTParams → Prop}
    (hC : ∀ (P : WTParams) (C₁ C₂ : ℝ), Q₁ P → Q₁ {P with C₁ := C₁, C₂ := C₂})
    (h₁ : WTPrefix Q₁) (h₂ : WTPrefix Q₂) : WTPrefix fun P => Q₁ P ∧ Q₂ P := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, H₁⟩ := h₁ d hd γ hγ
  obtain ⟨η₂, hη₂, H₂⟩ := h₂ d hd γ hγ
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁a, -, ν₁, hν₁, H₁⟩ := H₁ η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφ τ hτ φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, H₂⟩ := H₂ η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφ τ hτ φ hW
  refine ⟨C₁b, hC₁b, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, H₁⟩ := H₁ ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, H₂⟩ := H₂ ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, hL₁, H₁⟩ := H₁ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂b, hC₂b, L₂, hL₂, H₂⟩ := H₂ δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  exact ⟨C₂b, hC₂b, max L₁ L₂, hL₁.trans (le_max_left _ _), fun L hL =>
    ⟨hC _ C₁b C₂b (H₁ L ((le_max_left _ _).trans hL)), H₂ L ((le_max_right _ _).trans hL)⟩⟩

/-- `δ` small after `ν, C₁`, `L` large after `d, C₂`; and the standing positivity facts. -/
theorem WTPrefix.small {Q : WTParams → Prop} (h : WTPrefix Q) (f : ℝ → ℝ → ℝ)
    (hf : ∀ ν C₁, 0 < ν → 1 ≤ C₁ → 0 < f ν C₁) (g : ℕ → ℝ → ℝ) :
    WTPrefix fun P => Q P ∧ 3 ≤ P.d ∧ 0 < P.ν ∧ 1 ≤ P.C₁ ∧ 0 < P.δ ∧ P.δ ≤ f P.ν P.C₁ ∧ 1 ≤ P.C₂ ∧
      g P.d P.C₂ ≤ P.L ∧ 2 ≤ P.L := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨min δ₀ (f ν C₁), lt_min hδ₀ (hf ν C₁ hν.1 hC₁), fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  refine ⟨C₂, hC₂, max L₀ (g d C₂), hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  exact ⟨H L ((le_max_left _ _).trans hL), hd, hν.1, hC₁, hδ.1, hδ.2.trans (min_le_right _ _), hC₂,
    (le_max_right _ _).trans hL, hL₀.trans ((le_max_left _ _).trans hL)⟩

theorem WTPrefix.mono {Q Q' : WTParams → Prop} (h : WTPrefix Q) (hQ : ∀ P, Q P → Q' P) : WTPrefix Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ (H L hL)⟩

namespace X2E

/-! ## Constant independence -/

theorem R_update_x2' (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).R p = P.R p := R_update_x2 P C₁ C₂ p

theorem coupleRemainder_update_x2 (P : WTParams) (C₁ C₂ : ℝ) (R : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) :
    coupleRemainder {P with C₁ := C₁, C₂ := C₂} R p N t = coupleRemainder P R p N t := by
  funext k
  simp only [coupleRemainder, truncSumC, inputsF_update_x2, N_update_x2]

theorem layergardenBody_update_x2 (P : WTParams) (C₁ C₂ : ℝ) :
    Gates.LayergardenBody {P with C₁ := C₁, C₂ := C₂} = Gates.LayergardenBody P := by
  simp only [Gates.LayergardenBody, Induct.LayergardenBody, RemainderBound, coupleRemainder_update_x2, truncSum,
    inputsF_update_x2, WTParams.theta, WTParams.Lambda, N_update_x2, R_update_x2]

theorem OX3CplBody_update.{u} (P : WTParams) (C₁ C₂ : ℝ) :
    OX3CplBody.{u} {P with C₁ := C₁, C₂ := C₂} = OX3CplBody.{u} P := by
  simp only [OX3CplBody, AnsatzAt, truncSum, coupleSum, inputsF_update_x2, WTParams.theta, WTParams.Lambda,
    N_update_x2, R_update_x2, cplRand]

/-! ## Low orders of `ℒ₀` vanish -/

theorem coupleSum_L0_eq_zero_of_lt (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (dt : Bool) (t : ℝ)
    (k : Mom P.d) (hN : N < 2 * (P.N (p + 1) + 1)) : coupleSum P F p N .L0 dt t k = 0 := by
  classical
  unfold coupleSum
  refine finsum_eq_zero_of_forall_eq_zero fun LG => ?_
  rw [finsum_eq_dif, dite_eq_right_iff]
  intro h
  have hj : ∀ j, P.N (p + 1) + 1 ≤ LG.topOrder p j := fun j => (h.2.2.2.1 j).1
  have : 2 * (P.N (p + 1) + 1) ≤ LG.garden.order := by
    calc 2 * (P.N (p + 1) + 1) = ∑ _j : Fin 2, (P.N (p + 1) + 1) := by simp
      _ ≤ ∑ j, LG.topOrder p j := Finset.sum_le_sum fun j _ => hj j
      _ ≤ LG.garden.order := sum_topOrder_le_order LG p
  rw [h.2.2.1] at this
  omega

/-! ## The bounds -/

/-- The Part 1 bound of each couple quantity. -/
noncomputable def cplBound (P : WTParams) (p : ℕ) (n : Fin P.d → ℤ) : CplVar → ℝ
  | .aTr => jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ 2
  | .L0 => jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ 2 *
      Real.exp (-(100 * P.N (p + 1) : ℝ))
  | .aTrDt => jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ 2 * P.L ^ (100 * P.d : ℝ)
  | .L0Dt => jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ 2 * P.L ^ (100 * P.d : ℝ) *
      Real.exp (-(100 * P.N (p + 1) : ℝ))

/-- The body of the Part 1 moment bounds (T (trterm1) and its `ℒ₀`, `∂_t` variants). -/
def CplMomBody.{u} (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ (n : Fin P.d → ℤ) (v : CplVar),
    Integrable (fun ω => ‖cplRand P (a ω p) p v t n‖ ^ 2) (μ.restrict (Fev p)) ∧
    ∫ ω in Fev p, ‖cplRand P (a ω p) p v t n‖ ^ 2 ∂μ ≤ cplBound P p n v

/-! ### Scalar lemmas -/

theorem jbr_pos' {d : ℕ} (k : Mom d) : 0 < jbr k := Real.sqrt_pos.2 (by positivity)

/-- `⟨k⟩^{Λ} |F| ≤ M` gives `|F| ≤ ⟨k⟩^{−Λ} M`. -/
theorem le_jbr_rpow_neg {d : ℕ} {k : Mom d} {Λ : ℕ} {x M : ℝ} (h : jbr k ^ Λ * x ≤ M) :
    x ≤ jbr k ^ (-(Λ : ℝ)) * M := by
  have hj := pow_pos (jbr_pos' k) Λ
  rw [Real.rpow_neg (jbr_pos' k).le, Real.rpow_natCast, ← div_eq_inv_mul, le_div_iff₀ hj, mul_comm]
  exact h

/-- `∑_{N ∈ s} x^{⌊N/2⌋} ≤ 4` for `0 ≤ x ≤ 1/4`. -/
theorem sum_pow_half_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (s : Finset ℕ) :
    ∑ N ∈ s, x ^ (N / 2) ≤ 4 := by
  have hterm : ∀ N, x ^ (N / 2) ≤ 2 * (1 / 2 : ℝ) ^ N := by
    intro N
    calc x ^ (N / 2) ≤ (1 / 4 : ℝ) ^ (N / 2) := pow_le_pow_left₀ hx0 hx _
      _ = (1 / 2 : ℝ) ^ (2 * (N / 2)) := by rw [pow_mul]; norm_num
      _ ≤ 2 * (1 / 2 : ℝ) ^ N := by
          rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
          · rw [show 2 * (2 * m / 2) = 2 * m by omega]
            have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (2 * m)
            linarith
          · rw [show 2 * ((2 * m + 1) / 2) = 2 * m by omega, pow_succ]
            have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (2 * m)
            linarith
  calc ∑ N ∈ s, x ^ (N / 2) ≤ ∑ N ∈ s, 2 * (1 / 2 : ℝ) ^ N := Finset.sum_le_sum fun N _ => hterm N
    _ = 2 * ∑ N ∈ s, (1 / 2 : ℝ) ^ N := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * (1 / 2 : ℝ) ^ 0) := by
        gcongr
        exact sum_pow_le_two_mul (by norm_num) le_rfl s 0 fun _ _ => Nat.zero_le _
    _ = 4 := by norm_num

theorem real_le_of_complex {I e b : ℝ} {S : ℂ} (hI : 0 ≤ I) (hS : ‖S‖ ≤ b) (h : ‖((I : ℝ) : ℂ) - S‖ ≤ e) :
    I ≤ b + e := by
  have h1 : I = ‖((I : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hI]
  rw [h1]
  calc ‖((I : ℝ) : ℂ)‖ ≤ ‖S‖ + ‖((I : ℝ) : ℂ) - S‖ := norm_le_insert' _ _
    _ ≤ b + e := add_le_add hS h

/-- **The Part 1 couple moment bounds from the gates and O-X3-CPL.** -/
theorem cplMoments_of_gates.{u} (hG : LayergardenFlowerGate) (hL : Gates.LayergardenGate)
    (hW : Gates.WkeTaylorGate) (hC : OX3Cpl.{u}) : WTPrefix CplMomBody.{u} := by
  have h1 : WTPrefix fun P => (∃ Pm, B112Body Pm P) ∧ Gates.LayergardenBody P ∧ OX3CplBody.{u} P :=
    WTPrefix.and (fun P C₁ C₂ h => h.imp fun Pm hP => B112Body_const Pm P C₁ C₂ hP)
      hG.toWTPrefix (WTPrefix.and (fun P C₁ C₂ h => by rw [layergardenBody_update_x2]; exact h) hL hC)
  have h2 := (WTPrefix.and (fun P C₁ C₂ h => ⟨h.1.imp fun Pm hP => B112Body_const Pm P C₁ C₂ hP, by
        rw [layergardenBody_update_x2]; exact h.2.1, by rw [OX3CplBody_update]; exact h.2.2⟩) h1 hW).small
    (fun ν C₁ => min (Real.exp (-(101 / ν))) (1 / (4 * C₁)))
    (fun ν C₁ hν hC₁ => lt_min (Real.exp_pos _) (by positivity))
    (fun d C₂ => max (Real.exp (100 * d + 11)) (4 * C₂ + 3))
  refine h2.mono ?_
  rintro P ⟨⟨⟨⟨Pm, hB⟩, hLG, hX⟩, hWT⟩, hd, hν, hC₁, hδ, hδf, hC₂, hLg, hL2⟩
  intro Ω _ μ _ g hg p hp a Fev R E Et hA t ht n v
  obtain ⟨hint, hexp⟩ := hX Ω μ g hg p hp a Fev R E Et hA t ht n v
  refine ⟨hint, ?_⟩
  have hRB : RemainderBound P R p := fun q hq => (hA q hq).2.1.1
  set Ntr := P.N (p + 1)
  set k := latticePoint P.L n
  set J := jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ))
  have hJ0 : 0 ≤ J := Real.rpow_nonneg (jbr_pos' k).le _
  have hLpos : 0 < P.L := by linarith
  have hI0 : 0 ≤ ∫ ω in Fev p, ‖cplRand P (a ω p) p v t n‖ ^ 2 ∂μ :=
    setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => by positivity)
  -- small parameters
  have hδ1 : P.δ ≤ Real.exp (-(101 / P.ν)) := hδf.trans (min_le_left _ _)
  have hδ2 : P.δ ≤ 1 / (4 * P.C₁) := hδf.trans (min_le_right _ _)
  set q1 := P.δ ^ P.ν
  have hq10 : 0 ≤ q1 := Real.rpow_nonneg hδ.le _
  have hq1e : q1 ≤ Real.exp (-101) := by
    calc q1 ≤ Real.exp (-(101 / P.ν)) ^ P.ν := Real.rpow_le_rpow hδ.le hδ1 hν.le
      _ = Real.exp (-101) := by rw [← Real.exp_mul]; congr 1; field_simp
  have he101 : Real.exp (-101) ≤ 1 / 2 := by
    have := Real.add_one_le_exp (101 : ℝ)
    have h2 : Real.exp (-101) * Real.exp 101 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-101 : ℝ)]
  have hq1 : q1 ≤ 1 / 2 := hq1e.trans he101
  have hN0 : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _
  have hLlog := P.N_ge_log (by omega) ((le_max_left _ _).trans hLg) (p + 1)
  -- `L^{100d} ≤ e^{N - 10}`
  have hLpow : P.L ^ (100 * P.d : ℝ) ≤ Real.exp (Ntr - 10) := by
    rw [Real.rpow_def_of_pos hLpos]
    exact Real.exp_le_exp.2 (by nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ P.L)])
  have hexp101 : Real.exp (-(101 * Ntr : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- `ℒ₀`-type sums
  have hL0sum : ∀ dt : Bool, ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1),
      coupleSum P (inputsF P R) p N .L0 dt t k‖ ≤ J * Real.exp (-(100 * Ntr : ℝ)) := by
    intro dt
    have hterm : ∀ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .L0 dt t k‖ ≤
        if 2 * (Ntr + 1) ≤ N then J * P.L ^ (100 * P.d : ℝ) * q1 ^ N else 0 := by
      intro N hN
      split_ifs with hlow
      · have := (hB p hp R hRB).2 t ht k N (Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)) .L0 dt
          (fun h => absurd h (by intro h'; cases h'))
        refine this.trans (le_of_eq ?_)
        rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
      · rw [coupleSum_L0_eq_zero_of_lt P _ p N dt t k (not_le.1 hlow), norm_zero]
    calc ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), coupleSum P (inputsF P R) p N .L0 dt t k‖
        ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .L0 dt t k‖ := norm_sum_le _ _
      _ ≤ ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (2 * (Ntr + 1) ≤ ·), J * P.L ^ (100 * P.d : ℝ) * q1 ^ N := by
          rw [Finset.sum_filter]; exact Finset.sum_le_sum hterm
      _ = J * P.L ^ (100 * P.d : ℝ) * ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (2 * (Ntr + 1) ≤ ·), q1 ^ N := by
          rw [Finset.mul_sum]
      _ ≤ J * P.L ^ (100 * P.d : ℝ) * (2 * q1 ^ (2 * (Ntr + 1))) := by
          gcongr
          exact sum_pow_le_two_mul hq10 hq1 _ _ fun N hN => (Finset.mem_filter.1 hN).2
      _ ≤ J * Real.exp (Ntr - 10) * (2 * Real.exp (-101) ^ (2 * (Ntr + 1))) := by
          gcongr
      _ = J * (2 * Real.exp (Ntr - 10 - 202 * (Ntr + 1))) := by
          rw [← Real.exp_nat_mul, mul_assoc, ← mul_assoc (Real.exp _) 2, mul_comm (Real.exp _) 2,
            mul_assoc 2, ← Real.exp_add]
          push_cast; ring_nf
      _ ≤ J * Real.exp (-(100 * Ntr : ℝ)) := by
          gcongr
          have : Real.exp (Ntr - 10 - 202 * (Ntr + 1)) ≤ Real.exp (-(100 * Ntr : ℝ) - 1) :=
            Real.exp_le_exp.2 (by linarith)
          have h2 : 2 * Real.exp (-(100 * Ntr : ℝ) - 1) ≤ Real.exp (-(100 * Ntr : ℝ)) := by
            rw [Real.exp_sub]
            have := Real.add_one_le_exp (1 : ℝ)
            rw [mul_div_assoc']
            rw [div_le_iff₀ (Real.exp_pos 1)]
            nlinarith [Real.exp_pos (-(100 * Ntr : ℝ))]
          linarith
  have hL2' : (1 : ℝ) ≤ P.L ^ 2 := one_le_pow₀ (by linarith)
  have hLd1 : (1 : ℝ) ≤ P.L ^ (100 * P.d : ℝ) := Real.one_le_rpow (by linarith) (by positivity)
  cases v with
  | L0 =>
    have := real_le_of_complex hI0 (hL0sum false) hexp
    show _ ≤ J * P.L ^ 2 * Real.exp (-(100 * Ntr : ℝ))
    have he : Real.exp (-(101 * Ntr : ℝ)) ≤ Real.exp (-(100 * Ntr : ℝ)) := Real.exp_le_exp.2 (by linarith)
    have hee := Real.exp_pos (-(100 * Ntr : ℝ))
    have h4 := mul_le_mul_of_nonneg_left he hJ0
    have hJe := mul_nonneg hJ0 hee.le
    have hL4 : (4 : ℝ) ≤ P.L ^ 2 := by nlinarith
    have h5 : 2 * (J * Real.exp (-(100 * Ntr : ℝ))) ≤ J * P.L ^ 2 * Real.exp (-(100 * Ntr : ℝ)) := by
      have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ P.L ^ 2 by linarith) hJe
      linarith
    linarith
  | L0Dt =>
    have := real_le_of_complex hI0 (hL0sum true) hexp
    show _ ≤ J * P.L ^ 2 * P.L ^ (100 * P.d : ℝ) * Real.exp (-(100 * Ntr : ℝ))
    have he : Real.exp (-(101 * Ntr : ℝ)) ≤ Real.exp (-(100 * Ntr : ℝ)) := Real.exp_le_exp.2 (by linarith)
    have hee := Real.exp_pos (-(100 * Ntr : ℝ))
    have h3 : 2 * (J * Real.exp (-(100 * Ntr : ℝ))) ≤ J * P.L ^ 2 * P.L ^ (100 * P.d : ℝ) *
        Real.exp (-(100 * Ntr : ℝ)) := by
      have h2L : (2 : ℝ) ≤ P.L ^ 2 * P.L ^ (100 * P.d : ℝ) := by nlinarith
      have hJe := mul_nonneg hJ0 hee.le
      have := mul_le_mul_of_nonneg_right h2L hJe
      linarith
    have h4 := mul_le_mul_of_nonneg_left he hJ0
    linarith
  | aTrDt =>
    have hsum : ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), coupleSum P (inputsF P R) p N .tr true t k‖ ≤
        J * P.L ^ (100 * P.d : ℝ) * 2 := by
      calc _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .tr true t k‖ := norm_sum_le _ _
        _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), J * P.L ^ (100 * P.d : ℝ) * q1 ^ N := by
            refine Finset.sum_le_sum fun N hN => ?_
            have := (hB p hp R hRB).2 t ht k N (Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)) .tr true
              (fun _ => rfl)
            refine this.trans (le_of_eq ?_)
            rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
        _ = J * P.L ^ (100 * P.d : ℝ) * ∑ N ∈ Finset.range (Ntr ^ 4 + 1), q1 ^ N := by rw [Finset.mul_sum]
        _ ≤ J * P.L ^ (100 * P.d : ℝ) * (2 * q1 ^ 0) := by
            gcongr
            exact sum_pow_le_two_mul hq10 hq1 _ 0 fun _ _ => Nat.zero_le _
        _ = J * P.L ^ (100 * P.d : ℝ) * 2 := by ring
    have := real_le_of_complex hI0 hsum hexp
    show _ ≤ J * P.L ^ 2 * P.L ^ (100 * P.d : ℝ)
    have hJL := mul_nonneg hJ0 (le_trans zero_le_one hLd1)
    have hL4 : (4 : ℝ) ≤ P.L ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hexp101 hJ0
    have h5 : J ≤ J * P.L ^ (100 * P.d : ℝ) := le_mul_of_one_le_right hJ0 hLd1
    have h6 := mul_le_mul_of_nonneg_right hL4 hJL
    nlinarith
  | aTr =>
    have hWp := (hWT p hp).2.2
    have hLGp := hLG p hp R hRB t ⟨ht.1, ht.2.le⟩
    set x := P.C₁ * P.δ
    have hx0 : 0 ≤ x := mul_nonneg (by linarith) hδ.le
    have hx : x ≤ 1 / 4 := by
      have hC₁pos : 0 < P.C₁ := by linarith
      calc x ≤ P.C₁ * (1 / (4 * P.C₁)) := mul_le_mul_of_nonneg_left hδ2 hC₁pos.le
        _ = 1 / 4 := by field_simp
    set q2 := P.δ ^ (2 * P.ν)
    have hq20 : 0 ≤ q2 := Real.rpow_nonneg hδ.le _
    have hq2 : q2 ≤ 1 / 2 := by
      have : q2 = q1 ^ 2 := by
        simp only [q2, q1]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
        congr 1
        push_cast
        ring
      rw [this]
      nlinarith
    have hterm : ∀ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .tr false t k‖ ≤
        J * q2 ^ N + J * (P.C₂ * x ^ (N / 2)) := by
      intro N hN
      have hNle : N ≤ Ntr ^ 4 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)
      rw [WaveTurbulence.FlowerProbes.coupleSum_tr]
      have hcR := hLGp N hNle |>.2.2
      have hθ : 0 ≤ (4 * P.theta (p + 1) + P.theta p) / 5 := by
        unfold WTParams.theta
        have h20 : 0 ≤ P.η ^ 20 := by positivity
        positivity
      have hcast : (-(((4 * P.Lambda (p + 1) : ℕ)) : ℝ)) = -(4 * P.Lambda (p + 1) : ℝ) := by push_cast; ring
      have hcRpt := le_jbr_rpow_neg (norm_le_of_SNorm_le (by positivity) hcR k)
      have hU := le_jbr_rpow_neg (norm_le_of_SNormR_le (by positivity) (hWp (N / 2) t ⟨ht.1.le, ht.2.le⟩) k)
      rw [hcast] at hcRpt hU
      have hsplit : truncSumC P (inputsF P R) (p + 1) N t k = coupleRemainder P R p N t k +
          (if Even N then (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (N / 2) t k : ℂ) else 0) := by
        simp only [coupleRemainder]; ring
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine hcRpt.trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hJ0
        have hLθ : P.L ^ (-((4 * P.theta (p + 1) + P.theta p) / 5)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
        rw [show -(4 * P.theta (p + 1) + P.theta p) / 5 = -((4 * P.theta (p + 1) + P.theta p) / 5) by ring,
          Real.rpow_mul hδ.le, Real.rpow_natCast]
        exact mul_le_of_le_one_left (pow_nonneg hq20 _) hLθ
      · split_ifs
        · rw [Complex.norm_real, Real.norm_eq_abs]
          exact hU
        · rw [norm_zero]; exact mul_nonneg hJ0 (mul_nonneg (by linarith) (pow_nonneg hx0 _))
    have hsum : ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), coupleSum P (inputsF P R) p N .tr false t k‖ ≤
        J * 2 + J * (P.C₂ * 4) := by
      calc _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖coupleSum P (inputsF P R) p N .tr false t k‖ :=
            norm_sum_le _ _
        _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), (J * q2 ^ N + J * (P.C₂ * x ^ (N / 2))) :=
            Finset.sum_le_sum hterm
        _ = J * ∑ N ∈ Finset.range (Ntr ^ 4 + 1), q2 ^ N +
              J * (P.C₂ * ∑ N ∈ Finset.range (Ntr ^ 4 + 1), x ^ (N / 2)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ J * (2 * q2 ^ 0) + J * (P.C₂ * 4) := by
            gcongr
            · exact sum_pow_le_two_mul hq20 hq2 _ 0 fun _ _ => Nat.zero_le _
            · exact sum_pow_half_le hx0 hx _
        _ = J * 2 + J * (P.C₂ * 4) := by ring
    have := real_le_of_complex hI0 hsum hexp
    show _ ≤ J * P.L ^ 2
    have hL43 : 4 * P.C₂ + 3 ≤ P.L := (le_max_right _ _).trans hLg
    have hLL : P.L ≤ P.L ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hexp101 hJ0
    have h5 : 3 + 4 * P.C₂ ≤ P.L ^ 2 := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hJ0
    linarith

end X2E

end WaveTurbulence

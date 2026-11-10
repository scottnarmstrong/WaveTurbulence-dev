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

end X2E

end WaveTurbulence

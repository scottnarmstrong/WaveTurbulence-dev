/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Kernel

/-!
# X2, part 2: `flowerest1`, the moment bounds of the flower kernels

TARGET Prop `flowerest1` (L2279–L2305):
`𝔼_p|𝒦^ζ_{kk'}(t,s)|^{2P} ≤ ⟨k−ζk'⟩^{−4Λ_{p+1}P} L^{(100d)³P}`. For `𝒴`, `𝒲` there is an extra
`e^{−100N_{p+1}}`, and with the cutoffs an extra `M₁^{−80dP}` and `M₂^{−P/9}`. Here
`𝔼_p = ∫_{F_p} · dμ`, as in `AnsatzAt`.

The proof has two layers.
1. **The expansion** (T (flowerexp2), L2287–L2290). Its proof follows T.cmattr (Section `secduhamel`):
   `𝔼_p|𝒦|^{2P} = ∑_{𝒢 ∈ ℋ^tr_{p+1}, n(𝒢) ≤ N_{p+1}^4} K̃_𝒢 + 𝓔`, where the error `𝓔` contains an `E_p` or
   `Ẽ_p`, or has order `> N_{p+1}^4`. It is the **obligation `OX2Exp`**, stated exactly below. It needs the
   top-tree/attached-garden graft bijection that INDUCT is building for T.cmattr (HANDOFF).
2. **The bound** (`flowerest1_of_gates`, proved). The B1.12 gate bounds each order: `≤ B · δ^{2νN}`. Summing
   over `N` gives `2B` for `𝒳`. For `𝒴`, `𝒲` the kinds force `N ≥ 2P(N_{p+1}+1)` (`flowerSum_eq_zero_of_lt`),
   which gives `2B e^{−100N_{p+1}}` once `δ^{4ν} ≤ e^{−100}`. The error adds `B e^{−101N_{p+1}}`.

The gate enters as the Prop `LayergardenFlowerGate`, the verbatim statement of `Flower-Gate.lean`'s
`layergardenFlower` (probe: definitional equality). It is a hypothesis, never an axiom.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence

/-! ## `WTPrefixP` combinators -/

/-- Two `WTPrefixP` statements combine when the first does not depend on the constants `C₁, C₂`. -/
theorem WTPrefixP.and {Q₁ Q₂ : ℕ → WTParams → Prop}
    (hC : ∀ Pm (P : WTParams) (C₁ C₂ : ℝ), Q₁ Pm P → Q₁ Pm {P with C₁ := C₁, C₂ := C₂})
    (h₁ : WTPrefixP Q₁) (h₂ : WTPrefixP Q₂) : WTPrefixP fun Pm P => Q₁ Pm P ∧ Q₂ Pm P := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, H₁⟩ := h₁ d hd γ hγ
  obtain ⟨η₂, hη₂, H₂⟩ := h₂ d hd γ hγ
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁a, -, ν₁, hν₁, H₁⟩ := H₁ η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφ τ hτ φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, H₂⟩ := H₂ η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφ τ hτ φ hW
  refine ⟨C₁b, hC₁b, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨P₁, H₁⟩ := H₁ ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨P₂, H₂⟩ := H₂ ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨max P₁ P₂, fun Pm hPm => ?_⟩
  obtain ⟨δ₁, hδ₁, H₁⟩ := H₁ Pm ((le_max_left _ _).trans hPm)
  obtain ⟨δ₂, hδ₂, H₂⟩ := H₂ Pm ((le_max_right _ _).trans hPm)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, hL₁, H₁⟩ := H₁ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂b, hC₂b, L₂, hL₂, H₂⟩ := H₂ δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  exact ⟨C₂b, hC₂b, max L₁ L₂, hL₁.trans (le_max_left _ _), fun L hL =>
    ⟨hC _ _ C₁b C₂b (H₁ L ((le_max_left _ _).trans hL)),
      H₂ L ((le_max_right _ _).trans hL)⟩⟩

/-- `δ` may be taken below a positive function of `ν`, and `P` positive. -/
theorem WTPrefixP.small {Q : ℕ → WTParams → Prop} (h : WTPrefixP Q) (f : ℝ → ℝ) (hf : ∀ ν, 0 < ν → 0 < f ν) :
    WTPrefixP fun Pm P => Q Pm P ∧ 1 ≤ Pm ∧ 0 < P.ν ∧ 0 < P.δ ∧ P.δ ≤ f P.ν ∧ 2 ≤ P.L := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  refine ⟨max P₀ 1, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm ((le_max_left _ _).trans hPm)
  refine ⟨min δ₀ (f ν), lt_min hδ₀ (hf ν hν.1), fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL =>
    ⟨H L hL, (le_max_right _ _).trans hPm, hν.1, hδ.1, hδ.2.trans (min_le_right _ _), hL₀.trans hL⟩⟩

theorem WTPrefixP.mono {Q Q' : ℕ → WTParams → Prop} (h : WTPrefixP Q) (hQ : ∀ Pm P, Q Pm P → Q' Pm P) :
    WTPrefixP Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  refine ⟨P₀, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm hPm
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ _ (H L hL)⟩

namespace X2E

/-! ## The B1.12 gate as a Prop -/

/-- The bound of B1.12 clause (1) without the factor `δ^{2νN}`. -/
noncomputable def x2Bound (P : WTParams) (Pm p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ) {w : ℕ}
    (pat : Fin w → FixPat) (cut1 cut2 : Option ℕ) : ℝ :=
  jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
    P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
    (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
    (cut2.elim 1 fun j₂ => if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)

/-- The body of B1.12 `layergardenFlower` (verbatim). -/
def B112Body (Pm : ℕ) (P : WTParams) : Prop :=
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N))

/-- **The B1.12 gate** (`Flower-Gate.lean`, `layergardenFlower`), as a hypothesis. -/
def LayergardenFlowerGate : Prop := WTPrefixP B112Body

/-! The next four lemmas are copied from wt-cumul's INDUCT `GateConstants.lean`
(`/home/scott/wt-scratch/induct/GateConstants.lean`, sha256 `f60851de90d8cddffe11f6ffca0883623221bd2c584eb378c7c5e3287f7cc6f7`),
renamed to avoid a clash on landing. -/

theorem Rdown_update_x2 (P : WTParams) (C₁ C₂ : ℝ) (n : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).Rdown n = P.Rdown n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [WTParams.Rdown, ih]

theorem R_update_x2 (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).R p = P.R p := by
  unfold WTParams.R
  exact Rdown_update_x2 P C₁ C₂ _

theorem N_update_x2 (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).N p = P.N p := by
  unfold WTParams.N
  rw [R_update_x2]

theorem inputsF_update_x2 (P : WTParams) (C₁ C₂ : ℝ) (R : ℕ → Mom P.d → ℝ) :
    inputsF {P with C₁ := C₁, C₂ := C₂} R = inputsF P R := rfl

/-- B1.12's body does not use the constants `C₁, C₂`. -/
theorem B112Body_update (Pm : ℕ) (P : WTParams) (C₁ C₂ : ℝ) :
    B112Body Pm {P with C₁ := C₁, C₂ := C₂} = B112Body Pm P := by
  simp only [B112Body, RemainderBound, flowerSum, coupleSum, inputsF_update_x2, WTParams.theta,
    WTParams.Lambda, N_update_x2]

theorem B112Body_const (Pm : ℕ) (P : WTParams) (C₁ C₂ : ℝ) (h : B112Body Pm P) :
    B112Body Pm {P with C₁ := C₁, C₂ := C₂} := by
  rw [B112Body_update]
  exact h

/-! ## The obligation O-X2-EXP -/

/-- The random kernel of `flowerest1` built from `a(ω, p)`. -/
noncomputable abbrev randK {Ω : Type*} (P : WTParams) (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (p : ℕ)
    (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)
    (t s : ℝ) (n n' : Fin P.d → ℤ) (ω : Ω) : ℂ :=
  SysAPI.randFlowerKernel P.L P.γ P.δ p (P.N (p + 1)) (a ω p) kind pat dagger cut1 cut2 ζ t s n n'

/-- The body of O-X2-EXP. -/
def OX2ExpBody.{u} (Pm : ℕ) (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
  ∀ (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
    (pat = .plain ∨ pat = .dRoot) →
    (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
    Integrable (fun ω => ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm))
      (μ.restrict (Fev p)) ∧
    ‖(((∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          flowerSum P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c)
            cut1 cut2 ζ t s n n'‖ ≤
      x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) cut1 cut2 *
        Real.exp (-(101 * P.N (p + 1) : ℝ))

/-- **Obligation O-X2-EXP** (T (flowerexp2), L2287–L2290; proof of T Prop `flowerest1`, following T.cmattr).
Let `𝒦` be the random kernel of `flowerest1` built from `a(p)`, of any kind, pattern, `†` and cutoffs. Then:
- `|𝒦|^{2P}` is integrable on `F_p`;
- `𝔼_p|𝒦|^{2P} = ∑_{N ≤ N_{p+1}^4} flowerSum_N + 𝓔` with `|𝓔| ≤ B e^{−101N_{p+1}}`. Here `flowerSum_N` is the
  B1.12 garden sum of width `2P` with the alternating signature, constant pattern, `†` labels and cutoffs, and `B`
  is B1.12's bound without `δ^{2νN}`.

**Proof plan.**
1. Expand `|𝒦|^{2P} = ∏_j 𝒦^{(−1)^j}` over 2P-tuples of flower trees and joint decorations.
2. Use the moment–cumulant formula (`integral_prod_eq_sum_cumulant`, Foundations) on the leaves `a_{k_ℓ}(p)`.
3. Insert `AnsatzAt` (2) and (3) for the cumulant blocks. The pairs give `F_p`, the higher blocks give
   `truncSum` gardens, and the `E_p`, `Ẽ_p` terms give `𝓔`.
4. Identify (top flower trees, blocks, attached layered gardens) with `𝒢 ∈ ℋ^tr_{p+1}`, together with the kernel
   and time-domain factorization. This is the graft bijection of T.cmattr, which INDUCT is building.
5. Bound the error as in T.propansatz: `E_p`, `Ẽ_p ≤ e^{−N_p}` with `N_p = N_{p+1}^{(40d)²}`, and orders
   `> N_{p+1}^4`.

It is **not** assumed anywhere as an axiom. `flowerest1_of_gates` takes it as a hypothesis.

**Patterns.** Only `plain` and `dRoot` are covered: X3 bounds the operator through `sup_t ∫|𝒦(t,s)| ds`, which needs
`∂_t` only. For `dChild i`, B1.12's `PatValid` also allows the `i`-th child of `𝔣^pr` to be the root of an attached
lower-layer garden. The tree kernel's `∂_s` boundary term (T L2331) designates only top branching children, so the
identity would fail for `dChild` (X2-HANDOFF, finding). -/
def OX2Exp.{u} : Prop := WTPrefixP OX2ExpBody.{u}

/-! ## The `𝒴`, `𝒲` kinds have large order -/

theorem sum_topOrder_le_order {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :
    ∑ j, LG.topOrder p j ≤ LG.garden.order := by
  classical
  have h1 : ∀ j, LG.topOrder p j ≤
      (Finset.univ.filter fun b : GBranch LG.garden.tree => b.1.1 = j).card := fun j =>
    Finset.card_le_card fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hb.1
  calc ∑ j, LG.topOrder p j
      ≤ ∑ j, (Finset.univ.filter fun b : GBranch LG.garden.tree => b.1.1 = j).card :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = Fintype.card (GBranch LG.garden.tree) := by
        rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := fun b : GBranch LG.garden.tree => b.1.1)
          (fun _ _ => Finset.mem_univ _)]
    _ = LG.garden.order := by rw [card_gbranch]; rfl

theorem kind_order_lower {w : ℕ} (LG : LayeredGarden w) (p Ntr : ℕ) (kind : FlowerKind)
    (hk : kind ≠ .X) (h : LG.FlowerKindOK p Ntr kind) : w * (Ntr + 1) ≤ LG.garden.order := by
  have hj : ∀ j, Ntr + 1 ≤ LG.topOrder p j := by
    intro j
    cases kind with
    | X => exact absurd rfl hk
    | Y => exact (h j).1
    | W => exact (h j).1
  calc w * (Ntr + 1) = ∑ _j : Fin w, (Ntr + 1) := by simp
    _ ≤ ∑ j, LG.topOrder p j := Finset.sum_le_sum fun j _ => hj j
    _ ≤ LG.garden.order := sum_topOrder_le_order LG p

/-- For the kinds `𝒴`, `𝒲` the flower sum vanishes below order `w (N_{p+1} + 1)`. -/
theorem flowerSum_eq_zero_of_lt (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (hk : kind ≠ .X) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (hN : N < w * (P.N (p + 1) + 1)) :
    flowerSum P F p N kind pat dagger cut1 cut2 ζ t s n n' = 0 := by
  unfold flowerSum
  classical
  refine finsum_eq_zero_of_forall_eq_zero fun LG => ?_
  rw [finsum_eq_dif, dite_eq_right_iff]
  intro h
  have := kind_order_lower LG p (P.N (p + 1)) kind hk h.2.2.2.1
  rw [h.2.2.1] at this
  omega

/-! ## `flowerest1` -/

/-- The gain of the kind: `1` for `𝒳`, `e^{−100N_{p+1}}` for `𝒴`, `𝒲`. -/
noncomputable def kindGain (Ntr : ℕ) : FlowerKind → ℝ
  | .X => 1
  | .Y => Real.exp (-(100 * Ntr : ℝ))
  | .W => Real.exp (-(100 * Ntr : ℝ))

/-- The body of `flowerest1` (T Prop `flowerest1`, (flowerest2) and its variants). -/
def X2Body.{u} (Pm : ℕ) (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
  ∀ (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
    (pat = .plain ∨ pat = .dRoot) →
    (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
    Integrable (fun ω => ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm))
      (μ.restrict (Fev p)) ∧
    ∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ ≤
      3 * x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) cut1 cut2 * kindGain (P.N (p + 1)) kind

theorem x2Bound_nonneg (P : WTParams) (hL : 0 < P.L) (Pm p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ) {w : ℕ}
    (pat : Fin w → FixPat) (cut1 cut2 : Option ℕ) : 0 ≤ x2Bound P Pm p ζ n n' pat cut1 cut2 := by
  unfold x2Bound
  have h2L : ∀ j : ℕ, 0 < (2 : ℝ) ^ j * P.L := fun j => mul_pos (pow_pos two_pos j) hL
  refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    (Real.rpow_nonneg hL.le _)) ?_) ?_
  · cases cut1 with
    | none => exact zero_le_one
    | some j => exact Real.rpow_nonneg (h2L j).le _
  · cases cut2 with
    | none => exact zero_le_one
    | some j =>
      show 0 ≤ (if ∀ j, pat j = .plain then ((2 : ℝ) ^ j * P.L) ^ (-(Pm / 9 : ℝ)) else 1)
      split_ifs
      · exact Real.rpow_nonneg (h2L j).le _
      · exact zero_le_one

/-- The geometric sum `∑_{N ∈ s} q^N ≤ 2 q^A` for `0 ≤ q ≤ 1/2` and `N ≥ A` on `s`. -/
theorem sum_pow_le_two_mul {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (s : Finset ℕ) (A : ℕ) (hs : ∀ N ∈ s, A ≤ N) :
    ∑ N ∈ s, q ^ N ≤ 2 * q ^ A := by
  have hq1 : q < 1 := by linarith
  calc ∑ N ∈ s, q ^ N ≤ ∑ N ∈ s.image (· - A), q ^ A * q ^ N := by
        rw [Finset.sum_image (fun x hx y hy h => by
          have := hs x hx; have := hs y hy; omega)]
        refine Finset.sum_le_sum fun N hN => ?_
        rw [← pow_add, Nat.add_sub_cancel' (hs N hN)]
    _ = q ^ A * ∑ N ∈ s.image (· - A), q ^ N := by rw [Finset.mul_sum]
    _ ≤ q ^ A * ∑' N, q ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 _)
        exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ fun i _ => pow_nonneg hq0 _
    _ = q ^ A * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ q ^ A * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 _)
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
    _ = 2 * q ^ A := mul_comm _ _

/-- **`flowerest1` from the B1.12 gate and O-X2-EXP.** -/
theorem flowerest1_of_gates.{u} (hG : LayergardenFlowerGate) (hE : OX2Exp.{u}) : WTPrefixP X2Body.{u} := by
  refine ((WTPrefixP.and B112Body_const hG hE).small (fun ν => Real.exp (-(25 / ν))) fun ν _ =>
    Real.exp_pos _).mono ?_
  rintro Pm P ⟨⟨hB, hX⟩, hPm, hν, hδ, hδν, hL⟩
  classical
  intro Ω _ μ _ g hg p hp a Fev R E Et hA t ht s hs n n' ζ kind pat dagger cut1 cut2 hpat hcut
  obtain ⟨hint, hexp⟩ := hX Ω μ g hg p hp a Fev R E Et hA t ht s hs n n' ζ kind pat dagger cut1 cut2 hpat hcut
  refine ⟨hint, ?_⟩
  have hRB : RemainderBound P R p := fun q hq => (hA q hq).2.1.1
  set Ntr := P.N (p + 1)
  set B := x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) cut1 cut2
  set I := ∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ
  set fS : ℕ → ℂ := fun N => flowerSum P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat)
    (dagger.map fun c _ => c) cut1 cut2 ζ t s n n'
  have hB0 : 0 ≤ B := x2Bound_nonneg P (by linarith) Pm p ζ n n' _ cut1 cut2
  set q := P.δ ^ (2 * P.ν)
  have hq0 : 0 ≤ q := Real.rpow_nonneg hδ.le _
  have hq50 : q ≤ Real.exp (-50) := by
    calc q ≤ Real.exp (-(25 / P.ν)) ^ (2 * P.ν) := Real.rpow_le_rpow hδ.le hδν (by positivity)
      _ = Real.exp (-50) := by
          rw [← Real.exp_mul]
          congr 1
          field_simp
          ring
  have hq : q ≤ 1 / 2 := hq50.trans (by
    have := Real.add_one_le_exp (-50 : ℝ)
    have h2 : Real.exp (-50) * Real.exp 50 = 1 := by rw [← Real.exp_add]; simp
    have h3 : (51 : ℝ) ≤ Real.exp 50 := by linarith [Real.add_one_le_exp (50 : ℝ)]
    nlinarith [Real.exp_pos (-50 : ℝ)])
  -- the per-order bound
  have hord : ∀ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖ ≤ B * q ^ N := by
    intro N hN
    have hN' : N ≤ Ntr ^ 4 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)
    have h := (hB p hp R hRB).1 t ht s hs n n' ζ N hN' kind (fun _ => pat) (dagger.map fun c _ => c)
      cut1 cut2 hcut
    have hq' : P.δ ^ (2 * P.ν * N) = q ^ N := by
      rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
    refine h.trans (le_of_eq ?_)
    rw [hq']
    simp only [B, x2Bound]
    ring
  -- the low orders vanish for `𝒴`, `𝒲`
  set A : ℕ := if kind = .X then 0 else 2 * Pm * (Ntr + 1)
  have hlow : ∀ N, N < A → fS N = 0 := by
    intro N hN
    by_cases hk : kind = .X
    · simp [A, hk] at hN
    · simp only [A, hk, ite_false] at hN
      exact flowerSum_eq_zero_of_lt P _ p N kind hk _ _ cut1 cut2 ζ t s n n' hN
  have hsum : ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖ ≤ 2 * B * q ^ A := by
    calc ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖
        ≤ ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (A ≤ ·), B * q ^ N := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun N hN => ?_
          split_ifs with h
          · exact hord N hN
          · rw [hlow N (not_le.1 h), norm_zero]
      _ = B * ∑ N ∈ (Finset.range (Ntr ^ 4 + 1)).filter (A ≤ ·), q ^ N := by rw [Finset.mul_sum]
      _ ≤ B * (2 * q ^ A) := mul_le_mul_of_nonneg_left
          (sum_pow_le_two_mul hq0 hq _ A fun N hN => (Finset.mem_filter.1 hN).2) hB0
      _ = 2 * B * q ^ A := by ring
  have hI0 : 0 ≤ I := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => by positivity)
  have hIle : I ≤ 2 * B * q ^ A + B * Real.exp (-(101 * Ntr : ℝ)) := by
    have h1 : I = ‖((I : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hI0]
    rw [h1]
    calc ‖((I : ℝ) : ℂ)‖ ≤ ‖∑ N ∈ Finset.range (Ntr ^ 4 + 1), fS N‖ +
          ‖((I : ℝ) : ℂ) - ∑ N ∈ Finset.range (Ntr ^ 4 + 1), fS N‖ := norm_le_insert' _ _
      _ ≤ ∑ N ∈ Finset.range (Ntr ^ 4 + 1), ‖fS N‖ + B * Real.exp (-(101 * Ntr : ℝ)) :=
          add_le_add (norm_sum_le _ _) hexp
      _ ≤ _ := add_le_add hsum le_rfl
  have he101 : Real.exp (-(101 * Ntr : ℝ)) ≤ Real.exp (-(100 * Ntr : ℝ)) :=
    Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _; linarith)
  have he100 : Real.exp (-(100 * Ntr : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _; linarith)
  cases kind with
  | X =>
    have hA0 : A = 0 := by simp [A]
    rw [hA0, pow_zero] at hIle
    show I ≤ 3 * B * 1
    nlinarith
  | Y | W =>
    have hAq : q ^ A ≤ Real.exp (-(100 * Ntr : ℝ)) := by
      have hA' : 2 * (Ntr + 1) ≤ A := by
        simp only [A, reduceCtorEq, ite_false]
        nlinarith
      calc q ^ A ≤ q ^ (2 * (Ntr + 1)) := pow_le_pow_of_le_one hq0 (hq.trans (by norm_num)) hA'
        _ ≤ Real.exp (-50) ^ (2 * (Ntr + 1)) := pow_le_pow_left₀ hq0 hq50 _
        _ = Real.exp (-(100 * (Ntr + 1) : ℝ)) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ Real.exp (-(100 * Ntr : ℝ)) := Real.exp_le_exp.2 (by linarith)
    show I ≤ 3 * B * Real.exp (-(100 * Ntr : ℝ))
    nlinarith

end X2E

end WaveTurbulence

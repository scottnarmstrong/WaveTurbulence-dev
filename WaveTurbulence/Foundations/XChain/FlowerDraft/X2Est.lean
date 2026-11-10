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
        ‖flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
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
  simp only [B112Body, RemainderBound, flowerSumP, coupleSum, inputsF_update_x2, WTParams.theta,
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
          flowerSumP P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c)
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
    flowerSumP P F p N kind pat dagger cut1 cut2 ζ t s n n' = 0 := by
  unfold flowerSumP
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

end X2E

end WaveTurbulence

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.MkMarkX.Defs

/-! # B4 STAGE1MK-GATE: the gate at fixed parameters

* `fineMk`: the fine′ marking of Stage 1′ (ruling R177, F-B4-4 (b)): B2e's `markIX = markI ∪ X` for a stem-dependent
  weight, `markI` for a stem-free one. It is a `FineMarking` (`fineMarking_fineMk`), given B2e's fine transport of
  `markIX` (`B2eIX`).
* `ZeroVanish P`: the class value of every stem-unclean fine′ class vanishes (FL-SEP; discharged in `Zero2` from B2e's
  `markX` transport and per-tree FL-SEP).
* `fullAt`: `Stage1ReductionAtMKFull C₀ cP cθ P` from the B3+B3s hypothesis, `B2eIX` and `ZeroVanish P`, at
  parameters with `K^(D+1) ≤ C₂`, `0 ≤ C₁`, `0 < L`; `frozenAt`: the frozen `Stage1ReductionAtMK C₀ (cP + 343) P` from
  the same inputs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

variable {w : ℕ}

/-- **B2e's fine transport of `markIX`** (B2e export `fineTransportedAt_markIX`, statement verbatim). -/
def B2eIX : Prop :=
  ∀ {w : ℕ} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (a : VineA.PrescribedPrimeGarden w), a.FineTransportedAt (MkMarkX.markIX J pat t s kSel)

/-- **The fine′ marking of Stage 1′.** -/
def fineMk (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σ : Fin w → Option ℕ) :
    Stage1Mk.MarkFn w :=
  fun {_} B => if StemDep σ kSel then MkMarkX.markIX J pat t s kSel B else markI J pat t s kSel B

theorem fineMk_stem (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (h : StemDep σ kSel) : @fineMk w J pat t s kSel σ = @MkMarkX.markIX w J pat t s kSel := by
  funext LG B
  simp only [fineMk, if_pos h]

theorem fineMk_free (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (h : ¬ StemDep σ kSel) : @fineMk w J pat t s kSel σ = @markI w J pat t s kSel := by
  funext LG B
  simp only [fineMk, if_neg h]

/-- In the stem-dependent case B2e's `markIX` is a fine marking (B2e handoff, field for field). -/
theorem fineMarking_markIX (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (hS : StemDep σ kSel) (hfine : ∀ a : PrescribedPrimeGarden w, a.FineTransportedAt (MkMarkX.markIX J pat t s kSel)) :
    FineMarking J pat t s kSel σ (MkMarkX.markIX J pat t s kSel) :=
  ⟨fun _ => Set.subset_union_left, fun _ _ _ c hc hun => Or.inr ⟨hc, hun⟩,
    fun _ _ hc => hc.imp id fun h => ⟨hS, h⟩, hfine⟩

/-- **`fineMk` is a fine marking.** -/
theorem fineMarking_fineMk (hIX : B2eIX) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (kSel σ : Fin w → Option ℕ) : FineMarking J pat t s kSel σ (fineMk J pat t s kSel σ) := by
  by_cases hS : StemDep σ kSel
  · rw [fineMk_stem J pat t s hS]
    exact fineMarking_markIX J pat t s hS (hIX J pat t s kSel)
  · rw [fineMk_free J pat t s hS]
    exact fineMarking_stemFree J pat t s hS

/-- **Zero classes vanish**: under the gate's hypotheses, the class value of a fine′ class (at `fineMk`) of a
stem-dependent weight that contains a stem-unclean point is `0` (FL-SEP). -/
def ZeroVanish (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ π : PcA R p (objKind (2 * R)) A (fineMk J pat t s kSel σ), StemDep σ kSel →
    (∃ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a (fineMk J pat t s kSel σ) ∧ ¬ CleanPt J a) →
    classValue P p J pat kSel t s A roots h Rf σ Rs dag (fineMk J pat t s kSel σ) π = 0

section Gate
variable {C₀ K : ℕ} {cP cθ : ℝ} {P : WTParams}

/-- The good pieces of the gate data (non-zero classes from B3s, zero classes vanish). -/
theorem gate_good (hB : MarkedClassRepresentsMK cP cθ P) (hIX : B2eIX) (hZ : ZeroVanish P)
    (hC : 0 ≤ P.C₁) (hL : 0 < P.L) {p : ℕ} (hp : p < P.D) {R : ℕ} (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    {N : ℕ} (hN1 : 1 ≤ N) (hNb : N ≤ P.N (p + 1) ^ 4)
    (J : Finset (Fin (2 * R))) (hJ : J.card = R) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ)
    {t : ℝ} (ht : t ∈ Ioo (p : ℝ) (p + 1)) {s : ℝ} (hs : s ∈ Ioo (p : ℝ) t) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p)
    (hpl : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (hTC : MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)))
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hb : 1 ≤ b) (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r) (hRs : ∀ j, P.L ≤ Rs j)
    (hhigh : ((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖)
    (π : PcA R p (objKind (2 * R)) A (fineMk J pat t s kSel σ)) :
    Nonempty (GoodPiece P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ (fineMk J pat t s kSel σ) π) := by
  have hF := fineMarking_fineMk hIX J pat t s kSel σ
  by_cases hnz : ¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a (fineMk J pat t s kSel σ) → CleanPt J a
  · exact good_of_nonzero P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ _ hB hp hR hRmax hN1 hNb hJ ht hs hA
      hpl hTC hb hh hRf hRs hhigh hF hL.ne' π hnz
  · push_neg at hnz
    exact good_of_zero P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ _ hR hNb hA hb hRs hC hL π
      (hZ p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A hA roots h b Rf σ Rs dag hRf hhigh π hnz.1 hnz.2)

/-- **The marked Stage-1′ gate, Full form, at fixed parameters.** -/
theorem fullAt (hcnt : PieceCountAt C₀ K) (hK : (K : ℝ) ^ (P.D + 1) ≤ P.C₂) (hC : 0 ≤ P.C₁) (hL : 0 < P.L)
    (hB : MarkedClassRepresentsMK cP cθ P) (hIX : B2eIX) (hZ : ZeroVanish P) :
    Stage1ReductionAtMKFull C₀ cP cθ P := by
  intro p hp R hR hRmax N hN1 hNb J hJ pat kSel t ht s hs A hA hpl hTC roots h b Rf σ Rs dag hb hh hRf hRs hhigh
  have hF := fineMarking_fineMk hIX J pat t s kSel σ
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, h1, h2, h3, h4, h5, -⟩ :=
    gate_of_good P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ (fineMk J pat t s kSel σ) C₀ K hcnt hK hp hR hN1
      hA (fun B => (markI0_sub_markI J pat t s kSel B).trans (hF.sub B))
      (gate_good hB hIX hZ hC hL hp hR hRmax hN1 hNb J hJ pat kSel ht hs A hA hpl hTC roots h b Rf σ Rs dag hb hh
        hRf hRs hhigh)
  exact ⟨S, Cl, hCl, cls, members, sel, selR, h1, h2, h3, h4, h5⟩

end Gate

end WaveTurbulence.Flower.Stage1MKGate

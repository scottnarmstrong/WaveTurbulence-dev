/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Rest
public import WaveTurbulence.Foundations.Flower.MkSlots.Statement

/-! # B3s MK-SLOTS: milestone α from the class representation

`pieceα` is the α class piece (protected atoms `protOf`, pins `fixOf` at capped flower parents, no filters, the
dagger sibling indicator `sibIndOf` at `G_sb` flower parents with flower children `flwOf`). `ClassRepAlpha cP P` has
the binders of `MarkedClassRepresentsMKα` and concludes only `RepresentsIntMK` of the class value for `pieceα`.
**`markedClassRepresentsMKα_of_rep`**: `1 ≤ P.L → ClassRepAlpha cP P → MarkedClassRepresentsMKα cP cθ P` (with no
selection, `selR = ∅`: `RepresentsIntMKSel … ∅` is `RepresentsIntMK`, `selMassMK = b^N`; `repMK` by monotonicity in
`cP`; `PieceRestB3s` by `pieceRest_alpha`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots

/-- The flower children of a `G_sb` branch: leaves paired with a cap root. -/
def flwOf {w : ℕ} (J : Finset (Fin w)) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    GBranch (stA mkF a).G.tree → Fin 3 → Prop :=
  fun c i => ∃ ℓ : GLeaf (stA mkF a).G.tree, ℓ.toNode = c.child i ∧ ((stA mkF a).G.pair ℓ).1.1 ∈ J

/-- **The α class piece.** -/
def pieceα (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) : Stage1PieceMK P.d R :=
  classPiece P mkF a (protOf J (fun _ => FixPat.plain) t s kSel mkF a)
    (protI a.layered J (fun _ => FixPat.plain) t s kSel).card (fixOf J (fun _ => FixPat.plain) t s mkF a)
    (fun _ => none) (sibIndOf J mkF a dag (flwOf J mkF a))

/-- **The α analytic core**: the class value is represented by the α piece. -/
def ClassRepAlpha (cP : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  (∀ j, pat j = FixPat.plain) → (∀ j, kSel j = none) →
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j, σ j = none) →
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  (pieceα P J t s kSel mkF (repPt π) dag).RepresentsIntMK N cP (fun _ => t) 0 roots (b ^ N)
    (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

/-- `RepresentsIntMK` is monotone in the protected loss exponent (for `L ≥ 1`). -/
theorem representsIntMK_mono_cP {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) {n : ℕ} {cP cP' : ℝ}
    (hc : cP ≤ cP') (hL : 1 ≤ P.L) {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    {s : ℝ} {val : ℂ} (h : π.RepresentsIntMK n cP tt base roots s val) :
    π.RepresentsIntMK n cP' tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  have hexp : P.L ^ (cP * P.d * (π.nProt : ℝ)) ≤ P.L ^ (cP' * P.d * (π.nProt : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by
      have : (0 : ℝ) ≤ P.d * (π.nProt : ℝ) := by positivity
      nlinarith)
  have hpos : 0 < P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push_neg at hneg
    have : K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s < 0 := by
      have := mul_neg_of_neg_of_pos hneg hpos
      linarith [this, show K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s = K * s * P.L ^ (cP * P.d * (π.nProt : ℝ))
        from by ring]
    linarith
  calc ∫ ξ, ‖w ξ‖ ∂μ ≤ K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s := h4
    _ = K * s * P.L ^ (cP * P.d * (π.nProt : ℝ)) := by ring
    _ ≤ K * s * P.L ^ (cP' * P.d * (π.nProt : ℝ)) := mul_le_mul_of_nonneg_left hexp hKs
    _ = K * P.L ^ (cP' * P.d * (π.nProt : ℝ)) * s := by ring

/-- With no depth selection, the selected mass is `b^N`. -/
theorem selMassMK_none {R N : ℕ} (b : ℝ) (Rs : Fin (2 * R) → ℝ) (U : Finset (Fin (2 * R))) :
    selMassMK N b Rs (fun _ => none) U = b ^ N := by
  simp [selMassMK]

/-- **Milestone α from the analytic core.** -/
theorem markedClassRepresentsMKα_of_rep {cP cθ : ℝ} {P : WTParams} (hL : 1 ≤ P.L) (hrep : ClassRepAlpha cP P) :
    MarkedClassRepresentsMKα cP cθ P := by
  intro p hp R h1 h2 N hN1 hN2 J pat kSel t ht s hs hpat hk A hA hpl hTC roots hh b Rf σ Rs dag hσ hb hsn hRf hRs
    hhigh mkF hmk π hπ
  have hrep' := hrep p hp R h1 h2 N hN1 hN2 J pat kSel t ht s hs hpat hk A hA hpl hTC roots hh b Rf σ Rs dag hσ hb
    hsn hRf hRs hhigh mkF hmk π hπ
  have hpat' : pat = fun _ => FixPat.plain := funext hpat
  have hk' : kSel = fun _ => none := funext hk
  subst hpat' hk'
  have hG : CapGeo (repPt π).layered J p := (hA _ (repPt_layered_memMk π)).2.2.2.2.1
  refine ⟨protOf J (fun _ => FixPat.plain) t s (fun _ => none) mkF (repPt π),
    fixOf J (fun _ => FixPat.plain) t s mkF (repPt π), fun _ => none,
    sibIndOf J mkF (repPt π) dag (flwOf J mkF (repPt π)), ∅, ?_⟩
  refine ⟨?_, pieceRest_alpha P J p mkF (repPt π) hG t s hs ht.2 _ dag (flwOf J mkF (repPt π)) cθ,
    fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
    Nat.zero_le _, representsIntMK_mono_cP _ (by linarith) hL hrep',
    fun v hv => absurd hv (Finset.notMem_empty v)⟩
  rw [selMassMK_none]
  exact (representsIntMKSel_empty (pieceα P J t s (fun _ => none) mkF (repPt π) dag) N cP (fun _ => t) 0 roots
    (b ^ N) _).2 hrep'

/-- A loss `L^ℓ` carried by the mass parameter moves into the protected factor when `ℓ ≤ cP·d·nProt`. -/
theorem representsIntMK_absorb {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) {n : ℕ} {cP ℓ : ℝ}
    (hL : 1 ≤ P.L) (hℓ : ℓ ≤ cP * P.d * (π.nProt : ℝ)) {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (h : π.RepresentsIntMK n 0 tt base roots (P.L ^ ℓ * s) val) :
    π.RepresentsIntMK n cP tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  have hexp : P.L ^ ℓ ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL hℓ
  have hpos : 0 < P.L ^ ℓ := Real.rpow_pos_of_pos hL0 _
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have h4' : ∫ ξ, ‖w ξ‖ ∂μ ≤ K * s * P.L ^ ℓ := by
    have : K * P.L ^ ((0 : ℝ) * P.d * (π.nProt : ℝ)) * (P.L ^ ℓ * s) = K * s * P.L ^ ℓ := by
      rw [zero_mul, zero_mul, Real.rpow_zero]; ring
    rw [← this]; exact h4
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith
  calc ∫ ξ, ‖w ξ‖ ∂μ ≤ K * s * P.L ^ ℓ := h4'
    _ ≤ K * s * P.L ^ (cP * P.d * (π.nProt : ℝ)) := mul_le_mul_of_nonneg_left hexp hKs
    _ = K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s := by ring

end WaveTurbulence.Flower.MkSlots

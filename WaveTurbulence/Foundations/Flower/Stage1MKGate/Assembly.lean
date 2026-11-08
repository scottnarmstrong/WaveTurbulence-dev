/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Zero
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Marking
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr3
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10b
public import WaveTurbulence.Foundations.Stage1.ClassCount.Final

/-! # B4 STAGE1MK-GATE: assembly of the gate from good class pieces (design steps 2–6)

For fixed gate data and a fine marking `mkF ⊇ markI0`, a **good piece** of a fine′ class `π` is a world Stage-1′ piece
whose Stage-1 part is main's `stage1PieceOf` at the representative with some marked set `Mk`, together with residual
selected vertices, such that `ClassPieceOK` holds for the class value, `nProt ≤ |Π(rep)|`, and `SoundMKFull`.
`gate_of_good` assembles every clause of `Stage1ReductionAtMKFull`'s conclusion from one good piece per class:
* classes: main's fine′ classes `PcA … mkF`, coarse′ classes `ClA … markI0`, selections `selPMk … mkF`;
* `Stage1Partition`: main's `stage1Partition_prodMk` (B2b's `markInvariantBatchV_markI0`, `markI0 ⊆ mkF`);
* values: the class value `classValue` (definitional);
* the protected count at the representative (a member of its coarse′ class);
* orders: `order_add_hinges_leMk` and the representative's skeleton order;
* `Stage1Counts`: main's `pieceCount_of_repMk` with `classCountMk` (any marking), fibres `≤ 3^N` (`fibre_card_leMk`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.ClassCount
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

/-- The piece count of main's `pieceCount_of_repMk` at the admissibility `True` (constants `C₀`, `K`). -/
def PieceCountAt (C₀ K : ℕ) : Prop :=
  ∀ (P : WTParams), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R → ∀ N, 1 ≤ N →
    ∀ (S : Stage1Data P R) (rep : S.Pc → LayeredGarden (2 * R)) (M : ℕ),
      (∀ π, Stage1Mk.Stage1CarriesW P p N (rep π) ∧
        HasPieceDataMk (fun _ _ _ => True) P.d (rep π) (S.piece π).gbar (S.piece π).rbar) →
      (∀ LG, ((@univ S.Pc S.fin).filter fun π => rep π = LG).card ≤ M) →
      ∀ g r : ℕ,
        ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
          (M : ℝ) * ((C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
            P.C₂ ^ (g + r))

theorem exists_pieceCountAt : ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ PieceCountAt C₀ K :=
  pieceCount_of_repMk (fun _ _ _ => True) classCountMk

section Good
variable (P : WTParams) {R : ℕ} (p N : ℕ) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ)
  (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (cP cθ : ℝ) (mkF : Stage1Mk.MarkFn (2 * R))

/-- **A good piece of a fine′ class.** -/
structure GoodPiece (π : PcA R p (objKind (2 * R)) A mkF) where
  piece : Stage1PieceMK P.d R
  selR : Finset (GBranch piece.Gsb.tree)
  Mk : Set (Stage1.CLVine (repPt π).prime.skeleton)
  hpiece : piece.toStage1PieceD = VineA.NormalizedSplice.stage1PieceOf P.d (repPt π).prime.prime.1
    (repPt π).layered (repPt π).prime.decodes (repPt π).totalSigma Mk
  ok : ClassPieceOK piece selR N cP cθ t b roots kSel Rs (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)
  nprot : piece.nProt ≤ (protI (repPt π).layered J pat t s kSel).card
  sound : SoundMKFull piece p 0 roots cθ

/-- The carrier of the gate gives main's truncation-free carrier (ruling R156). -/
theorem carriersW_of {p N : ℕ} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {LG : LayeredGarden (2 * R)}
    (hA : MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) :
    Stage1Mk.Stage1CarriesW P p N LG :=
  ⟨hA.1.1, hA.1.2.2.1, hA.1.2.2.2, hA.2.1⟩

/-- **Assembly of the gate's conclusion from one good piece per fine′ class.** -/
theorem gate_of_good (C₀ K : ℕ) (hcnt : PieceCountAt C₀ K) (hK : (K : ℝ) ^ (P.D + 1) ≤ P.C₂) (hp : p < P.D)
    (hR : 1 ≤ R) (hN1 : 1 ≤ N)
    (hA : ∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI0 J pat t s B ⊆ mkF B)
    (hG : ∀ π : PcA R p (objKind (2 * R)) A mkF,
      Nonempty (GoodPiece P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ mkF π)) :
    ∃ (S : Stage1DataMK P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
      (members : Cl → Finset (LayeredGarden (2 * R)))
      (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
      (selR : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)),
      Stage1Partition roots A members cls sel ∧
      (∀ π, S.val π = ∑ LG ∈ members (cls π),
          kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
            (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k)
            (fun _ => t) 0 roots (sel π LG) ∧
        RepresentsIntMKSel (S.piece π) (selR π) N cP (fun _ => t) 0 roots
          (selMassMK N b Rs kSel ((selR π).image fun v => v.1.1)) (S.val π) ∧
        (∃ LG ∈ members (cls π), (S.piece π).nProt ≤ (protI LG J pat t s kSel).card) ∧
        (∀ v ∈ selR π, (kSel v.1.1).isSome ∧ (S.piece π).fix v = none ∧
          ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) ∧
        (∀ v ∈ selR π, ∀ v' ∈ selR π, v.1.1 = v'.1.1 → v = v') ∧
        (selR π).card ≤ (S.piece π).nProt) ∧
      (∀ π, SoundMKFull (S.piece π) p 0 roots cθ) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
      Stage1Counts C₀ P R N S.toData Cl hCl cls ∧
      (∀ π, (S.piece π).RepresentsIntMK N (cP + 343) (fun _ => t) 0 roots (b ^ N) (S.val π)) := by
  set kind := objKind (2 * R) with hkind
  let G : ∀ π : PcA R p kind A mkF, GoodPiece P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ mkF π :=
    fun π => Classical.choice (hG π)
  let S : Stage1DataMK P R :=
    ⟨PcA R p kind A mkF, inferInstance, fun π => (G π).piece,
      fun π => classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π⟩
  have hplain : ∀ LG ∈ A, LG.garden.IsPlain := fun LG hLG => (hA LG hLG).1.1.1
  have hW : ∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG := fun LG hLG => carriersW_of P (hA LG hLG)
  have hV : Stage1Mk.MarkInvariantBatchV (@markI0 (2 * R) J pat t s) (fun _ => True) :=
    fun hb hA' hm hc => MkMark.markInvariantBatchV_markI0 J pat t s hb hA' hm hc
  have hrepW : ∀ π : PcA R p kind A mkF, Stage1Mk.Stage1CarriesW P p N (repPt π).layered :=
    fun π => hW _ (repPt_layered_memMk π)
  -- the Stage-1 part of each piece
  have hD : ∀ π : PcA R p kind A mkF, (S.piece π).toStage1PieceD =
      VineA.NormalizedSplice.stage1PieceOf P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
        (repPt π).totalSigma (G π).Mk := fun π => (G π).hpiece
  refine ⟨S, ClA R p kind A (markI0 J pat t s), inferInstance, clsPMk (markI0 J pat t s), membersP,
    selPMk p kind A P 0 roots mkF, fun π => (G π).selR,
    stage1Partition_prodMk p kind A hplain P 0 roots hV hsub, fun π => ?_, fun π => (G π).sound, fun π => ?_, ?_,
    fun π => (G π).ok.repMK⟩
  · -- values, representation, protected count, residual selections
    refine ⟨rfl, (G π).ok.rep, ⟨(repPt π).layered, Finset.mem_filter.2 ⟨repPt_layered_memMk π,
      (repPt π).prime.mem_coarse_outputs_selfMk (markI0 J pat t s (repPt π).prime)⟩, (G π).nprot⟩,
      (G π).ok.sel_spec, (G π).ok.sel_inj, (G π).ok.sel_card⟩
  · -- orders
    have h1 := prod_piece_gsb_orderMk (mk := mkF) P p N kind A hW π
    have h2 := order_add_hinges_leMk (Mk := (G π).Mk) (Mole.garden_isMolecule (repPt π).prime.skeleton)
      (repPt π).totalSigma
    have e : (S.piece π).Gsb = (stSt (repPt π).prime.skeleton (repPt π).totalSigma (G π).Mk).G := by
      have := congrArg Stage1PieceD.Gsb (hD π)
      exact this
    show (S.piece π).Gsb.order ≤ N
    rw [e]
    omega
  · -- counts
    refine ⟨fun π => ?_, fun π => ?_, ?_⟩
    · have hc := hrepW π
      have hn1 : 1 ≤ (repPt π).prime.skeleton.order := (skelFacts_of_carriesW P p N hR hc (repPt π).prime).2.2
      show 1 ≤ (S.piece π).toStage1PieceD.rbar ∧ (S.piece π).toStage1PieceD.rbar ≤ N
      rw [hD π]
      exact stage1Piece_rbar_boundsMk P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
        (repPt π).totalSigma hn1 (prod_piece_gsb_orderMk (mk := mkF) P p N kind A hW π)
    · have hsz := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
      have hord : (repPt π).layered.garden.order = N := (hrepW π).2.1
      show (S.piece π).toStage1PieceD.gbar ≤ N
      rw [hD π]
      exact stage1Piece_gbar_leMk P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
        (repPt π).totalSigma (by omega)
    · intro g r
      have hK' : K ^ (P.D + 1) ≤ P.C₂ := by exact_mod_cast hK
      have := hcnt P hK' p hp R hR N hN1 S.toData (fun π => (repPt π).layered) (3 ^ N)
        (fun π => ⟨hrepW π, ?_⟩) (fun LG => ?_) g r
      · have h2 := this
        push_cast at h2
        calc _ ≤ _ := h2
          _ = _ := by ring
      · show HasPieceDataMk (fun _ _ _ => True) P.d (repPt π).layered (S.piece π).toStage1PieceD.gbar
          (S.piece π).toStage1PieceD.rbar
        rw [hD π]
        exact ⟨_, (repPt π).prime.data, (repPt π).prime.prime.1, (repPt π).prime.decodes, (repPt π).totalSigma,
          (G π).Mk, trivial, rfl, rfl⟩
      · by_cases hex : ∃ π : PcA R p kind A mkF, (repPt π).layered = LG
        · obtain ⟨π, hπ⟩ := hex
          have hpl : LG.garden.IsPlain := hπ ▸ (repPt π).prime.decodes.1
          exact fibre_card_leMk (mk := mkF) p kind A LG hpl (by rw [← hπ]; exact (hrepW π).2.1)
        · refine le_trans (le_of_eq (Finset.card_eq_zero.2 ?_)) (Nat.zero_le _)
          rw [Finset.filter_eq_empty_iff]
          intro π _ hπ
          exact hex ⟨π, hπ⟩

end Good

end WaveTurbulence.Flower.Stage1MKGate

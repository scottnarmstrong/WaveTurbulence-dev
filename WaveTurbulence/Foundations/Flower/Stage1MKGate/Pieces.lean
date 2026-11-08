/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.MkMark.CountBound

/-! # B4 STAGE1MK-GATE: the good piece of each fine′ class

* **Non-zero classes** (`good_of_nonzero`): B3s's data from the hypothesis `MarkedClassRepresentsMK`, on B2c's piece
  at the representative with marked set `classMk mkF (repPt π)` (R173) and `nProt = |Π(rep)|`. The survivor count
  `m ≤ 6·nProt` is B4's: the marked set lies in `markI(rep)` (a stem-unclean marked vine of `𝒱₀(σ)` would contradict
  cleanness), `m ≤ 2·#Mk` (`survivorsMk_length_le`, F-B4-6) and `#markI ≤ 3|Π|` (B2b's `markCountBound`, Lemma 1⁺).
* **Zero classes** (`good_of_zero`): the zero piece, when the class value vanishes. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

/-- The marked set of a non-zero class piece lies in `markI` of the representative. -/
theorem classMk_sub_markI {R : ℕ} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {t s : ℝ}
    {kSel σ : Fin (2 * R) → Option ℕ} {mkF : Stage1Mk.MarkFn (2 * R)} (hF : FineMarking J pat t s kSel σ mkF)
    (a : PrescribedPrimeGarden (2 * R)) (hnz : ¬ StemDep σ kSel ∨ CleanPt J a) :
    classMk mkF a ⊆ markI J pat t s kSel a.prime := by
  rintro c ⟨hcF, hcV⟩
  rcases hF.le a.prime c hcF with h | ⟨hsd, -, hun⟩
  · exact h
  · rcases hnz with h | h
    · exact (h hsd).elim
    · exact (hun (h c hcV)).elim

/-- **The survivor count of a non-zero class piece**: `m ≤ 6·|Π(rep)|`. -/
theorem classPiece_surv_le (P : WTParams) {R : ℕ} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat}
    {t s : ℝ} {kSel σ : Fin (2 * R) → Option ℕ} {mkF : Stage1Mk.MarkFn (2 * R)}
    (hF : FineMarking J pat t s kSel σ mkF) (a : PrescribedPrimeGarden (2 * R)) (hnz : ¬ StemDep σ kSel ∨ CleanPt J a)
    (prot : Finset (GBranch (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree))
    (fix : GBranch (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree → Option ℝ)
    (filt : GBranch (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree → Mom P.d) → ℝ) :
    (classPiece P mkF a prot (protI a.layered J pat t s kSel).card fix filt ind).surv.m ≤
      6 * (protI a.layered J pat t s kSel).card := by
  show (VineA.NormalizedSplice.survObjs a.prime.skeleton a.totalSigma (classMk mkF a)).length ≤ _
  rw [VineA.NormalizedSplice.survObjs_length]
  have h1 := survivorsMk_length_le a.prime.skeleton a.totalSigma (classMk mkF a)
  have h2 : (classMk mkF a).ncard ≤ (markI J pat t s kSel a.prime).ncard :=
    Set.ncard_le_ncard (classMk_sub_markI hF a hnz) (Set.toFinite _)
  have h3 : (markI J pat t s kSel a.prime).ncard ≤ 3 * (protI a.layered J pat t s kSel).card :=
    MkMark.markCountBound a.prime (protI a.layered J pat t s kSel)
  omega

section Good
variable (P : WTParams) {R : ℕ} (p N : ℕ) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ)
  (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (cP cθ : ℝ) (mkF : Stage1Mk.MarkFn (2 * R))

/-- **The good piece of a non-zero class** (from B3s's hypothesis). -/
theorem good_of_nonzero (hB : MarkedClassRepresentsMK cP cθ P) (hp : p < P.D) (hR : 1 ≤ R)
    (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N) (hNb : N ≤ P.N (p + 1) ^ 4)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t)
    (hA : ∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p)
    (hpl : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (hTC : MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)))
    (hb : 1 ≤ b) (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r) (hRs : ∀ j, P.L ≤ Rs j)
    (hhigh : ((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖)
    (hF : FineMarking J pat t s kSel σ mkF) (hL : P.L ≠ 0) (π : PcA R p (objKind (2 * R)) A mkF)
    (hnz : ¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) :
    Nonempty (GoodPiece P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ mkF π) := by
  obtain ⟨prot, fix, filt, ind, selR, hok⟩ := hB p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A hA hpl hTC roots
    h b Rf σ Rs dag hb hh hRf hRs hhigh mkF hF π hnz
  have hnz' : ¬ StemDep σ kSel ∨ CleanPt J (repPt π) :=
    hnz.imp id fun h => h (repPt π) (Relation.EqvGen.refl _)
  have hcW := carriersW_of P (hA _ (repPt_layered_memMk π))
  refine ⟨⟨classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind,
    selR, classMk mkF (repPt π), rfl, hok, le_rfl, ?_⟩⟩
  exact pointPiece_soundFull P hR (repPt π) hcW hNb hL roots cθ (classMk_sub_vinesV0 mkF _) prot _ fix filt ind
    ⟨classPiece_surv_le P hF (repPt π) hnz' prot fix filt ind, hok.rest.prot_card, hok.rest.fix_prot,
      hok.rest.fix_layer, hok.rest.filt_ok, hok.rest.ind_ok, hok.rest.ind_local⟩

/-- **The good piece of a zero class** (class value `0`). -/
theorem good_of_zero (hR : 1 ≤ R) (hNb : N ≤ P.N (p + 1) ^ 4)
    (hA : ∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p)
    (hb : 1 ≤ b) (hRs : ∀ j, P.L ≤ Rs j) (hC : 0 ≤ P.C₁) (hL : 0 < P.L) (π : PcA R p (objKind (2 * R)) A mkF)
    (hval : classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π = 0) :
    Nonempty (GoodPiece P p N J pat kSel t s A roots h b Rf σ Rs dag cP cθ mkF π) := by
  have hcW := carriersW_of P (hA _ (repPt_layered_memMk π))
  have hRs0 : ∀ j, 0 ≤ Rs j := fun j => hL.le.trans (hRs j)
  have hrest := zeroPiece_rest P (repPt π) cθ
  refine ⟨⟨zeroPiece P (repPt π), ∅, ∅, rfl, ?_, Nat.zero_le _,
    zeroPiece_soundFull P hR (repPt π) hcW hNb hL.ne' roots cθ⟩⟩
  refine ⟨?_, ⟨hrest.prot_card, hrest.fix_prot, hrest.fix_layer, hrest.filt_ok, hrest.ind_ok, hrest.ind_local⟩,
    by simp, by simp, by simp, ?_⟩
  · rw [hval]
    exact representsIntMKSel_zero _ _ N cP _ 0 roots _ hC hL.le
      (selMassMK_nonneg N (zero_le_one.trans hb) hRs0 kSel _)
  · rw [hval]
    exact representsIntMK_zero _ N (cP + 343) _ 0 roots _ hC hL.le (pow_nonneg (zero_le_one.trans hb) N)

end Good

end WaveTurbulence.Flower.Stage1MKGate

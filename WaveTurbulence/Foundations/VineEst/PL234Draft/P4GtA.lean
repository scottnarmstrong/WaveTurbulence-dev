/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Count

/-!
# Prop 6.3 for `q > q'`: the carrier sum as a sum over labelled codes

For fixed codes `(Q, X)`, the coherent carriers are exactly the labelled ones (`P4LayFrame`, `P4LayTree`,
`P4LayUnique`), one per valid label list. So:

* **`carrier_QX`**: the carrier sum over `(LQ, LX)` is the label sum
  `∑_{ls ∈ labC Q} ∑_{μ ∈ labsF q' X q} [BM b (κC + κT)] appC · conj appT`;
* `appC_nondom`, `appT_nondom`: non-dominant codes contribute `0`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-! ### Two finsum lemmas -/

theorem finsum_split3 {α β M : Type*} [AddCommMonoid M] (C : α → β → Prop) (A : α → Prop) (B : β → Prop)
    (R : α → β → Prop) (hC : ∀ a b, C a b ↔ A a ∧ B b ∧ R a b) (f : α → β → M) :
    (∑ᶠ (a) (b) (_ : C a b), f a b) = ∑ᶠ (a) (_ : A a), ∑ᶠ (b) (_ : B b) (_ : R a b), f a b := by
  refine finsum_congr fun a => ?_
  by_cases ha : A a
  · rw [finsum_eq_if (p := A a), ite_eq_left ha]
    refine finsum_congr fun b => ?_
    rw [finsum_eq_if, finsum_eq_if]
    by_cases hb : B b
    · rw [ite_eq_left hb, finsum_eq_if]
      exact if_congr (by rw [hC]; tauto) rfl rfl
    · rw [ite_eq_right hb, ite_eq_right fun h => hb ((hC a b).1 h).2.1]
  · rw [finsum_eq_if (p := A a), ite_eq_right ha]
    exact finsum_eq_zero_of_forall_eq_zero fun b => by
      rw [finsum_eq_if, ite_eq_right fun h => ha ((hC a b).1 h).1]

theorem finsum_cond_image {α β M : Type*} [AddCommMonoid M] (P : α → Prop) (s : Finset β) (e : β → α)
    (hinj : Set.InjOn e s) (himg : ∀ a, P a ↔ ∃ b ∈ s, e b = a) (g : α → M) :
    (∑ᶠ (a) (_ : P a), g a) = ∑ b ∈ s, g (e b) := by
  have hs : {a | P a} = e '' (s : Set β) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]
    exact himg a
  rw [← finsum_mem_coe_finset, ← finsum_mem_image hinj, ← hs]
  rfl

/-! ### The labelled carriers of a code -/

/-- The valid labels of a couple code. -/
def labC (q q' : ℕ) : RegCpl → Finset (List ℕ)
  | .type2 Xp _ _ => labsF q' Xp q
  | _ => {[]}

/-- The labelled carrier of a couple code. -/
noncomputable def eQ (q q' : ℕ) : RegCpl → List ℕ → LayeredGarden 2
  | .type2 Xp Xm Qlp, ls => lcLG Xp Xm Qlp ls q q'
  | Q, _ => constLayered (decodedCouple Q) q'

/-- The top-layer count of a labelled couple. -/
def κC (p q : ℕ) : RegCpl → List ℕ → ℕ
  | .type2 Xp _ _, ls => if q = p then (sliceL Xp ls q).size else 0
  | _, _ => 0

/-- The top-layer count of a labelled tree. -/
def κT (p q : ℕ) (X : RegChain) (μ : List ℕ) : ℕ := if q = p then (sliceL X μ q).size else 0

/-- The optional top-layer condition. -/
def BM : Option ℕ → ℕ → Prop
  | none, _ => True
  | some m, c => c = m

section Labelled

variable {p q q' : ℕ} (hlt : q' < q) (hqp : q ≤ p)
include hlt hqp

theorem coherQ_iff {Q : RegCpl} (hQ : Q.wf = true) (LQ : LayeredGarden 2) :
    IsCoherentCoupleAt p q q' Q LQ ↔ ∃ ls ∈ labC q q' Q, eQ q q' Q ls = LQ := by
  cases Q with
  | type2 Xp Xm Qlp =>
    constructor
    · intro hc
      obtain ⟨hL, he⟩ := coherent_lc_unique hlt.le hqp hc
      exact ⟨_, (mem_labsF Xp q _).2 hL, he.symm⟩
    · rintro ⟨ls, hls, rfl⟩
      exact coherent_lc Xm Qlp ⟨(mem_labsF Xp q ls).1 hls, hlt.le⟩ hqp hQ
  | triv =>
    constructor
    · intro hc
      exact ⟨[], Finset.mem_singleton_self _, (coherent_low_unique hlt.le hc rfl).symm⟩
    · rintro ⟨ls, -, rfl⟩
      exact coherent_low _ hlt.le hqp hQ rfl
  | type1 c Q₁ Q₂ Q₃ =>
    constructor
    · intro hc
      exact ⟨[], Finset.mem_singleton_self _, (coherent_low_unique hlt.le hc rfl).symm⟩
    · rintro ⟨ls, -, rfl⟩
      exact coherent_low _ hlt.le hqp hQ rfl

omit hqp in
theorem readback_C {Q : RegCpl} {ls : List ℕ} (hls : ls ∈ labC q q' Q) : cplLabels (eQ q q' Q ls) Q = ls := by
  cases Q with
  | type2 Xp Xm Qlp =>
    have hL := (mem_labsF Xp q ls).1 hls
    exact spine_readback Xp 1 ls _ q hL (lc_chain Xm Qlp ⟨hL, hlt.le⟩)
  | triv => exact (Finset.mem_singleton.1 hls).symm
  | type1 c Q₁ Q₂ Q₃ => exact (Finset.mem_singleton.1 hls).symm

omit hqp in
theorem injOn_eQ (Q : RegCpl) : Set.InjOn (eQ q q' Q) (labC q q' Q) := fun l₁ h₁ l₂ h₂ he => by
  rw [← readback_C hlt h₁, ← readback_C hlt h₂, he]

omit hlt hqp in
theorem lt_chain {X : RegChain} {μ : List ℕ} (h : LabOK q' X μ q ∧ q' ≤ q) (z : Fin 1 × Path)
    (hz : z ∈ chainNodesSet X 1 ((0 : Fin 1), [])) :
    layerAt (ltLG X μ q q') z = chainLay X μ q' ((0 : Fin 1), []) z := by
  have hn := (ChainEmb.of_decodesTree (decodedTree_decodes X 1)).mem_nodes hz
  rw [layerAt_ltLG h hn]
  show chainLay X μ q' (treeIota ((0 : Fin 1), [])) (treeIota z) = _
  exact chainLay_map treeIota treeIota_hom treeIota_under X μ _ z

omit hqp in
theorem readback_T {X : RegChain} {μ : List ℕ} (hμ : μ ∈ labsF q' X q) :
    spineLabels (ltLG X μ q q') ((0 : Fin 1), []) X = μ := by
  have hL := (mem_labsF X q μ).1 hμ
  exact spine_readback X 1 μ _ q hL (lt_chain ⟨hL, hlt.le⟩)

omit hqp in
theorem injOn_eX (X : RegChain) : Set.InjOn (fun μ => ltLG X μ q q') (labsF q' X q) := fun l₁ h₁ l₂ h₂ he => by
  rw [← readback_T hlt h₁, ← readback_T hlt h₂]
  exact congrArg (fun L => spineLabels L ((0 : Fin 1), []) X) he

theorem coherX_iff {X : RegChain} (hX : X.wf = true) (LX : LayeredGarden 1) :
    (IsCoherentTreeAt p q q' X LX ∧ LX.garden.sig 0 = 1) ↔ ∃ μ ∈ labsF q' X q, ltLG X μ q q' = LX := by
  constructor
  · rintro ⟨hc, hs⟩
    obtain ⟨hL, he⟩ := coherentTree_lt_unique hlt.le hc hs
    exact ⟨_, (mem_labsF X q _).2 hL, he.symm⟩
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨coherentTree_lt hX ⟨(mem_labsF X q μ).1 hμ, hlt.le⟩ hqp, ?_⟩
    rw [ltLG_garden]
    rfl

omit hlt hqp in
theorem eQ_order (Q : RegCpl) (ls : List ℕ) : (eQ q q' Q ls).garden.order = Q.size := by
  cases Q with
  | type2 Xp Xm Qlp => rw [show eQ q q' _ ls = lcLG Xp Xm Qlp ls q q' from rfl, lcLG_garden, decodedCouple_order]
  | triv => exact decodedCouple_order _
  | type1 c Q₁ Q₂ Q₃ => exact decodedCouple_order _

theorem eQ_count {Q : RegCpl} {ls : List ℕ} (hls : ls ∈ labC q q' Q) :
    topBranchCount (eQ q q' Q ls) p = κC p q Q ls := by
  cases Q with
  | type2 Xp Xm Qlp => exact count_lc ⟨(mem_labsF Xp q ls).1 hls, hlt.le⟩ hlt hqp
  | triv => exact count_low hlt hqp
  | type1 c Q₁ Q₂ Q₃ => exact count_low hlt hqp

end Labelled

/-! ### Non-dominant codes -/

theorem chain_app_nondom {d : ℕ} {δ r : ℝ} {F : Mom d → ℝ} {X : RegChain} (h : X.dominant = false) (ζ : ℤˣ)
    (t s : ℝ) (k : Mom d) : X.app δ r F ζ t s k = 0 := by
  unfold RegChain.app
  rw [h]
  rfl

theorem slice_nondom {d : ℕ} : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ), LabOK d X ls u → X.dominant = false →
    ∃ r, d ≤ r ∧ r ≤ u ∧ (sliceL X ls r).dominant = false
  | .nil, _, _, _, h => by simp [RegChain.dominant] at h
  | .pair .., [], _, h, _ => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, ⟨h1, h2, h3⟩, h => by
    by_cases hown : (inner.isNil && Qr.dominant && Qg.dominant) = true
    · have hr : rest.dominant = false := by
        simp only [RegChain.dominant] at h
        rw [hown] at h
        simpa using h
      obtain ⟨r, hr1, hr2, hr3⟩ := slice_nondom rest ls l h3 hr
      refine ⟨r, hr1, hr2.trans h2, ?_⟩
      show (if l = r then RegChain.pair m Qr Qg inner (sliceL rest ls r) else sliceL rest ls r).dominant = false
      split_ifs
      · simp only [RegChain.dominant, hr3, Bool.and_false]
      · exact hr3
    · refine ⟨l, h1, h2, ?_⟩
      show (if l = l then RegChain.pair m Qr Qg inner (sliceL rest ls l) else sliceL rest ls l).dominant = false
      rw [ite_eq_left rfl]
      simp only [RegChain.dominant]
      simp only [Bool.not_eq_true] at hown
      rw [hown, Bool.false_and]

theorem closeCouple_nondom {A Xm : RegChain} {Qlp : RegCpl} (h : (A.dominant && Xm.dominant && Qlp.dominant) = false) :
    (SourceApp.closeCouple A Xm Qlp).dominant = false := by
  unfold SourceApp.closeCouple
  split_ifs with hn
  · simp only [Bool.and_eq_true] at hn
    obtain ⟨hA, hM⟩ := hn
    rw [isNil_iff] at hA hM
    subst hA
    subst hM
    simpa [RegChain.dominant] using h
  · exact h

section Nondom

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {q q' : ℕ} (t s : ℝ) (k : Mom d) (hlt : q' < q)
include hlt

theorem appC_nondom {Q : RegCpl} {ls : List ℕ} (hQ : Q.dominant = false) (hls : ls ∈ labC q q' Q) :
    appC δ F q q' t s k Q ls = 0 := by
  cases Q with
  | triv => exact RegCpl.app_of_not_dominant _ _ _ _ hQ _ _ _
  | type1 c Q₁ Q₂ Q₃ => exact RegCpl.app_of_not_dominant _ _ _ _ hQ _ _ _
  | type2 Xp Xm Qlp =>
    have hL := (mem_labsF Xp q ls).1 hls
    show (∏ r ∈ Ioo q' q, (sliceL Xp ls r).app δ r (F r) 1 (r + 1) r k) *
      (sliceL Xp ls q).app δ q (F q) 1 t q k *
      (SourceApp.closeCouple (sliceL Xp ls q') Xm Qlp).app δ q' (F q') (q' + 1) s k = 0
    have hbot : (sliceL Xp ls q').dominant = false ∨ (Xm.dominant && Qlp.dominant) = false →
        (SourceApp.closeCouple (sliceL Xp ls q') Xm Qlp).app δ q' (F q') (q' + 1) s k = 0 := fun h =>
      RegCpl.app_of_not_dominant _ _ _ _ (closeCouple_nondom (by
        rcases h with h | h
        · rw [h, Bool.false_and, Bool.false_and]
        · rw [Bool.and_assoc, h, Bool.and_false])) _ _ _
    by_cases hXp : Xp.dominant = true
    · have h' : (Xm.dominant && Qlp.dominant) = false := by
        simp only [RegCpl.dominant, hXp, Bool.true_and] at hQ
        exact hQ
      rw [hbot (Or.inr h'), mul_zero]
    · obtain ⟨r, hr1, hr2, hr3⟩ := slice_nondom Xp ls q hL (by simpa using hXp)
      by_cases hrq' : r = q'
      · subst hrq'
        rw [hbot (Or.inl hr3), mul_zero]
      · by_cases hrq : r = q
        · subst hrq
          rw [chain_app_nondom hr3, mul_zero, zero_mul]
        · rw [Finset.prod_eq_zero (i := r) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩) (chain_app_nondom hr3 _ _ _ _),
            zero_mul, zero_mul]

theorem appT_nondom {X : RegChain} {μ : List ℕ} (hX : X.dominant = false) (hμ : μ ∈ labsF q' X q) :
    appT δ F q q' t s k X μ = 0 := by
  have hL := (mem_labsF X q μ).1 hμ
  unfold appT
  obtain ⟨r, hr1, hr2, hr3⟩ := slice_nondom X μ q hL hX
  by_cases hrq' : r = q'
  · subst hrq'
    rw [chain_app_nondom hr3, mul_zero]
  · by_cases hrq : r = q
    · subst hrq
      rw [chain_app_nondom hr3, mul_zero, zero_mul]
    · rw [Finset.prod_eq_zero (i := r) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩) (chain_app_nondom hr3 _ _ _ _),
        zero_mul, zero_mul]

end Nondom

/-! ### The carrier sum of a pair of codes -/

/-- The label sum of a pair of codes. -/
noncomputable def labSum {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) (p q q' : ℕ) (t s : ℝ) (k : Mom d) (b : Option ℕ)
    (Q : RegCpl) (X : RegChain) : ℂ :=
  ∑ ls ∈ labC q q' Q, ∑ μ ∈ labsF q' X q,
    if BM b (κC p q Q ls + κT p q X μ) then appC δ F q q' t s k Q ls * star (appT δ F q q' t s k X μ) else 0

section Carrier

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} (t s : ℝ) (k : Mom d) (n : ℕ) (b : Option ℕ)
  (hlt : q' < q) (hqp : q ≤ p)
include hlt hqp

/-- **The carrier sum of a pair of codes is its label sum.** -/
theorem carrier_QX (Q : RegCpl) (X : RegChain) :
    (∑ᶠ (LQ : LayeredGarden 2) (LX : LayeredGarden 1) (_ : CoherentPairCarrier p q q' n b Q X LQ LX),
      SourceApp.couple δ F LQ Q q q' t s k * star (SourceApp.tree δ F LX X q q' t s k)) =
    if Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n then labSum δ F p q q' t s k b Q X else 0 := by
  by_cases hw : Q.wf = true ∧ X.wf = true
  · rw [finsum_split3 _ (fun LQ => IsCoherentCoupleAt p q q' Q LQ)
      (fun LX => IsCoherentTreeAt p q q' X LX ∧ LX.garden.sig 0 = 1)
      (fun LQ LX => LQ.garden.order + LX.garden.order = 2 * n ∧
        BM b (topBranchCount LQ p + topBranchCount LX p))
      (fun LQ LX => by cases b <;> simp only [CoherentPairCarrier, BM] <;> tauto)]
    rw [finsum_cond_image _ (labC q q' Q) (eQ q q' Q) (injOn_eQ hlt Q) (coherQ_iff hlt hqp hw.1)]
    have step : ∀ ls ∈ labC q q' Q, (∑ᶠ (LX : LayeredGarden 1)
        (_ : IsCoherentTreeAt p q q' X LX ∧ LX.garden.sig 0 = 1)
        (_ : (eQ q q' Q ls).garden.order + LX.garden.order = 2 * n ∧
          BM b (topBranchCount (eQ q q' Q ls) p + topBranchCount LX p)),
        SourceApp.couple δ F (eQ q q' Q ls) Q q q' t s k * star (SourceApp.tree δ F LX X q q' t s k)) =
        ∑ μ ∈ labsF q' X q, if Q.size + X.size = 2 * n ∧ BM b (κC p q Q ls + κT p q X μ) then
          appC δ F q q' t s k Q ls * star (appT δ F q q' t s k X μ) else 0 := by
      intro ls hls
      rw [finsum_cond_image _ (labsF q' X q) (fun μ => ltLG X μ q q') (injOn_eX hlt X)
        (coherX_iff hlt hqp hw.2)]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hL := (mem_labsF X q μ).1 hμ
      have hs : (ltLG X μ q q').garden.sig 0 = 1 := by rw [ltLG_garden]; rfl
      have hord : (ltLG X μ q q').garden.order = X.size := by rw [ltLG_garden, decodedTree_order]
      rw [finsum_eq_if]
      refine if_congr ?_ ?_ rfl
      · rw [eQ_order, hord, eQ_count hlt hqp hls, count_lt ⟨hL, hlt.le⟩ hlt hqp]
        rfl
      · rw [sourceCouple_eq_appC δ F q q' t s k hlt, readback_C hlt hls,
          sourceTree_eq_appT δ F q q' t s k hlt _ X hs, readback_T hlt hμ]
    rw [Finset.sum_congr rfl step]
    unfold labSum
    by_cases hn : Q.size + X.size = 2 * n
    · rw [ite_eq_left ⟨hw.1, hw.2, hn⟩]
      refine Finset.sum_congr rfl fun ls _ => Finset.sum_congr rfl fun μ _ => ?_
      exact if_congr (by simp [hn]) rfl rfl
    · rw [ite_eq_right fun h => hn h.2.2]
      exact Finset.sum_eq_zero fun ls _ => Finset.sum_eq_zero fun μ _ => ite_eq_right fun h => hn h.1
  · rw [ite_eq_right fun h => hw ⟨h.1, h.2.1⟩]
    refine finsum_eq_zero_of_forall_eq_zero fun LQ => finsum_eq_zero_of_forall_eq_zero fun LX => ?_
    rw [finsum_eq_if, ite_eq_right fun h => hw ⟨h.1.1, h.2.1.1⟩]

end Carrier

end WaveTurbulence.PL234

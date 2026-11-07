/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Family

/-! # BOT-DECOMP: the index type of the bottom bundle (R60, F-W2-BOT)

The bottom bundle `psiBot` (4d-B2) sums over `canonFinsetK p kind A c0` (pairs `(state, chain region)`), not over `zpFinset` (pairs `(state, split)`): at a
member of piece index `0` the chain region has the lower joint of the member as its bottom joint, so there is no lower block and hence no `SplitAt`.
This module mirrors `ZpSurjStmt` (`zpSet`, `ZpSurj`), `P1.ZpLayers`, `BundleState` (`bsA`, `bsB`, `bsigma`, `bundle_eq_repl`'s row lemmas) and
`CarrierSum` for the index type `BT w ι = Σ Bs, ChainAt Bs.skeleton Bs.family`.  Every definition only reads `b.1` (the state).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C

/-- The index type of the bottom class: states with their chain region. -/
abbrev BT (w : ℕ) (ι : Type*) : Type _ := Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family

section
variable {w : ℕ} {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (kind : Bool) (pstar : ι) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)

/-- The states of the bottom class of sign `σ` with both roots `<= L4` (mirror of `zpSet`). -/
def botSet (σ : ℤˣ) : Set (BT w ι) :=
  {G | G ∈ canonFinsetK p kind A c0 ∧ nuOf G.1 pstar = σ ∧ ZpRootsLE A G.1 pstar}

/-- **`BotSurj`**: the bottom analogue of `ZpSurj` (R51, R60): the class `canonFinsetK p kind A c0` of the bottom vine realizes the whole coherent
pair carrier. -/
structure BotSurj : Prop where
  coherent : ∀ G ∈ canonFinsetK p kind A c0,
    IsCoherentCoupleAt p (zpQQ G.1 pstar).1 (zpQQ G.1 pstar).2 (zpCodeC G.1 pstar) (zpObjC G.1 pstar) ∧
    IsCoherentTreeAt p (zpBranchQ G.1 pstar).1 (zpBranchQ G.1 pstar).2 (zpCodeT G.1 pstar) (zpObjT G.1 pstar)
  twin : ∃ τ : BT w ι → BT w ι,
    Set.BijOn τ (botSet p kind pstar A c0 (-1)) (botSet p kind pstar A c0 1) ∧
    ∀ G ∈ botSet p kind pstar A c0 (-1),
      IsConjugateCouple (sigStar G.1 pstar).2.1 (sigStar (τ G).1 pstar).2.1 ∧
      IsConjugateTree (sigStar G.1 pstar).2.2 (sigStar (τ G).1 pstar).2.2 ∧
      (zpData (τ G).1 pstar).1 = conjCpl (zpData G.1 pstar).1 ∧
      (zpData (τ G).1 pstar).2.1 = conjChain (zpData G.1 pstar).2.1
  carrier : Set.BijOn (fun G : BT w ι => zpCarrierOf G.1 pstar) (botSet p kind pstar A c0 (-1)) {c | ZpCarrier p A pstar c}

/-- **`BotLayers`**: the bottom analogue of `P1.ZpLayers` (layer numerals of the vine). -/
structure BotLayers : Prop where
  le : zpQ2 A pstar ≤ zpQ4 A pstar
  le_p : zpQ4 A pstar ≤ p
  pair : ∀ G ∈ canonFinsetK p kind A c0, (zpQQ G.1 pstar).2 = zpQ2 A pstar ∧
    (zpQQ G.1 pstar).2 ≤ (zpQQ G.1 pstar).1 ∧ (zpQQ G.1 pstar).1 ≤ p
  branch : ∀ G ∈ canonFinsetK p kind A c0, (zpBranchQ G.1 pstar).2 = zpQ2 A pstar ∧
    (zpBranchQ G.1 pstar).2 ≤ (zpBranchQ G.1 pstar).1

open Classical in
/-- The index set of the II-b terms: all II-b states of the class. -/
noncomputable def botB : Finset (BT w ι) := (canonFinsetK p kind A c0).filter fun G => nuOf G.1 pstar ≠ 1

open Classical in
/-- The index set of the II-a terms (twin pairs indexed by the II-b member, and the unpaired II-a states with a root `> L4`). -/
noncomputable def botA : Finset (BT w ι) :=
  (canonFinsetK p kind A c0).filter fun G =>
    (nuOf G.1 pstar ≠ 1 ∧ ZpRootsLE A G.1 pstar) ∨ (nuOf G.1 pstar = 1 ∧ ¬ ZpRootsLE A G.1 pstar)

open Classical in
/-- The II-a state standing for the index `b`. -/
noncomputable def botSigma (τ : BT w ι → BT w ι) (b : BT w ι) : BT w ι := if nuOf b.1 pstar = 1 then b else τ b

/-- The source approximant (at the parameters `zpQQ`) of the carrier-side couple of the index `b`. -/
noncomputable def botSrcQ (κ : KPar d) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) (zpQQ b.1 pstar).1
    (zpQQ b.1 pstar).2 t s k

/-- The source approximant (at the parameters `zpBranchQ`) of the carrier-side tree of the index `b`. -/
noncomputable def botSrcT (κ : KPar d) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) (zpBranchQ b.1 pstar).1
    (zpBranchQ b.1 pstar).2 t s k

/-- The remainder of the carrier-side couple: exact kernel minus approximant. -/
noncomputable def botRemQ (κ : KPar d) (Qf : BT w ι → ℝ → ℝ → Mom d → ℂ) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) t s k - Qf b t s k

/-- The remainder of the carrier-side tree. -/
noncomputable def botRemT (κ : KPar d) (Tf : BT w ι → ℝ → ℝ → Mom d → ℂ) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) t s k - Tf b t s k

variable (κ : KPar d) (Qf Tf : BT w ι → ℝ → ℝ → Mom d → ℂ)

/-- Exact rows of a II-b index: `K*_Q = Q + R_Q`. -/
theorem botRowQ_B (b : BT w ι) (hb : nuOf b.1 pstar ≠ 1) (t s : ℝ) (k : Mom d) :
    rowQ κ b.1 pstar t s k = Qf b t s k + botRemQ pstar κ Qf b t s k := by
  have h := (units_ne_one_iff _).mp hb
  unfold botRemQ rowQ
  rw [zpObjC_of_neg h]; ring

/-- Exact tree row of a II-b index: `K*_{T̄} = T̄ + conj R_T`. -/
theorem botRowT_B (b : BT w ι) (hb : nuOf b.1 pstar ≠ 1) (t s : ℝ) (k : Mom d) :
    rowT κ b.1 pstar t s k = cconj (Tf) b t s k + (starRingEnd ℂ) (botRemT pstar κ Tf b t s k) := by
  have h := (units_ne_one_iff _).mp hb
  have hc := PL234.KTstar_conj κ.L κ.γ κ.δ κ.F (conjLayered_isConjugateBy (sigStar b.1 pstar).2.2 (Equiv.refl (Fin 1))) t s k
  unfold botRemT rowT cconj
  rw [zpObjT_of_neg h, hc, map_sub]
  simp

variable (τ : BT w ι → BT w ι)

/-- Exact couple row of the II-a state standing for an index of `botA`: `K*_{Q̄} = Q̄ + conj R_Q`. -/
theorem botRowQ_A {b : BT w ι} (hb : (nuOf b.1 pstar = 1) ∨
      (nuOf b.1 pstar ≠ 1 ∧ IsConjugateCouple (sigStar b.1 pstar).2.1 (sigStar (τ b).1 pstar).2.1))
    (t s : ℝ) (k : Mom d) :
    rowQ κ (botSigma pstar τ b).1 pstar t s k = cswap (Qf) b t s k + (starRingEnd ℂ) (botRemQ pstar κ Qf b s t k) := by
  classical
  unfold cswap botRemQ rowQ botSigma
  rcases hb with h | ⟨h, hc⟩
  · rw [if_pos h, zpObjC_of_pos h]
    have := PL234.KQstar_conj κ.L κ.γ κ.δ κ.F (conjLayered_isConjugateBy (sigStar b.1 pstar).2.1 (Equiv.swap (0 : Fin 2) 1)) s t k
    rw [map_sub, ← sub_eq_zero]
    rw [this]; simp
  · have h' := (units_ne_one_iff _).mp h
    rw [if_neg h, zpObjC_of_neg h', PL234.KQstar_conj κ.L κ.γ κ.δ κ.F hc t s k]
    simp

/-- Exact tree row of the II-a state standing for an index of `botA`: `K*_T = T + R_T`. -/
theorem botRowT_A {b : BT w ι} (hb : (nuOf b.1 pstar = 1) ∨
      (nuOf b.1 pstar ≠ 1 ∧ IsConjugateTree (sigStar b.1 pstar).2.2 (sigStar (τ b).1 pstar).2.2))
    (t s : ℝ) (k : Mom d) :
    rowT κ (botSigma pstar τ b).1 pstar t s k = Tf b t s k + botRemT pstar κ Tf b t s k := by
  classical
  unfold botRemT rowT botSigma
  rcases hb with h | ⟨h, hc⟩
  · rw [if_pos h, zpObjT_of_pos h]; ring
  · have h' := (units_ne_one_iff _).mp h
    rw [if_neg h, zpObjT_of_neg h', PL234.KTstar_conj κ.L κ.γ κ.δ κ.F hc t s k,
      PL234.KTstar_conj κ.L κ.γ κ.δ κ.F (conjLayered_isConjugateBy (sigStar b.1 pstar).2.2 (Equiv.refl (Fin 1))) t s k]
    ring

open Classical in
theorem sum_botA_reindex
    (hbij : Set.BijOn τ (botSet p kind pstar A c0 (-1)) (botSet p kind pstar A c0 1)) (F : BT w ι → ℂ) :
    ∑ b ∈ botA p kind pstar A c0, F (botSigma pstar τ b) =
      ∑ G ∈ (canonFinsetK p kind A c0).filter (fun G => nuOf G.1 pstar = 1), F G := by
  refine Finset.sum_nbij (botSigma pstar τ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro b hb
    simp only [botA, Finset.mem_filter] at hb
    simp only [Finset.mem_filter]
    unfold botSigma
    rcases hb with ⟨hz, ⟨hn, hr⟩ | ⟨hn, hr⟩⟩
    · have hbm : b ∈ botSet p kind pstar A c0 (-1) := ⟨hz, (units_ne_one_iff _).mp hn, hr⟩
      rw [if_neg hn]
      have := hbij.mapsTo hbm
      exact ⟨this.1, this.2.1⟩
    · rw [if_pos hn]; exact ⟨hz, hn⟩
  · intro b1 hb1 b2 hb2 he
    simp only [Finset.mem_coe, botA, Finset.mem_filter] at hb1 hb2
    unfold botSigma at he
    by_cases h1 : nuOf b1.1 pstar = 1 <;> by_cases h2 : nuOf b2.1 pstar = 1
    · rw [if_pos h1, if_pos h2] at he; exact he
    · rw [if_pos h1, if_neg h2] at he
      have hb2m : b2 ∈ botSet p kind pstar A c0 (-1) := by
        rcases hb2 with ⟨hz, ⟨hn, hr⟩ | ⟨hn, _⟩⟩
        · exact ⟨hz, (units_ne_one_iff _).mp hn, hr⟩
        · exact absurd hn h2
      have hm := (hbij.mapsTo hb2m)
      rw [← he] at hm
      rcases hb1 with ⟨_, ⟨hn, _⟩ | ⟨_, hr⟩⟩
      · exact absurd h1 hn
      · exact absurd hm.2.2 hr
    · rw [if_neg h1, if_pos h2] at he
      have hb1m : b1 ∈ botSet p kind pstar A c0 (-1) := by
        rcases hb1 with ⟨hz, ⟨hn, hr⟩ | ⟨hn, _⟩⟩
        · exact ⟨hz, (units_ne_one_iff _).mp hn, hr⟩
        · exact absurd hn h1
      have hm := (hbij.mapsTo hb1m)
      rw [he] at hm
      rcases hb2 with ⟨_, ⟨hn, _⟩ | ⟨_, hr⟩⟩
      · exact absurd h2 hn
      · exact absurd hm.2.2 hr
    · rw [if_neg h1, if_neg h2] at he
      have hm : ∀ b : BT w ι, b ∈ botA p kind pstar A c0 → ¬ nuOf b.1 pstar = 1 →
          b ∈ botSet p kind pstar A c0 (-1) := by
        intro b hb hn
        simp only [botA, Finset.mem_filter] at hb
        rcases hb with ⟨hz, ⟨hn', hr⟩ | ⟨hn', _⟩⟩
        · exact ⟨hz, (units_ne_one_iff _).mp hn', hr⟩
        · exact absurd hn' hn
      exact hbij.injOn (hm b1 (by simp only [botA, Finset.mem_filter]; exact hb1) h1)
        (hm b2 (by simp only [botA, Finset.mem_filter]; exact hb2) h2) he
  · intro G hG
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hG
    by_cases hr : ZpRootsLE A G.1 pstar
    · have hGm : G ∈ botSet p kind pstar A c0 1 := ⟨hG.1, hG.2, hr⟩
      obtain ⟨b, hb, hbG⟩ := hbij.surjOn hGm
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_coe, botA, Finset.mem_filter]
        exact ⟨hb.1, Or.inl ⟨by rw [hb.2.1]; decide, hb.2.2⟩⟩
      · unfold botSigma
        have : ¬ nuOf b.1 pstar = 1 := by rw [hb.2.1]; decide
        rw [if_neg this]; exact hbG
    · refine ⟨G, ?_, ?_⟩
      · simp only [Finset.mem_coe, botA, Finset.mem_filter]
        exact ⟨hG.1, Or.inr ⟨hG.2, hr⟩⟩
      · unfold botSigma; rw [if_pos hG.2]

open Classical in
/-- The finset of II-b states of the bottom class with carrier-side roots `<= L4`. -/
noncomputable def botMinusFin : Finset (BT w ι) :=
  (canonFinsetK p kind A c0).filter fun G => nuOf G.1 pstar = -1 ∧ ZpRootsLE A G.1 pstar

theorem coe_botMinusFin :
    (botMinusFin p kind pstar A c0 : Set (BT w ι)) = botSet p kind pstar A c0 (-1) := by
  classical
  ext G
  simp [botMinusFin, botSet]

/-- **The carrier `finsum` of `reality_all` is the finite sum over the II-b states with roots `<= L4`** (mirror of `carrier_sum_eq`). -/
theorem bot_carrier_sum_eq
    (hbij : Set.BijOn (fun G : BT w ι => zpCarrierOf G.1 pstar) (botSet p kind pstar A c0 (-1)) {c | ZpCarrier p A pstar c})
    (f : RegCpl → RegChain → LayeredGarden 2 → LayeredGarden 1 → ℂ) :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) Q X LQ LX),
        f Q X LQ LX) =
      ∑ G ∈ botMinusFin p kind pstar A c0, f (zpCarrierOf G.1 pstar).1 (zpCarrierOf G.1 pstar).2.1
        (zpCarrierOf G.1 pstar).2.2.1 (zpCarrierOf G.1 pstar).2.2.2 := by
  classical
  have hfin : ({c | ZpCarrier p A pstar c} : Set _).Finite := by
    rw [← hbij.image_eq]
    refine Set.Finite.image _ ?_
    rw [← coe_botMinusFin p kind pstar A c0]
    exact Finset.finite_toSet _
  have h1 := carrier_finsum {c | ZpCarrier p A pstar c} hfin f
  have h2 : (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) Q X LQ LX),
        f Q X LQ LX) = ∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : (Q, X, LQ, LX) ∈ {c | ZpCarrier p A pstar c}), f Q X LQ LX := rfl
  rw [h2, h1, ← hbij.image_eq, finsum_mem_image hbij.injOn, ← coe_botMinusFin p kind pstar A c0, finsum_mem_coe_finset]

end
end WaveTurbulence.VineEstS5C.P4.Bot

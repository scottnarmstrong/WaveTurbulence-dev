/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Construct4

/-!
# A decoration is determined by its root value and link parameters (packet C2)

`cplDec_determined`: if `f` decorates `Q` at `(a, b)`, `f a = r` and `f` has parameters `θ` at the
chosen nodes, then `f = cplVal θ Q a b r` at every node of the code.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- The children values of a node from its value, its parameters and the node relation. -/
theorem children_of_params {f : Fin w × Path → V} {a : Fin w × Path} {u : V} {t : V × V}
    (ha : NodeRel f a) (hu : f a = u) (hx : xv f a = t.1) (hy : yv f a = t.2) :
    ∀ i, f (addrExt a [i]) = childVals u t i := by
  unfold xv at hx; unfold yv at hy; unfold NodeRel at ha
  have h0 : f (addrExt a [0]) = u + t.1 := by rw [← hx, hu]; abel
  have h2 : f (addrExt a [2]) = u - t.2 := by rw [← hy, hu]; abel
  have h1 : f (addrExt a [1]) = u + t.1 - t.2 := by
    have : f (addrExt a [1]) = f (addrExt a [0]) + f (addrExt a [2]) - f a := by
      rw [ha]; abel
    rw [this, h0, h2, hu]; abel
  intro i
  fin_cases i <;> simp [childVals, h0, h1, h2]

mutual
/-- **A decoration is determined by its root value and its link parameters.** -/
theorem cplDec_determined (θ : Fin w × Path → V × V) (Q : RegCpl) (a b : Fin w × Path) (r : V)
    (h : Indep a b) (f : Fin w × Path → V) (hd : CplDec f Q a b) (hr : f a = r)
    (hθ : ∀ l ∈ Q.linksAt a b, xv f l.1 = (θ l.1).1 ∧ yv f l.1 = (θ l.1).2) :
    ∀ z ∈ pairEndpoints (Q.linksAt a b) ∪ pairEndpoints (Q.pairsAt a b),
      f z = cplVal θ Q a b r z := by
  have hb : f b = r := (cplDec_root_eq f Q a b hd).symm.trans hr
  cases Q with
  | triv =>
    intro z hz
    simp only [RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_nil, pairEndpoints_singleton,
      Finset.empty_union, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [cplVal, hr, hb]
  | type1 c Q₁ Q₂ Q₃ =>
    obtain ⟨ha, -, h₁, h₂, h₃⟩ := hd
    have D := fun z => type1_dispatch θ c Q₁ Q₂ Q₃ a b r h z
    have hθa := hθ (a, b) List.mem_cons_self
    have fc := children_of_params ha hr hθa.1 hθa.2
    have hθ' : ∀ l ∈ Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
        Q₂.linksAt (addrExt b [1]) (addrExt a [1]) ++
        Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2]), _ :=
      fun l hl => hθ l (List.mem_cons_of_mem _ hl)
    have I₁ := cplDec_determined θ Q₁ _ _ _ (h.ext _ _) f h₁ (fc 0)
      (fun l hl => hθ' l (by simp [hl]))
    have I₂ := cplDec_determined θ Q₂ _ _ _ (h.symm.ext _ _) f h₂
      ((cplDec_root_eq f Q₂ _ _ h₂).trans (fc 1)) (fun l hl => hθ' l (by simp [hl]))
    have I₃ := cplDec_determined θ Q₃ _ _ _ (h.ext _ _) f h₃ (fc 2)
      (fun l hl => hθ' l (by simp [hl]))
    intro z hz
    simp only [RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_cons, pairEndpoints_append,
      Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl | ((h' | h') | h')) | ((h' | h') | h')
    · simp [cplVal, hr]
    · simp [cplVal, hb]
    · rw [I₁ z (Finset.mem_union_left _ h')]
      exact ((D z).1 (cpl_endpoints_under Q₁ _ _ z (Finset.mem_union_left _ h'))).symm
    · rw [I₂ z (Finset.mem_union_left _ h')]
      exact ((D z).2.1 (cpl_endpoints_under Q₂ _ _ z (Finset.mem_union_left _ h'))).symm
    · rw [I₃ z (Finset.mem_union_left _ h')]
      exact ((D z).2.2 (cpl_endpoints_under Q₃ _ _ z (Finset.mem_union_left _ h'))).symm
    · rw [I₁ z (Finset.mem_union_right _ h')]
      exact ((D z).1 (cpl_endpoints_under Q₁ _ _ z (Finset.mem_union_right _ h'))).symm
    · rw [I₂ z (Finset.mem_union_right _ h')]
      exact ((D z).2.1 (cpl_endpoints_under Q₂ _ _ z (Finset.mem_union_right _ h'))).symm
    · rw [I₃ z (Finset.mem_union_right _ h')]
      exact ((D z).2.2 (cpl_endpoints_under Q₃ _ _ z (Finset.mem_union_right _ h'))).symm
  | type2 Xp Xm Qlp =>
    obtain ⟨hp, hm, hl⟩ := hd
    have iQ := h.ext Xp.lonePath Xm.lonePath
    have vQ := cplVal_root θ Qlp _ _ r iQ
    have Ip := chainDec_determined θ Xp 1 a r _ vQ.1 f hp hr
      (fun l hl' => hθ l (by simp [RegCpl.linksAt, hl']))
    have Im := chainDec_determined θ Xm (-1) b r _ vQ.2 f hm hb
      (fun l hl' => hθ l (by simp [RegCpl.linksAt, hl']))
    have IQ := cplDec_determined θ Qlp _ _ r iQ f hl
      ((chainDec_lone_eq f Xp 1 a hp).symm.trans hr)
      (fun l hl' => hθ l (by simp [RegCpl.linksAt, hl']))
    have gA : ∀ z, Under a z → cplVal θ (.type2 Xp Xm Qlp) a b r z =
        chainVal θ Xp 1 a r (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) z :=
      fun z hz => by simp only [cplVal, hz, ↓reduceIte]
    have gB : ∀ z, Under b z → cplVal θ (.type2 Xp Xm Qlp) a b r z =
        chainVal θ Xm (-1) b r (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) z :=
      fun z hz => by
        have : ¬ Under a z := fun ha => h.not_both ha hz
        simp only [cplVal, this, ↓reduceIte]
    have gQ : ∀ z, Under (addrExt a Xp.lonePath) z ∨ Under (addrExt b Xm.lonePath) z →
        cplVal θ (.type2 Xp Xm Qlp) a b r z =
          cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r z := fun z hz => by
      rcases hz with hz | hz
      · rw [gA z (under_trans (under_ext _ _) hz), chainVal_lone θ Xp 1 a r _ z hz]
      · rw [gB z (under_trans (under_ext _ _) hz), chainVal_lone θ Xm (-1) b r _ z hz]
    intro z hz
    simp only [RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_append, Finset.mem_union] at hz
    rcases hz with ((h' | h') | h') | ((h' | h') | h')
    · rw [Ip z (Finset.mem_union_left _ h'),
        gA z (chain_endpoints_region Xp 1 a z (Finset.mem_union_left _ h')).1]
    · rw [Im z (Finset.mem_union_left _ h'),
        gB z (chain_endpoints_region Xm (-1) b z (Finset.mem_union_left _ h')).1]
    · rw [IQ z (Finset.mem_union_left _ h'),
        gQ z (cpl_endpoints_under Qlp _ _ z (Finset.mem_union_left _ h'))]
    · rw [Ip z (Finset.mem_union_right _ h'),
        gA z (chain_endpoints_region Xp 1 a z (Finset.mem_union_right _ h')).1]
    · rw [Im z (Finset.mem_union_right _ h'),
        gB z (chain_endpoints_region Xm (-1) b z (Finset.mem_union_right _ h')).1]
    · rw [IQ z (Finset.mem_union_right _ h'),
        gQ z (cpl_endpoints_under Qlp _ _ z (Finset.mem_union_right _ h'))]
termination_by structural Q

/-- Chain version of `cplDec_determined`. -/
theorem chainDec_determined (θ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (u : V) (cont : (Fin w × Path) → V) (hc : cont (addrExt a X.lonePath) = u)
    (f : Fin w × Path → V) (hd : ChainDec f X ζ a) (hr : f a = u)
    (hθ : ∀ l ∈ X.linksAt ζ a, xv f l.1 = (θ l.1).1 ∧ yv f l.1 = (θ l.1).2) :
    ∀ z ∈ pairEndpoints (X.linksAt ζ a) ∪ pairEndpoints (X.pairsAt ζ a),
      f z = chainVal θ X ζ a u cont z := by
  cases X with
  | nil => simp [RegChain.linksAt, RegChain.pairsAt]
  | pair m Qr Qg inner rest =>
    obtain ⟨ha, hb, hrd, hgd, hi, hs⟩ := hd
    obtain ⟨vA, vnb, -, -, -⟩ := chainVal_pair_vals θ m Qr Qg inner rest ζ a u cont hc
    have D := fun z => chain_dispatch θ m Qr Qg inner rest ζ a u cont z
    have hθa := hθ (a, _) List.mem_cons_self
    have fc := children_of_params ha hr hθa.1 hθa.2
    have mR : ∀ l, l ∈ (if slotSign ζ m.red.1 = 1 then
          Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) →
        l ∈ (RegChain.pair m Qr Qg inner rest).linksAt ζ a := fun l hl => by
      simp only [RegChain.linksAt, List.mem_cons, List.mem_append]; tauto
    have mG : ∀ l, l ∈ (if slotSign ζ m.green.1 = 1 then
          Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) →
        l ∈ (RegChain.pair m Qr Qg inner rest).linksAt ζ a := fun l hl => by
      simp only [RegChain.linksAt, List.mem_cons, List.mem_append]; tauto
    have mI : ∀ l, l ∈ inner.linksAt (slotSign ζ m.c) (addrExt a [m.c]) →
        l ∈ (RegChain.pair m Qr Qg inner rest).linksAt ζ a := fun l hl => by
      simp only [RegChain.linksAt, List.mem_cons, List.mem_append]; tauto
    have mS : ∀ l, l ∈ rest.linksAt (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) →
        l ∈ (RegChain.pair m Qr Qg inner rest).linksAt ζ a := fun l hl => by
      simp only [RegChain.linksAt, List.mem_cons, List.mem_append]; tauto
    -- conservation through the pair
    have er := oriented_eq (fun x y hh => cplDec_root_eq f Qr x y hh) hrd
    have eg := oriented_eq (fun x y hh => cplDec_root_eq f Qg x y hh) hgd
    have ei := chainDec_lone_eq f inner _ _ hi
    rw [addrExt_append] at ei
    have hb' : f (addrExt a ([m.c] ++ inner.lonePath)) =
        f (addrExt a ([m.c] ++ inner.lonePath ++ [0])) -
          f (addrExt a ([m.c] ++ inner.lonePath ++ [1])) +
          f (addrExt a ([m.c] ++ inner.lonePath ++ [2])) := by
      rw [hb]; simp only [NodeRel, addrExt_append]
    have flone := miniTree_local m (f a) (f (addrExt a ([m.c] ++ inner.lonePath)))
      (fun i => f (addrExt a [i])) (fun i => f (addrExt a ([m.c] ++ inner.lonePath ++ [i])))
      ha hb' ei er eg
    have fnb : f (addrExt a ([m.c] ++ inner.lonePath)) = childVals u (θ a) m.c := ei.symm.trans (fc _)
    have hcr : cont (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath) = u := by
      rw [← hc, chain_lonePath_eq]
    -- the four parts
    have IR : ∀ z, (z ∈ pairEndpoints (if slotSign ζ m.red.1 = 1 then
          Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∨
        z ∈ pairEndpoints (if slotSign ζ m.red.1 = 1 then
          Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))) →
        f z = chainVal θ (.pair m Qr Qg inner rest) ζ a u cont z := fun z hz => by
      by_cases hsr : slotSign ζ m.red.1 = 1 <;> simp only [hsr, ↓reduceIte] at hrd hz mR ⊢
      · have I := cplDec_determined θ Qr _ _ _ (indep_red m _ a) f hrd (fc _)
          (fun l hl => hθ l (mR l hl))
        rw [I z (Finset.mem_union.2 hz), (D z).1 (cpl_endpoints_under Qr _ _ z
          (Finset.mem_union.2 hz))]
        simp only [hsr, ↓reduceIte]
      · have I := cplDec_determined θ Qr _ _ _ (indep_red m _ a).symm f hrd (er.symm.trans (fc _))
          (fun l hl => hθ l (mR l hl))
        rw [I z (Finset.mem_union.2 hz), (D z).1 (cpl_endpoints_under Qr _ _ z
          (Finset.mem_union.2 hz)).symm]
        simp only [hsr, ↓reduceIte]
    have IG : ∀ z, (z ∈ pairEndpoints (if slotSign ζ m.green.1 = 1 then
          Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∨
        z ∈ pairEndpoints (if slotSign ζ m.green.1 = 1 then
          Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))) →
        f z = chainVal θ (.pair m Qr Qg inner rest) ζ a u cont z := fun z hz => by
      by_cases hsg : slotSign ζ m.green.1 = 1 <;> simp only [hsg, ↓reduceIte] at hgd hz mG ⊢
      · have I := cplDec_determined θ Qg _ _ _ (indep_green m _ a) f hgd (fc _)
          (fun l hl => hθ l (mG l hl))
        rw [I z (Finset.mem_union.2 hz), (D z).2.1 (cpl_endpoints_under Qg _ _ z
          (Finset.mem_union.2 hz))]
        simp only [hsg, ↓reduceIte]
      · have I := cplDec_determined θ Qg _ _ _ (indep_green m _ a).symm f hgd (eg.symm.trans (fc _))
          (fun l hl => hθ l (mG l hl))
        rw [I z (Finset.mem_union.2 hz), (D z).2.1 (cpl_endpoints_under Qg _ _ z
          (Finset.mem_union.2 hz)).symm]
        simp only [hsg, ↓reduceIte]
    have II := chainDec_determined θ inner _ _ _ (fun _ => childVals u (θ a) m.c) rfl f hi (fc _)
      (fun l hl => hθ l (mI l hl))
    have IS := chainDec_determined θ rest _ _ u cont hcr f hs (flone.symm.trans hr)
      (fun l hl => hθ l (mS l hl))
    intro z hz
    simp only [RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append,
      Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl | (((h' | h') | h') | h')) | (((h' | h') | h') | h')
    · rw [hr]; simp [chainVal]
    · rw [fnb, vnb]
    · exact IR z (Or.inl h')
    · exact IG z (Or.inl h')
    · obtain ⟨r1, r2⟩ := chain_endpoints_region inner _ _ z (Finset.mem_union_left _ h')
      rw [II z (Finset.mem_union_left _ h'), (D z).2.2.2 r1 (by rwa [addrExt_append] at r2)]
    · rw [IS z (Finset.mem_union_left _ h'),
        (D z).2.2.1 (chain_endpoints_region rest _ _ z (Finset.mem_union_left _ h')).1]
    · exact IR z (Or.inr h')
    · exact IG z (Or.inr h')
    · obtain ⟨r1, r2⟩ := chain_endpoints_region inner _ _ z (Finset.mem_union_right _ h')
      rw [II z (Finset.mem_union_right _ h'), (D z).2.2.2 r1 (by rwa [addrExt_append] at r2)]
    · rw [IS z (Finset.mem_union_right _ h'),
        (D z).2.2.1 (chain_endpoints_region rest _ _ z (Finset.mem_union_right _ h')).1]
termination_by structural X
end

end WaveTurbulence.Links

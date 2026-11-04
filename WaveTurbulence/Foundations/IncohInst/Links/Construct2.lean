/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Construct

/-!
# The constructed values are decorations (packet C2)

`cplDec_cplVal`: `cplVal θ Q a b r` decorates `Q` at independent positions `(a, b)`;
`chainDec_chainVal`: `chainVal θ X ζ a u cont` decorates `X` when `cont` has the value `u` at the lone
position.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

theorem partner_cases (c : MiniCplCode) :
    (c.partner 0 = 0 ∧ c.partner 2 = 2) ∨ (c.partner 0 = 2 ∧ c.partner 2 = 0) := by
  fin_cases c <;> decide

theorem type1_dispatch (θ : Fin w × Path → V × V) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    (a b : Fin w × Path) (r : V) (h : Indep a b) (z : Fin w × Path) :
    ((Under (addrExt a [0]) z ∨ Under (addrExt b [c.partner 0]) z) →
      cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r z =
        cplVal θ Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (childVals r (θ a) 0) z) ∧
    ((Under (addrExt b [1]) z ∨ Under (addrExt a [1]) z) →
      cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r z =
        cplVal θ Q₂ (addrExt b [1]) (addrExt a [1]) (childVals r (θ a) 1) z) ∧
    ((Under (addrExt a [2]) z ∨ Under (addrExt b [c.partner 2]) z) →
      cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r z =
        cplVal θ Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (childVals r (θ a) 2) z) := by
  obtain ⟨T1, T2, T3⟩ := type1_regions (z := z) h c
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · simp only [cplVal, T1 hz, hz, ↓reduceIte]
  · simp only [cplVal, (T2 hz).1, (T2 hz).2, hz, ↓reduceIte]
  · simp only [cplVal, (T3 hz).1, (T3 hz).2.1, (T3 hz).2.2, ↓reduceIte]

theorem chain_dispatch (θ : Fin w × Path → V × V) (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner rest : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V) (cont : (Fin w × Path) → V)
    (z : Fin w × Path) :
    ((Under (addrExt a [m.red.1]) z ∨ Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) z) →
      chainVal θ (.pair m Qr Qg inner rest) ζ a u cont z =
      (if slotSign ζ m.red.1 = 1 then
        cplVal θ Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          (childVals u (θ a) m.red.1)
      else cplVal θ Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
          (childVals u (θ a) m.red.1)) z) ∧
    ((Under (addrExt a [m.green.1]) z ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) z) →
      chainVal θ (.pair m Qr Qg inner rest) ζ a u cont z =
      (if slotSign ζ m.green.1 = 1 then
        cplVal θ Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          (childVals u (θ a) m.green.1)
      else cplVal θ Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
          (childVals u (θ a) m.green.1)) z) ∧
    (Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z →
      chainVal θ (.pair m Qr Qg inner rest) ζ a u cont z =
        chainVal θ rest (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) u cont z) ∧
    (Under (addrExt a [m.c]) z → ¬ SUnder (addrExt a ([m.c] ++ inner.lonePath)) z →
      chainVal θ (.pair m Qr Qg inner rest) ζ a u cont z =
        chainVal θ inner (slotSign ζ m.c) (addrExt a [m.c]) (childVals u (θ a) m.c)
          (fun _ => childVals u (θ a) m.c) z) := by
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_, fun hz hn => ?_⟩
  · have ha : z ≠ a := by
      rcases hz with hz | hz
      · exact ne_of_under_cons _ [] hz
      · exact ne_of_under_cons m.c _ (by simpa using hz)
    simp only [chainVal, ha, hz, ↓reduceIte]
  · have ha : z ≠ a := by
      rcases hz with hz | hz
      · exact ne_of_under_cons _ [] hz
      · exact ne_of_under_cons m.c _ (by simpa using hz)
    have hr := (chain_regions (m := m) (L := inner.lonePath) (a := a)).2 hz
    simp only [chainVal, ha, hz, hr, ↓reduceIte]
  · have ha : z ≠ a := ne_of_under_cons m.c _ (by simpa using hz)
    obtain ⟨hr, hg⟩ := (chain_regions (m := m) (L := inner.lonePath) (a := a)).1 hz
    simp only [chainVal, ha, hz, hr, hg, ↓reduceIte]
  · obtain ⟨h1, h2, h3, h4⟩ := chain_inner_region hz hn
    simp only [chainVal, h1, h2, h3, h4, ↓reduceIte]

mutual
/-- **The constructed couple values form a decoration of the code.** -/
theorem cplDec_cplVal (θ : Fin w × Path → V × V) (Q : RegCpl) (a b : Fin w × Path) (r : V)
    (h : Indep a b) : CplDec (cplVal θ Q a b r) Q a b := by
  cases Q with
  | triv => simp [CplDec, cplVal]
  | type1 c Q₁ Q₂ Q₃ =>
    have i₁ : Indep (addrExt a [0]) (addrExt b [c.partner 0]) := h.ext _ _
    have i₂ : Indep (addrExt b [1]) (addrExt a [1]) := h.symm.ext _ _
    have i₃ : Indep (addrExt a [2]) (addrExt b [c.partner 2]) := h.ext _ _
    have v₁ := cplVal_root θ Q₁ _ _ (childVals r (θ a) 0) i₁
    have v₂ := cplVal_root θ Q₂ _ _ (childVals r (θ a) 1) i₂
    have v₃ := cplVal_root θ Q₃ _ _ (childVals r (θ a) 2) i₃
    have D := fun z => type1_dispatch θ c Q₁ Q₂ Q₃ a b r h z
    have ga : cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r a = r := by simp [cplVal]
    have gb : cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r b = r := by simp [cplVal]
    have ga0 := (D _).1 (Or.inl (under_refl _)); rw [v₁.1] at ga0
    have ga1 := (D _).2.1 (Or.inr (under_refl _)); rw [v₂.2] at ga1
    have ga2 := (D _).2.2 (Or.inl (under_refl _)); rw [v₃.1] at ga2
    have gb0 := (D _).1 (Or.inr (under_refl _)); rw [v₁.2] at gb0
    have gb1 := (D _).2.1 (Or.inl (under_refl _)); rw [v₂.1] at gb1
    have gb2 := (D _).2.2 (Or.inr (under_refl _)); rw [v₃.2] at gb2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold NodeRel; rw [ga, ga0, ga1, ga2]; exact childVals_rel _ _
    · unfold NodeRel
      rw [gb]
      have hr := childVals_rel r (θ a)
      rcases partner_cases c with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;> rw [h0] at gb0 <;> rw [h2] at gb2
      · rw [gb0, gb1, gb2]; exact hr
      · rw [gb0, gb1, gb2]; exact hr.trans (by abel)
    · exact cplDec_congr _ _ Q₁ _ _ (cplDec_cplVal θ Q₁ _ _ _ i₁) fun z hz => ((D z).1 hz).symm
    · exact cplDec_congr _ _ Q₂ _ _ (cplDec_cplVal θ Q₂ _ _ _ i₂) fun z hz =>
        ((D z).2.1 hz).symm
    · exact cplDec_congr _ _ Q₃ _ _ (cplDec_cplVal θ Q₃ _ _ _ i₃) fun z hz =>
        ((D z).2.2 hz).symm
  | type2 Xp Xm Qlp =>
    have iQ := h.ext Xp.lonePath Xm.lonePath
    have vQ := cplVal_root θ Qlp _ _ r iQ
    have D4 : ∀ z, Under a z → cplVal θ (.type2 Xp Xm Qlp) a b r z =
        chainVal θ Xp 1 a r (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) z :=
      fun z hz => by simp only [cplVal, hz, ↓reduceIte]
    have D5 : ∀ z, Under b z → cplVal θ (.type2 Xp Xm Qlp) a b r z =
        chainVal θ Xm (-1) b r (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) z :=
      fun z hz => by
        have : ¬ Under a z := fun ha => h.not_both ha hz
        simp only [cplVal, this, ↓reduceIte]
    refine ⟨chainDec_congr _ _ Xp 1 a (chainDec_chainVal θ Xp 1 a r _ vQ.1)
        (fun z hz _ => (D4 z hz).symm),
      chainDec_congr _ _ Xm (-1) b (chainDec_chainVal θ Xm (-1) b r _ vQ.2)
        (fun z hz _ => (D5 z hz).symm),
      cplDec_congr _ _ Qlp _ _ (cplDec_cplVal θ Qlp _ _ r iQ) fun z hz => ?_⟩
    rcases hz with hz | hz
    · rw [D4 z (under_trans (under_ext _ _) hz), chainVal_lone θ Xp 1 a r _ z hz]
    · rw [D5 z (under_trans (under_ext _ _) hz), chainVal_lone θ Xm (-1) b r _ z hz]
termination_by structural Q

/-- **The constructed chain values form a decoration of the chain code.** -/
theorem chainDec_chainVal (θ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (u : V) (cont : (Fin w × Path) → V) (hc : cont (addrExt a X.lonePath) = u) :
    ChainDec (chainVal θ X ζ a u cont) X ζ a := by
  cases X with
  | nil => trivial
  | pair m Qr Qg inner rest =>
    obtain ⟨vA, vnb, vlone, vR2, vG2⟩ := chainVal_pair_vals θ m Qr Qg inner rest ζ a u cont hc
    have D := fun z => chain_dispatch θ m Qr Qg inner rest ζ a u cont z
    have hcr : cont (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath) = u := by
      rw [← hc]; congr 1; simp [RegChain.lonePath, addrExt_append]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold NodeRel
      rw [show chainVal θ (.pair m Qr Qg inner rest) ζ a u cont a = u by simp [chainVal],
        vA 0, vA 1, vA 2]
      exact childVals_rel _ _
    · have := miniTree_consistent m u (childVals u (θ a))
        (fun i => chainVal θ (.pair m Qr Qg inner rest) ζ a u cont
          (addrExt a ([m.c] ++ inner.lonePath ++ [i])))
        (childVals_rel _ _) vlone vR2 vG2
      unfold NodeRel
      rw [vnb]
      simpa only [addrExt_append] using this
    · by_cases hs : slotSign ζ m.red.1 = 1
      · simp only [hs, ↓reduceIte]
        refine cplDec_congr _ _ Qr _ _ (cplDec_cplVal θ Qr _ _ (childVals u (θ a) m.red.1)
          (indep_red m _ a)) fun z hz => ?_
        rw [(D z).1 hz]; simp only [hs, ↓reduceIte]
      · simp only [hs, ↓reduceIte]
        refine cplDec_congr _ _ Qr _ _ (cplDec_cplVal θ Qr _ _ (childVals u (θ a) m.red.1)
          (indep_red m _ a).symm) fun z hz => ?_
        rw [(D z).1 hz.symm]; simp only [hs, ↓reduceIte]
    · by_cases hs : slotSign ζ m.green.1 = 1
      · simp only [hs, ↓reduceIte]
        refine cplDec_congr _ _ Qg _ _ (cplDec_cplVal θ Qg _ _ (childVals u (θ a) m.green.1)
          (indep_green m _ a)) fun z hz => ?_
        rw [(D z).2.1 hz]; simp only [hs, ↓reduceIte]
      · simp only [hs, ↓reduceIte]
        refine cplDec_congr _ _ Qg _ _ (cplDec_cplVal θ Qg _ _ (childVals u (θ a) m.green.1)
          (indep_green m _ a).symm) fun z hz => ?_
        rw [(D z).2.1 hz.symm]; simp only [hs, ↓reduceIte]
    · refine chainDec_congr _ _ inner _ _ (chainDec_chainVal θ inner (slotSign ζ m.c) (addrExt a [m.c])
        (childVals u (θ a) m.c) (fun _ => childVals u (θ a) m.c) rfl) fun z hz hn => ?_
      rw [(D z).2.2.2 hz (by rwa [addrExt_append] at hn)]
    · refine chainDec_congr _ _ rest _ _ (chainDec_chainVal θ rest _ _ u cont hcr)
        fun z hz _ => ?_
      rw [(D z).2.2.1 hz]
termination_by structural X
end

end WaveTurbulence.Links

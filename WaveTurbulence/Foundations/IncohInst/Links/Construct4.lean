/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Construct3

/-!
# Link parameters of the constructed decoration (packet C2)

* `cplVal_params`: any `f` agreeing with `cplVal θ Q a b r` below `a` and `b` has parameters
  `x_𝔫 = (θ 𝔫).1`, `y_𝔫 = (θ 𝔫).2` at every chosen node `𝔫` of `Q`.
* `cplDec_determined`: a decoration with root value `r` and these parameters agrees with
  `cplVal θ Q a b r` at every node of the code.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

theorem lone_sunder_nb (m : MiniTreeCode) (L R : Path) (a y : Fin w × Path)
    (hy : SUnder (addrExt (addrExt a ([m.c] ++ L ++ [m.lone])) R) y) :
    SUnder (addrExt (addrExt a [m.c]) L) y := by
  have e : addrExt (addrExt a ([m.c] ++ L ++ [m.lone])) R =
      addrExt (addrExt (addrExt a [m.c]) L) (m.lone :: R) := by
    simp [addrExt_append]
  rw [e] at hy
  exact sunder_of_sunder_ext _ hy

theorem red_not_lone (m : MiniTreeCode) (L R : Path) (a y : Fin w × Path)
    (hy : Under (addrExt a [m.red.1]) y ∨ Under (addrExt a ([m.c] ++ L ++ [m.red.2])) y) :
    ¬ SUnder (addrExt (addrExt a ([m.c] ++ L ++ [m.lone])) R) y := fun hs =>
  ((chain_regions (m := m) (L := L) (a := a)).1 (under_trans (under_ext _ _) hs.1)).1 hy

theorem green_not_lone (m : MiniTreeCode) (L R : Path) (a y : Fin w × Path)
    (hy : Under (addrExt a [m.green.1]) y ∨ Under (addrExt a ([m.c] ++ L ++ [m.green.2])) y) :
    ¬ SUnder (addrExt (addrExt a ([m.c] ++ L ++ [m.lone])) R) y := fun hs =>
  ((chain_regions (m := m) (L := L) (a := a)).1 (under_trans (under_ext _ _) hs.1)).2 hy

theorem chain_lonePath_eq (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain)
    (a : Fin w × Path) :
    addrExt a (RegChain.pair m Qr Qg inner rest).lonePath =
      addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath := by
  simp [RegChain.lonePath, addrExt_append]

theorem childVals_x (u : V) (θ : V × V) : childVals u θ 0 - u = θ.1 := by
  simp [childVals]

theorem childVals_y (u : V) (θ : V × V) : u - childVals u θ 2 = θ.2 := by
  simp [childVals]

mutual
/-- **The parameters of the constructed decoration are `θ`.** -/
theorem cplVal_params (θ : Fin w × Path → V × V) (Q : RegCpl) (a b : Fin w × Path) (r : V)
    (h : Indep a b) (f : Fin w × Path → V)
    (hf : ∀ z, Under a z ∨ Under b z → f z = cplVal θ Q a b r z) :
    ∀ l ∈ Q.linksAt a b, xv f l.1 = (θ l.1).1 ∧ yv f l.1 = (θ l.1).2 := by
  cases Q with
  | triv => simp [RegCpl.linksAt]
  | type1 c Q₁ Q₂ Q₃ =>
    have D := fun z => type1_dispatch θ c Q₁ Q₂ Q₃ a b r h z
    intro l hl
    simp only [RegCpl.linksAt, List.mem_cons, List.mem_append] at hl
    rcases hl with rfl | ((hl | hl) | hl)
    · have fa : f a = r := (hf a (Or.inl (under_refl a))).trans (by simp [cplVal])
      have fa0 : f (addrExt a [0]) = childVals r (θ a) 0 :=
        (hf _ (Or.inl (under_ext _ _))).trans (((D _).1 (Or.inl (under_refl _))).trans
          (cplVal_root θ Q₁ _ _ _ (h.ext _ _)).1)
      have fa2 : f (addrExt a [2]) = childVals r (θ a) 2 :=
        (hf _ (Or.inl (under_ext _ _))).trans (((D _).2.2 (Or.inl (under_refl _))).trans
          (cplVal_root θ Q₃ _ _ _ (h.ext _ _)).1)
      simp only [xv, yv, fa, fa0, fa2]
      exact ⟨childVals_x _ _, childVals_y _ _⟩
    · exact cplVal_params θ Q₁ _ _ _ (h.ext _ _) f (fun z hz => (hf z (hz.imp
        (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))).trans ((D z).1 hz)) l hl
    · exact cplVal_params θ Q₂ _ _ _ (h.symm.ext _ _) f (fun z hz => (hf z (hz.symm.imp
        (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))).trans ((D z).2.1 hz)) l hl
    · exact cplVal_params θ Q₃ _ _ _ (h.ext _ _) f (fun z hz => (hf z (hz.imp
        (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))).trans ((D z).2.2 hz)) l hl
  | type2 Xp Xm Qlp =>
    have iQ := h.ext Xp.lonePath Xm.lonePath
    have vQ := cplVal_root θ Qlp _ _ r iQ
    intro l hl
    simp only [RegCpl.linksAt, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · refine chainVal_params θ Xp 1 a r _ vQ.1 f (fun z hz _ => ?_) l hl
      rw [hf z (Or.inl hz)]; simp only [cplVal, hz, ↓reduceIte]
    · refine chainVal_params θ Xm (-1) b r _ vQ.2 f (fun z hz _ => ?_) l hl
      have : ¬ Under a z := fun ha => h.not_both ha hz
      rw [hf z (Or.inr hz)]; simp only [cplVal, this, ↓reduceIte]
    · refine cplVal_params θ Qlp _ _ r iQ f (fun z hz => ?_) l hl
      rcases hz with hz | hz
      · have ha : Under a z := under_trans (under_ext _ _) hz
        rw [hf z (Or.inl ha)]; simp only [cplVal, ha, ↓reduceIte]
        exact chainVal_lone θ Xp 1 a r _ z hz
      · have hb : Under b z := under_trans (under_ext _ _) hz
        have : ¬ Under a z := fun ha => h.not_both ha hb
        rw [hf z (Or.inr hb)]; simp only [cplVal, this, ↓reduceIte]
        exact chainVal_lone θ Xm (-1) b r _ z hz
termination_by structural Q

/-- Chain version of `cplVal_params`. -/
theorem chainVal_params (θ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (u : V) (cont : (Fin w × Path) → V) (hc : cont (addrExt a X.lonePath) = u)
    (f : Fin w × Path → V)
    (hf : ∀ z, Under a z → ¬ SUnder (addrExt a X.lonePath) z → f z = chainVal θ X ζ a u cont z) :
    ∀ l ∈ X.linksAt ζ a, xv f l.1 = (θ l.1).1 ∧ yv f l.1 = (θ l.1).2 := by
  cases X with
  | nil => simp [RegChain.linksAt]
  | pair m Qr Qg inner rest =>
    obtain ⟨vA, -, -, -, -⟩ := chainVal_pair_vals θ m Qr Qg inner rest ζ a u cont hc
    have D := fun z => chain_dispatch θ m Qr Qg inner rest ζ a u cont z
    rw [chain_lonePath_eq] at hf hc
    have hlen : (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath).2.length =
        a.2.length + inner.lonePath.length + rest.lonePath.length + 2 := by
      simp [addrExt]; omega
    intro l hl
    simp only [RegChain.linksAt, List.mem_cons, List.mem_append] at hl
    rcases hl with rfl | (((hl | hl) | hl) | hl)
    · have fa : f a = u :=
        (hf a (under_refl a) (not_sunder_of_length (by rw [hlen]; omega))).trans
          (by simp [chainVal])
      have fai : ∀ i, f (addrExt a [i]) = childVals u (θ a) i := fun i =>
        (hf _ (under_ext _ _) (not_sunder_of_length (by rw [hlen]; simp [addrExt]; omega))).trans
          (vA i)
      simp only [xv, yv, fa, fai]
      exact ⟨childVals_x _ _, childVals_y _ _⟩
    · have hreg := fun z (hz : Under (addrExt a [m.red.1]) z ∨
          Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) z) =>
        (hf z (by rcases hz with hz | hz <;> exact under_trans (under_ext _ _) hz)
          (red_not_lone m _ _ a z hz)).trans ((D z).1 hz)
      by_cases hs : slotSign ζ m.red.1 = 1 <;> simp only [hs, ↓reduceIte] at hl hreg
      · exact cplVal_params θ Qr _ _ _ (indep_red m _ a) f hreg l hl
      · exact cplVal_params θ Qr _ _ _ (indep_red m _ a).symm f (fun z hz => hreg z hz.symm) l hl
    · have hreg := fun z (hz : Under (addrExt a [m.green.1]) z ∨
          Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) z) =>
        (hf z (by rcases hz with hz | hz <;> exact under_trans (under_ext _ _) hz)
          (green_not_lone m _ _ a z hz)).trans ((D z).2.1 hz)
      by_cases hs : slotSign ζ m.green.1 = 1 <;> simp only [hs, ↓reduceIte] at hl hreg
      · exact cplVal_params θ Qg _ _ _ (indep_green m _ a) f hreg l hl
      · exact cplVal_params θ Qg _ _ _ (indep_green m _ a).symm f (fun z hz => hreg z hz.symm) l hl
    · refine chainVal_params θ inner _ _ _ (fun _ => childVals u (θ a) m.c) rfl f
        (fun z hz hn => ?_) l hl
      rw [hf z (under_trans (under_ext _ _) hz) (fun hs => hn (lone_sunder_nb m _ _ a z hs))]
      exact (D z).2.2.2 hz (by rwa [addrExt_append] at hn)
    · refine chainVal_params θ rest _ _ u cont hc f (fun z hz hn => ?_) l hl
      rw [hf z (under_trans (under_ext _ _) hz) hn]
      exact (D z).2.2.1 hz
termination_by structural X
end

end WaveTurbulence.Links

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Construct2
public import WaveTurbulence.Foundations.IncohInst.Links.Partition

/-!
# Link parameters determine decorations (packet C2)

* `cplVal_params`: the constructed decoration has parameters `θ` at every chosen node;
* `cplDec_determined`: a decoration with root value `r` and parameters `θ` at the chosen nodes equals
  `cplVal θ Q a b r` at every node of the code (link endpoints and leaf-pair endpoints).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-! ### Endpoints lie in the region of the code -/

mutual
theorem cpl_endpoints_under (Q : RegCpl) (a b : Fin w × Path) :
    ∀ z ∈ pairEndpoints (Q.linksAt a b) ∪ pairEndpoints (Q.pairsAt a b), Under a z ∨ Under b z := by
  cases Q with
  | triv =>
    intro z hz
    simp only [RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_nil, pairEndpoints_singleton,
      Finset.empty_union, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Or.inl (under_refl _)
    · exact Or.inr (under_refl _)
  | type1 c Q₁ Q₂ Q₃ =>
    intro z hz
    simp only [RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_cons, pairEndpoints_append,
      Finset.mem_union, Finset.mem_singleton] at hz
    have H₁ := fun z (h : z ∈ pairEndpoints (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])) ∪
        pairEndpoints (Q₁.pairsAt (addrExt a [0]) (addrExt b [c.partner 0]))) =>
      (cpl_endpoints_under Q₁ _ _ z h).imp (under_trans (under_ext a [0]))
        (under_trans (under_ext b [c.partner 0]))
    have H₂ := fun z (h : z ∈ pairEndpoints (Q₂.linksAt (addrExt b [1]) (addrExt a [1])) ∪
        pairEndpoints (Q₂.pairsAt (addrExt b [1]) (addrExt a [1]))) =>
      (cpl_endpoints_under Q₂ _ _ z h).symm.imp (under_trans (under_ext a [1]))
        (under_trans (under_ext b [1]))
    have H₃ := fun z (h : z ∈ pairEndpoints (Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])) ∪
        pairEndpoints (Q₃.pairsAt (addrExt a [2]) (addrExt b [c.partner 2]))) =>
      (cpl_endpoints_under Q₃ _ _ z h).imp (under_trans (under_ext a [2]))
        (under_trans (under_ext b [c.partner 2]))
    rcases hz with (rfl | rfl | ((h | h) | h)) | ((h | h) | h)
    · exact Or.inl (under_refl _)
    · exact Or.inr (under_refl _)
    · exact H₁ z (Finset.mem_union_left _ h)
    · exact H₂ z (Finset.mem_union_left _ h)
    · exact H₃ z (Finset.mem_union_left _ h)
    · exact H₁ z (Finset.mem_union_right _ h)
    · exact H₂ z (Finset.mem_union_right _ h)
    · exact H₃ z (Finset.mem_union_right _ h)
  | type2 Xp Xm Qlp =>
    intro z hz
    simp only [RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_append, Finset.mem_union] at hz
    have HQ := fun z (h : z ∈ pairEndpoints (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)) ∪
        pairEndpoints (Qlp.pairsAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))) =>
      (cpl_endpoints_under Qlp _ _ z h).imp (under_trans (under_ext a _)) (under_trans (under_ext b _))
    rcases hz with ((h | h) | h) | ((h | h) | h)
    · exact Or.inl (chain_endpoints_region Xp 1 a z (Finset.mem_union_left _ h)).1
    · exact Or.inr (chain_endpoints_region Xm (-1) b z (Finset.mem_union_left _ h)).1
    · exact HQ z (Finset.mem_union_left _ h)
    · exact Or.inl (chain_endpoints_region Xp 1 a z (Finset.mem_union_right _ h)).1
    · exact Or.inr (chain_endpoints_region Xm (-1) b z (Finset.mem_union_right _ h)).1
    · exact HQ z (Finset.mem_union_right _ h)
termination_by structural Q

theorem chain_endpoints_region (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    ∀ z ∈ pairEndpoints (X.linksAt ζ a) ∪ pairEndpoints (X.pairsAt ζ a),
      Under a z ∧ ¬ SUnder (addrExt a X.lonePath) z := by
  cases X with
  | nil => simp [RegChain.linksAt, RegChain.pairsAt]
  | pair m Qr Qg inner rest =>
    intro z hz
    have hlp : addrExt a (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath := by
      simp [RegChain.lonePath, addrExt_append]
    rw [hlp]
    have lone_below_nb : ∀ y, SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
        rest.lonePath) y → SUnder (addrExt (addrExt a [m.c]) inner.lonePath) y := fun y hy => by
      have e : addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath =
          addrExt (addrExt (addrExt a [m.c]) inner.lonePath) (m.lone :: rest.lonePath) := by
        simp [addrExt_append]
      rw [e] at hy
      exact sunder_of_sunder_ext _ hy
    have notlone_of_red : ∀ y, (Under (addrExt a [m.red.1]) y ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) y) →
        ¬ SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath) y :=
      fun y hy hs => ((chain_regions (m := m) (L := inner.lonePath) (a := a)).1
        (under_trans (under_ext _ _) hs.1)).1 hy
    have notlone_of_green : ∀ y, (Under (addrExt a [m.green.1]) y ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) y) →
        ¬ SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath) y :=
      fun y hy hs => ((chain_regions (m := m) (L := inner.lonePath) (a := a)).1
        (under_trans (under_ext _ _) hs.1)).2 hy
    have hlenX : (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath).2.length =
        a.2.length + inner.lonePath.length + rest.lonePath.length + 2 := by
      simp [addrExt]; omega
    have HR : ∀ z, (z ∈ pairEndpoints (if slotSign ζ m.red.1 = 1 then
          Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∨
        z ∈ pairEndpoints (if slotSign ζ m.red.1 = 1 then
          Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))) →
        Under a z ∧ ¬ SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
          rest.lonePath) z := fun z h => by
      have hr : Under (addrExt a [m.red.1]) z ∨
          Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) z := by
        split_ifs at h with hs
        · exact cpl_endpoints_under Qr _ _ z (Finset.mem_union.2 h)
        · exact (cpl_endpoints_under Qr _ _ z (Finset.mem_union.2 h)).symm
      exact ⟨by rcases hr with hr | hr <;> exact under_trans (under_ext _ _) hr,
        notlone_of_red z hr⟩
    have HG : ∀ z, (z ∈ pairEndpoints (if slotSign ζ m.green.1 = 1 then
          Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∨
        z ∈ pairEndpoints (if slotSign ζ m.green.1 = 1 then
          Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))) →
        Under a z ∧ ¬ SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
          rest.lonePath) z := fun z h => by
      have hg : Under (addrExt a [m.green.1]) z ∨
          Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) z := by
        split_ifs at h with hs
        · exact cpl_endpoints_under Qg _ _ z (Finset.mem_union.2 h)
        · exact (cpl_endpoints_under Qg _ _ z (Finset.mem_union.2 h)).symm
      exact ⟨by rcases hg with hg | hg <;> exact under_trans (under_ext _ _) hg,
        notlone_of_green z hg⟩
    have HI : ∀ z, z ∈ pairEndpoints (inner.linksAt (slotSign ζ m.c) (addrExt a [m.c])) ∪
        pairEndpoints (inner.pairsAt (slotSign ζ m.c) (addrExt a [m.c])) →
        Under a z ∧ ¬ SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
          rest.lonePath) z := fun z h => by
      obtain ⟨h1, h2⟩ := chain_endpoints_region inner _ _ z h
      exact ⟨under_trans (under_ext _ _) h1, fun hs => h2 (lone_below_nb z hs)⟩
    have HS : ∀ z, z ∈ pairEndpoints (rest.linksAt (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))) ∪
        pairEndpoints (rest.pairsAt (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))) →
        Under a z ∧ ¬ SUnder (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
          rest.lonePath) z := fun z h => by
      obtain ⟨h1, h2⟩ := chain_endpoints_region rest _ _ z h
      exact ⟨under_trans (under_ext _ _) h1, h2⟩
    simp only [RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append,
      Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl | (((h | h) | h) | h)) | (((h | h) | h) | h)
    · exact ⟨under_refl _, not_sunder_of_length (by rw [hlenX]; omega)⟩
    · exact ⟨under_ext _ _, not_sunder_of_length (by rw [hlenX]; simp [addrExt]; omega)⟩
    · exact HR z (Or.inl h)
    · exact HG z (Or.inl h)
    · exact HI z (Finset.mem_union_left _ h)
    · exact HS z (Finset.mem_union_left _ h)
    · exact HR z (Or.inr h)
    · exact HG z (Or.inr h)
    · exact HI z (Finset.mem_union_right _ h)
    · exact HS z (Finset.mem_union_right _ h)
termination_by structural X
end

end WaveTurbulence.Links

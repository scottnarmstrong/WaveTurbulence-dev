/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceGraftClosure

/-! # Replacing all original template leaf pairs by actual regular couples -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- An actual oriented template leaf pair together with its inserted couple code. -/
abbrev CoupleDecoration := ((Fin 2 × Path) × (Fin 2 × Path)) × RegCpl

/-- The literal pair blocks emitted by source-ordered template decorations. -/
def decorationPairs (E : List CoupleDecoration) : List ((Fin 2 × Path) × (Fin 2 × Path)) :=
  E.flatMap (fun e => e.2.pairsAt e.1.1 e.1.2)

/-- Sequential actual source grafts replace every listed original template slot.
The remaining original pairs are put first before each erase, so permutation
transport retains the exact multiplicity even if an inserted couple is trivial. -/
theorem exists_regular_decoration_grafts (E : List CoupleDecoration) (Q : RegCpl)
    (R : List ((Fin 2 × Path) × (Fin 2 × Path))) (hQ : IsRegularCouple (decodedCouple Q))
    (hp : Q.raw.2.Perm (E.map Prod.fst ++ R))
    (hE : ∀ e ∈ E, IsRegularCouple (decodedCouple e.2)) :
    ∃ D : RegCpl, IsRegularCouple (decodedCouple D) ∧ D.raw.2.Perm (R ++ decorationPairs E) := by
  induction E generalizing Q R with
  | nil => exact ⟨Q,hQ,by simpa only [List.map_nil,List.nil_append,decorationPairs,List.flatMap_nil,List.append_nil] using hp⟩
  | cons e E ih =>
    have hpair : e.1 ∈ Q.raw.2 := hp.mem_iff.mpr (by simp)
    have hnew := isRegularCouple_graft Q e.2 hQ (hE e (by exact List.mem_cons_self)) e.1.1 e.1.2 hpair
    have hframes : (graftCouple Q e.1.1 e.1.2 e.2).raw.2.Perm
        (E.map Prod.fst ++ (R ++ e.2.pairsAt e.1.1 e.1.2)) := by
      have hh := (hp.erase e.1).append_right (e.2.pairsAt e.1.1 e.1.2)
      simp only [List.map_cons,List.cons_append,List.erase_cons_head,List.append_assoc] at hh
      exact (graftCouple_pairs_perm Q e.1.1 e.1.2 e.2 hpair).trans hh
    obtain ⟨D,hD,hpairs⟩ := ih (graftCouple Q e.1.1 e.1.2 e.2) (R ++ e.2.pairsAt e.1.1 e.1.2)
      hnew hframes (fun e he => hE e (List.mem_cons_of_mem _ he))
    exact ⟨D,hD,by simpa only [decorationPairs,List.flatMap_cons,List.append_assoc] using hpairs⟩

/-- An actual regular outer template and actual regular inserted couples produce a regular carrier.
The two list identities are literal constructor computations, supplied by each
outer-code constructor in the reverse-range proof. -/
theorem isRegularCouple_of_decorated_template (Q C : RegCpl) (E : List CoupleDecoration)
    (hQ : IsRegularCouple (decodedCouple Q)) (hframes : Q.raw.2.Perm (E.map Prod.fst))
    (hpairs : C.raw.2 = decorationPairs E)
    (hE : ∀ e ∈ E, IsRegularCouple (decodedCouple e.2)) : IsRegularCouple (decodedCouple C) := by
  have hframes' : Q.raw.2.Perm (E.map Prod.fst ++ []) := by simpa only [List.append_nil] using hframes
  obtain ⟨D,hD,hpairsD⟩ := exists_regular_decoration_grafts E Q [] hQ hframes' hE
  have he : decodedCouple D = decodedCouple C := by
    apply decodedCouple_eq_of_rawPairs_perm
    simpa only [List.nil_append,← hpairs] using hpairsD
  rw [← he]
  exact hD

end WaveTurbulence.Reg

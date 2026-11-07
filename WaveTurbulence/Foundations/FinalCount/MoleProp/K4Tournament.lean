/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleGraphRank
import Mathlib.Tactic

/-! # Canonical balanced orientation of the actual terminal K4 -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- The six independent orientations of a loop-free complete four-atom graph. -/
def tournamentFromBits (b : Fin 6 → Bool) : Fin 4 → Fin 4 → Bool :=
  ![![false,b 0,b 1,b 2],![!b 0,false,b 3,b 4],
    ![!b 1,!b 3,false,b 5],![!b 2,!b 4,!b 5,false]]

/-- Each atom has at most two outgoing and two incoming bonds. -/
def BalancedTournament (b : Fin 6 → Bool) : Prop :=
  ∀ i : Fin 4, (univ.filter (fun j => tournamentFromBits b i j = true)).card ≤ 2 ∧
    (univ.filter (fun j => tournamentFromBits b j i = true)).card ≤ 2

instance (b : Fin 6 → Bool) : Decidable (BalancedTournament b) := by
  unfold BalancedTournament
  infer_instance

/-- Canonical orientation matching the three momentum tuples in K4CountAlgebra. -/
def canonicalK4 : Fin 4 → Fin 4 → Bool :=
  tournamentFromBits ![true,true,false,true,true,true]

private theorem classify_000 (d e f : Bool) (hb : BalancedTournament ![false,false,false,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![false,false,false,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,false,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,false,false,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,false,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,false,true,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,true,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,true,false,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,true,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,false,true,true,true]) hb)

private theorem classify_001 (d e f : Bool) (hb : BalancedTournament ![false,false,true,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![false,false,true,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · refine ⟨Equiv.ofBijective (![3,2,1,0] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,true,false,false,true]) hb)
  · refine ⟨Equiv.ofBijective (![2,1,0,3] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,true,false,true,true]) hb)
  · refine ⟨Equiv.ofBijective (![3,1,2,0] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,2,0,3] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,true,true,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,false,true,true,true,true]) hb)

private theorem classify_010 (d e f : Bool) (hb : BalancedTournament ![false,true,false,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![false,true,false,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,false,false,false,false]) hb)
  · refine ⟨Equiv.ofBijective (![2,3,1,0] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,3,0,2] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,1,3,0] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,false,true,false,false]) hb)
  · refine ⟨Equiv.ofBijective (![3,1,0,2] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,false,true,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,false,true,true,true]) hb)

private theorem classify_011 (d e f : Bool) (hb : BalancedTournament ![false,true,true,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![false,true,true,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · refine ⟨Equiv.ofBijective (![0,3,2,1] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,2,3,1] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,3,2] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,true,false,true,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,true,true,false,false]) hb)
  · refine ⟨Equiv.ofBijective (![1,0,2,3] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,true,true,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![false,true,true,true,true,true]) hb)

private theorem classify_100 (d e f : Bool) (hb : BalancedTournament ![true,false,false,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![true,false,false,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,false,false,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,false,false,false,true]) hb)
  · refine ⟨Equiv.ofBijective (![3,2,0,1] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,false,false,true,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,false,true,false,false]) hb)
  · refine ⟨Equiv.ofBijective (![2,3,0,1] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,3,2,0] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,2,3,0] : Fin 4 → Fin 4) (by decide),?_⟩
    decide

private theorem classify_101 (d e f : Bool) (hb : BalancedTournament ![true,false,true,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![true,false,true,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,true,false,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,true,false,false,true]) hb)
  · refine ⟨Equiv.ofBijective (![2,0,1,3] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,true,false,true,true]) hb)
  · refine ⟨Equiv.ofBijective (![0,3,1,2] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,3,1] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,3,2] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,false,true,true,true,true]) hb)

private theorem classify_110 (d e f : Bool) (hb : BalancedTournament ![true,true,false,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![true,true,false,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,false,false,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,false,false,false,true]) hb)
  · refine ⟨Equiv.ofBijective (![3,0,2,1] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,2,1,3] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,false,true,false,false]) hb)
  · refine ⟨Equiv.ofBijective (![3,0,1,2] : Fin 4 → Fin 4) (by decide),?_⟩
    decide
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,false,true,true,false]) hb)
  · refine ⟨Equiv.ofBijective (![0,1,2,3] : Fin 4 → Fin 4) (by decide),?_⟩
    decide

private theorem classify_111 (d e f : Bool) (hb : BalancedTournament ![true,true,true,d,e,f]) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits ![true,true,true,d,e,f] (p i) (p j) = canonicalK4 i j := by
  classical
  cases d <;> cases e <;> cases f
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,false,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,false,false,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,false,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,false,true,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,true,false,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,true,false,true]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,true,true,false]) hb)
  · exact False.elim ((by decide : ¬ BalancedTournament ![true,true,true,true,true,true]) hb)

/-- Every balanced four-atom tournament is isomorphic to the canonical
source orientation. The finite classification is proved by kernel reduction. -/
theorem balancedTournament_equiv_canonical (b : Fin 6 → Bool) (hb : BalancedTournament b) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, tournamentFromBits b (p i) (p j) = canonicalK4 i j := by
  have he : b = ![b 0,b 1,b 2,b 3,b 4,b 5] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hb ⊢
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2
  all_goals simp only [h0,h1,h2] at hb ⊢
  · exact classify_000 _ _ _ hb
  · exact classify_001 _ _ _ hb
  · exact classify_010 _ _ _ hb
  · exact classify_011 _ _ _ hb
  · exact classify_100 _ _ _ hb
  · exact classify_101 _ _ _ hb
  · exact classify_110 _ _ _ hb
  · exact classify_111 _ _ _ hb

/-- Source bond numbers 1,...,6 have these canonical initial atoms. -/
def k4BondStart : Fin 6 → Fin 4 := ![3,0,1,0,1,2]
/-- Source bond numbers 1,...,6 have these canonical terminal atoms. -/
def k4BondEnd : Fin 6 → Fin 4 := ![0,1,2,2,3,3]

theorem canonicalK4_bond (r : Fin 6) : canonicalK4 (k4BondStart r) (k4BondEnd r) = true := by
  fin_cases r <;> decide

theorem k4Bond_endpoints_injective : Function.Injective (fun r => (k4BondStart r,k4BondEnd r)) := by
  decide


private theorem tournamentFromBits_diag (b : Fin 6 → Bool) (i : Fin 4) :
    tournamentFromBits b i i = false := by
  fin_cases i <;> rfl

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Realized oriented edges inject each neighbor set into the actual
outgoing or incoming half-edges, so the molecule degree bounds imply balance. -/
theorem balancedTournament_of_oriented_edges (M : Molecule V D) (hM : M.IsMolecule)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 → Bool)
    (hedge : ∀ i j : Fin 4, i ≠ j → ∃ x : D, M.atom x = (e i).val ∧
      M.atom (M.mate x) = (e j).val ∧ M.out x = tournamentFromBits b i j) :
    BalancedTournament b := by
  classical
  intro i
  constructor
  · let J := {j : Fin 4 // tournamentFromBits b i j = true}
    have hex (j : J) : ∃ x : D, M.atom x = (e i).val ∧
        M.atom (M.mate x) = (e j.val).val ∧ M.out x = true := by
      have hne : i ≠ j.val := by
        intro h
        have hh := j.property
        rw [← h,tournamentFromBits_diag] at hh
        cases hh
      obtain ⟨x,hx,hxm,ho⟩ := hedge i j.val hne
      exact ⟨x,hx,hxm,ho.trans j.property⟩
    choose x hx using hex
    let O := (M.dartsAt (e i).val).filter (fun x => M.out x = true)
    let f : J → {x // x ∈ O} := fun j => ⟨x j,mem_filter.mpr
      ⟨(Mole.mem_dartsAt M _ _).mpr (hx j).1,(hx j).2.2⟩⟩
    have hinj : Function.Injective f := by
      intro j k h
      have hxx : x j = x k := congrArg Subtype.val h
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      exact (hx j).2.1.symm.trans ((congrArg (fun a => M.atom (M.mate a)) hxx).trans (hx k).2.1)
    have hc := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_coe O] at hc
    have hc' : (univ.filter (fun j => tournamentFromBits b i j = true)).card ≤ M.outdeg (e i).val := by
      simpa only [J,O,Molecule.outdeg,Fintype.card_subtype] using hc
    exact hc'.trans (hM.1 _ (e i).property).1
  · let J := {j : Fin 4 // tournamentFromBits b j i = true}
    have hex (j : J) : ∃ x : D, M.atom x = (e j.val).val ∧
        M.atom (M.mate x) = (e i).val ∧ M.out x = true := by
      have hne : j.val ≠ i := by
        intro h
        have hh := j.property
        rw [h,tournamentFromBits_diag] at hh
        cases hh
      obtain ⟨x,hx,hxm,ho⟩ := hedge j.val i hne
      exact ⟨x,hx,hxm,ho.trans j.property⟩
    choose x hx using hex
    let O := (M.dartsAt (e i).val).filter (fun x => M.out x = false)
    let f : J → {x // x ∈ O} := fun j => ⟨M.mate (x j),mem_filter.mpr
      ⟨(Mole.mem_dartsAt M _ _).mpr (hx j).2.1,by rw [M.out_mate,(hx j).2.2]; rfl⟩⟩
    have hinj : Function.Injective f := by
      intro j k h
      have hxx : M.mate (x j) = M.mate (x k) := congrArg Subtype.val h
      have heq := Mole.mate_injective M hxx
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      exact (hx j).1.symm.trans ((congrArg M.atom heq).trans (hx k).1)
    have hc := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_coe O] at hc
    have hc' : (univ.filter (fun j => tournamentFromBits b j i = true)).card ≤ M.indeg (e i).val := by
      simpa only [J,O,Molecule.indeg,Fintype.card_subtype] using hc
    exact hc'.trans (hM.1 _ (e i).property).2

/-- A concrete complete four-atom graph admits six independent oriented
bits; each ordered edge is realized by an actual half-edge. -/
theorem exists_realized_tournament_bits (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms})
    (hcomplete : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.Adj a b) :
    ∃ b : Fin 6 → Bool, ∀ i j : Fin 4, i ≠ j → ∃ x : D,
      M.atom x = (e i).val ∧ M.atom (M.mate x) = (e j).val ∧
        M.out x = tournamentFromBits b i j := by
  classical
  let lo : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
  let hi : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
  have hne (r : Fin 6) : lo r ≠ hi r := by fin_cases r <;> decide
  have hex (r : Fin 6) : ∃ x : D, M.atom x = (e (lo r)).val ∧ M.atom (M.mate x) = (e (hi r)).val := by
    apply hcomplete _ (e (lo r)).property _ (e (hi r)).property
    intro hh
    exact hne r (e.injective (Subtype.ext hh))
  choose x hx using hex
  let b := fun r => M.out (x r)
  refine ⟨b,?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨x 0,(hx 0).1,(hx 0).2,rfl⟩
  · exact ⟨x 1,(hx 1).1,(hx 1).2,rfl⟩
  · exact ⟨x 2,(hx 2).1,(hx 2).2,rfl⟩
  · exact ⟨M.mate (x 0),(hx 0).2,by rw [M.mate_mate]; exact (hx 0).1,M.out_mate (x 0)⟩
  · exact False.elim (hij rfl)
  · exact ⟨x 3,(hx 3).1,(hx 3).2,rfl⟩
  · exact ⟨x 4,(hx 4).1,(hx 4).2,rfl⟩
  · exact ⟨M.mate (x 1),(hx 1).2,by rw [M.mate_mate]; exact (hx 1).1,M.out_mate (x 1)⟩
  · exact ⟨M.mate (x 3),(hx 3).2,by rw [M.mate_mate]; exact (hx 3).1,M.out_mate (x 3)⟩
  · exact False.elim (hij rfl)
  · exact ⟨x 5,(hx 5).1,(hx 5).2,rfl⟩
  · exact ⟨M.mate (x 2),(hx 2).2,by rw [M.mate_mate]; exact (hx 2).1,M.out_mate (x 2)⟩
  · exact ⟨M.mate (x 4),(hx 4).2,by rw [M.mate_mate]; exact (hx 4).1,M.out_mate (x 4)⟩
  · exact ⟨M.mate (x 5),(hx 5).2,by rw [M.mate_mate]; exact (hx 5).1,M.out_mate (x 5)⟩
  · exact False.elim (hij rfl)


/-- Explicit atom and outgoing-bond bijections transport an actual complete
four-atom degree-three molecule to the canonical source K4 numbering. -/
theorem exists_canonical_K4_enumeration_of_complete (M : Molecule V D) (hM : M.IsMolecule)
    (hcard : M.atoms.card = 4) (hdeg : ∀ a ∈ M.atoms, M.deg a = 3)
    (hcomplete : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.Adj a b) :
    ∃ (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds}),
      ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
        M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val := by
  classical
  let e : Fin 4 ≃ {a // a ∈ M.atoms} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,hcard])).symm
  obtain ⟨bits,hedge⟩ := exists_realized_tournament_bits M e hcomplete
  have hbal := balancedTournament_of_oriented_edges M hM e bits hedge
  obtain ⟨p,hp⟩ := balancedTournament_equiv_canonical bits hbal
  let eC := p.trans e
  have hex (r : Fin 6) : ∃ x : D, M.atom x = (eC (k4BondStart r)).val ∧
      M.atom (M.mate x) = (eC (k4BondEnd r)).val ∧ M.out x = true := by
    have hne : k4BondStart r ≠ k4BondEnd r := by fin_cases r <;> decide
    obtain ⟨x,hx,hxm,ho⟩ := hedge (p (k4BondStart r)) (p (k4BondEnd r))
      (fun he => hne (p.injective he))
    exact ⟨x,hx,hxm,ho.trans ((hp _ _).trans (canonicalK4_bond r))⟩
  choose x hx using hex
  let f : Fin 6 → {x // x ∈ M.bonds} := fun r =>
    ⟨x r,mem_filter.mpr ⟨mem_univ _,(hx r).2.2⟩⟩
  have hinj : Function.Injective f := by
    intro r s h
    have he : x r = x s := congrArg Subtype.val h
    have hs : (eC (k4BondStart r)).val = (eC (k4BondStart s)).val :=
      (hx r).1.symm.trans ((congrArg M.atom he).trans (hx s).1)
    have ht : (eC (k4BondEnd r)).val = (eC (k4BondEnd s)).val :=
      (hx r).2.1.symm.trans ((congrArg (fun x => M.atom (M.mate x)) he).trans (hx s).2.1)
    exact k4Bond_endpoints_injective (Prod.ext (eC.injective (Subtype.ext hs))
      (eC.injective (Subtype.ext ht)))
  have hsum : (∑ a ∈ M.atoms, M.deg a) = 3 * M.atoms.card := by
    calc
      _ = ∑ _a ∈ M.atoms, (3 : ℕ) := sum_congr rfl hdeg
      _ = _ := by simp [mul_comm]
  have hhand := Mole.sum_degrees_eq_two_mul_bonds M
  have hbondcard : M.bonds.card = 6 := by rw [hsum,hcard] at hhand; omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj,by rw [Fintype.card_fin,Fintype.card_coe,hbondcard]⟩
  exact ⟨eC,Equiv.ofBijective f hbij,fun r => ⟨(hx r).1,(hx r).2.1⟩⟩

/-- The terminal rank-three simple molecule has the literal canonical
six-bond numbering used by K4CountAlgebra; all graph counts are derived. -/
theorem exists_canonical_K4_enumeration_of_simple_rank_three (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hne : M.atoms.Nonempty) (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hrank : M.circuitRank = 3) :
    ∃ (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds}),
      ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
        M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val := by
  obtain ⟨hc,hd,he⟩ := complete_of_simple_rank_three M hloop hsimple hne hmin hconn hrank
  exact exists_canonical_K4_enumeration_of_complete M hM hc hd he

end WaveTurbulence.MoleProp

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBondErasure
public import WaveTurbulence.Foundations.Molecule.Degen.Bridges
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-! # DH23 Appendix B: a bridge splits exactly one component

The quotient maps are constructed from actual adjacency before and after
bond deletion. Isolated endpoint atoms are retained.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

abbrev AppbComponents (M : Molecule V D) := Quot (fun u v : M.atoms => M.Adj u.val v.val)

@[expose] def appbComponent (M : Molecule V D) (v : M.atoms) : AppbComponents M :=
  Quot.mk _ v

@[expose] def appbBridgeForget (M : Molecule V D) (e : D) :
    AppbComponents (eraseBond M e) → AppbComponents M :=
  Quot.lift (fun v => appbComponent M v) (by
    intro u v h
    obtain ⟨x,hx,hy⟩ := h
    exact Quot.sound ⟨x.val,hx,hy⟩)

@[expose] noncomputable def appbBridgeSquash (M : Molecule V D) (e : D)
    (q : AppbComponents (eraseBond M e)) : AppbComponents (eraseBond M e) := by
  classical
  exact if q = appbComponent (eraseBond M e) ⟨M.atom (M.mate e),M.atom_mem _⟩
    then appbComponent (eraseBond M e) ⟨M.atom e,M.atom_mem _⟩ else q

private theorem appb_bridge_endpoints_ne (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    appbComponent (eraseBond M e) ⟨M.atom e,M.atom_mem _⟩ ≠
      appbComponent (eraseBond M e) ⟨M.atom (M.mate e),M.atom_mem _⟩ := by
  intro h
  have hp := (quotient_eq_iff_sameComponent (eraseBond M e) _ _).mp h
  have hlift : ∀ u v, (eraseBond M e).SameComponent u v →
      Relation.EqvGen (Degen.AdjWithoutBond M e) u v := by
    intro u v hp
    induction hp with
    | rel u v h =>
      obtain ⟨x,hx,hy⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨x.val,hx,hy,x.property⟩
    | refl u => exact Relation.EqvGen.refl u
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  exact hb (hlift _ _ hp)

@[expose] noncomputable def appbBridgeSection (M : Molecule V D) (e : D)
    (hb : Degen.IsBridge M e) : AppbComponents M → AppbComponents (eraseBond M e) :=
  Quot.lift (fun v => appbBridgeSquash M e (appbComponent (eraseBond M e) v)) (by
    classical
    intro u v h
    obtain ⟨x,hx,hy⟩ := h
    have hab := appb_bridge_endpoints_ne M e hb
    by_cases he : x = e
    · subst x
      have hu : u = ⟨M.atom e,M.atom_mem e⟩ := Subtype.ext hx.symm
      have hv : v = ⟨M.atom (M.mate e),M.atom_mem _⟩ := Subtype.ext hy.symm
      subst u; subst v
      unfold appbBridgeSquash
      split_ifs <;> first | rfl | contradiction
    · by_cases hm : x = M.mate e
      · subst x
        have hu : u = ⟨M.atom (M.mate e),M.atom_mem _⟩ := Subtype.ext hx.symm
        have hv : v = ⟨M.atom e,M.atom_mem _⟩ := Subtype.ext (by simpa only [M.mate_mate] using hy.symm)
        subst u; subst v
        unfold appbBridgeSquash
        split_ifs <;> first | rfl | contradiction
      · have hq : appbComponent (eraseBond M e) u = appbComponent (eraseBond M e) v :=
          Quot.sound ⟨⟨x,he,hm⟩,hx,hy⟩
        rw [hq])

theorem appbBridgeForget_section (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e)
    (q : AppbComponents M) : appbBridgeForget M e (appbBridgeSection M e hb q) = q := by
  classical
  induction q using Quot.inductionOn with | h v =>
    change appbBridgeForget M e (appbBridgeSquash M e (appbComponent (eraseBond M e) v)) = _
    unfold appbBridgeSquash
    split_ifs with h
    · have hforget := congrArg (appbBridgeForget M e) h
      change appbComponent M v = appbComponent M ⟨M.atom (M.mate e),M.atom_mem _⟩ at hforget
      have hs : appbComponent M ⟨M.atom e,M.atom_mem _⟩ =
          appbComponent M ⟨M.atom (M.mate e),M.atom_mem _⟩ := Quot.sound ⟨e,rfl,rfl⟩
      exact hs.trans hforget.symm
    · rfl

theorem appbBridgeSection_forget (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e)
    (q : AppbComponents (eraseBond M e)) :
    appbBridgeSection M e hb (appbBridgeForget M e q) = appbBridgeSquash M e q := by
  induction q using Quot.inductionOn with | h v => rfl

theorem appb_bridge_numComponents (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    (eraseBond M e).numComponents = M.numComponents + 1 := by
  classical
  let b : AppbComponents (eraseBond M e) := appbComponent (eraseBond M e) ⟨M.atom (M.mate e),M.atom_mem _⟩
  have hab := appb_bridge_endpoints_ne M e hb
  have hsq (q : AppbComponents (eraseBond M e)) : appbBridgeSquash M e q ≠ b := by
    unfold appbBridgeSquash
    split_ifs with h
    · exact hab
    · exact h
  have hsec (q : AppbComponents M) : appbBridgeSection M e hb q ≠ b := by
    rw [← appbBridgeForget_section M e hb q,appbBridgeSection_forget]
    exact hsq _
  let f : {q : AppbComponents (eraseBond M e) // q ≠ b} ≃ AppbComponents M := {
    toFun := fun q => appbBridgeForget M e q.val
    invFun := fun q => ⟨appbBridgeSection M e hb q,hsec q⟩
    left_inv := by
      intro q
      apply Subtype.ext
      change appbBridgeSection M e hb (appbBridgeForget M e q.val) = q.val
      rw [appbBridgeSection_forget]
      exact if_neg q.property
    right_inv := appbBridgeForget_section M e hb }
  letI : Fintype (AppbComponents (eraseBond M e)) := Fintype.ofFinite _
  letI : Fintype (AppbComponents M) := Fintype.ofFinite _
  have hc := Fintype.card_congr f
  have hp := Fintype.card_subtype_compl (fun q : AppbComponents (eraseBond M e) => q = b)
  have he : Fintype.card {q : AppbComponents (eraseBond M e) // q = b} = 1 := by simp
  change Nat.card (AppbComponents (eraseBond M e)) = Nat.card (AppbComponents M) + 1
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  rw [he] at hp
  change Fintype.card {q : AppbComponents (eraseBond M e) // ¬q = b} = _ at hc
  rw [hp] at hc
  have hcpos : 0 < Fintype.card (AppbComponents (eraseBond M e)) :=
    Fintype.card_pos_iff.mpr ⟨b⟩
  omega

/-- DH23 brprop, correcting the statement's sign to agree with its proof. -/
theorem appb_bridge_nu (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    appbNu (eraseBond M e) - appbNu M = -2 := by
  have he := appb_eraseBond_card_bonds M e
  have hez : ((eraseBond M e).bonds.card : ℤ) + 1 = M.bonds.card := by exact_mod_cast he
  have hf := appb_bridge_numComponents M e hb
  have hfz : ((eraseBond M e).numComponents : ℤ) = M.numComponents + 1 := by exact_mod_cast hf
  unfold appbNu
  change 4 * (M.atoms.card : ℤ) - 2 * (eraseBond M e).bonds.card - 4 * (eraseBond M e).numComponents -
    (4 * M.atoms.card - 2 * M.bonds.card - 4 * M.numComponents) = -2
  omega

end WaveTurbulence.Mole

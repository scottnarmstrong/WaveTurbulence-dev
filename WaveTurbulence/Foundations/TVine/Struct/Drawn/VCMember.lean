/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.TVine.Core.Bridge
public import WaveTurbulence.Foundations.TVine.Core.Lemma19Del
public import WaveTurbulence.Foundations.Molecule.VineInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.Molecule.ConnectedGeometryBridge
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
public import WaveTurbulence.Foundations.FinalCount.S1Erase
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy

/-!
# Lemma 8.1′ (packet L3D): the per-ingredient facts for the family `𝒱_γ`

DH23's proof of Lemma 8.1 (TARGET `vinechainlem`, L1930–L1933) uses only block facts and three facts about each vine
ingredient: it is connected, it stays connected after deleting any one atom, and its interior (the atoms other than
the joints) is connected. N2 N6 (`research-gamma-half-2/NOTES.md` L978–L983, REFEREED REF2): with `DV` replaced by
`DV′`, "DH23's proof of Lemma 8.1 then holds verbatim".

For a drawn vine these are main's `Vine.isVine_erase_connected`, `Vine.isVine_interior_connected`. For a T-vine they are
N2 Theorem 1.15 (F1) (DH23 `disjointlem` (i), (ii)), which this packet takes as the NAMED INPUT `TVineF1Input`
(owner L3: `TVine.Struct.f1_mol`, the first two conjuncts of `TVine.Struct.SubObjectsStatement`), together with a
direct argument for the deletion of a joint.

* `member_cases`: a member of `𝒱_γ` is a drawn vine or a T-vine (for every `γ`);
* `member_connected`, `member_erase_connected`, `member_interior_connected`;
* `member_eraseBond`: deleting a bond outside the group keeps a member a member.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn.VC

open Finset WaveTurbulence.GammaLow.FinalCount TVine WaveTurbulence.TVine.Core

universe u v

/-- **NAMED INPUT (N2 Theorem 1.15 (F1); owner L3).** The interior of a T-vine is connected (DH23 `disjointlem` (i)),
and a T-vine has no interior cut atom ((ii)). (`research-gamma-half-2/NOTES.md` Theorem 1.15 (F1), REF2 R1 patch in
N3 §2.1, M4 §2.2 L191; body-identical to L5a's `GammaLow.Fama.TVineF1Input` and to the first two conjuncts of L3's
`TVine.Struct.SubObjectsStatement`; proved by L3's `TVine.Struct.f1_mol`.) -/
def TVineF1Input : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      M.GroupConnected ((S.erase j₁).erase j₂) ∧
      (∀ w ∈ S, w ≠ j₁ → w ≠ j₂ → M.GroupConnected (S.erase w))

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ}
  {S : Finset V} {a b : V}

/-- A member of `𝒱_γ` is a drawn vine or a T-vine. -/
theorem member_cases (h : Src.IsSomeVine γ M S a b) : (∃ X, M.IsVine X S a b) ∨ M.IsTVine S a b := by
  rcases h with ⟨-, h | h | h⟩ | ⟨-, X, h⟩
  · exact Or.inl ⟨_, h⟩
  · exact Or.inl ⟨_, h⟩
  · exact Or.inr h
  · exact Or.inl ⟨X, h⟩

theorem member_block (h : Src.IsSomeVine γ M S a b) : M.IsBlock S a b := Src.isBlock_of_isSomeVine h

theorem member_ends (h : Src.IsSomeVine γ M S a b) : a ∈ S ∧ b ∈ S ∧ a ≠ b :=
  ⟨(member_block h).2.1, (member_block h).2.2.1, (member_block h).2.2.2.1⟩

/-- Pinned connectivity of a nonempty group gives connectivity in the induced molecule. -/
theorem vconn_of_pinned {T : Finset V} (h : M.GroupConnected T) : Vine.GroupConnected M T := by
  intro x hx y hy
  exact (Molecpl.connected_to_induced M ⟨x, hx⟩ h).2 x hx y hy

/-- A member is connected. -/
theorem member_connected (h : Src.IsSomeVine γ M S a b) : Vine.GroupConnected M S :=
  (LGSpine.groupConnected_of_block (member_block h)).2

/-- The interior of a member is connected (N2 Thm 1.15 (F1)(i) for T-vines). -/
theorem member_interior_connected (hF1 : TVineF1Input.{u, v}) (h : Src.IsSomeVine γ M S a b) :
    Vine.GroupConnected M (S \ {a, b}) := by
  rcases member_cases h with ⟨X, hX⟩ | hT
  · exact Vine.isVine_interior_connected hX
  · have he : S \ {a, b} = (S.erase a).erase b := by
      ext x; simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]; tauto
    rw [he]
    exact vconn_of_pinned (hF1 M S a b hT).1

/-- A joint of a T-vine has a bond to an interior atom. -/
theorem tvine_joint_adj_interior (hT : M.IsTVine S a b) : ∃ w ∈ (S.erase a).erase b, M.Adj b w := by
  have hTU := ((isTVine_iff M).mp hT).2
  have hl := hTU.loopless
  obtain ⟨⟨haV, hbV, hab, -⟩, -, C, ⟨hσ, -, -, added, hdata, -⟩, -⟩ := hTU
  set G := groupGraph M S with hG
  -- a neighbour `c` of `b` other than `a`, `b` in the closure data
  have key : ∀ c : V, c ∈ nbrs G b → c ≠ a → ∃ w ∈ (S.erase a).erase b, M.Adj b w := by
    intro c hc hca
    have hcount := count_nbrs G b c
    have hpos : 0 < (nbrs G b).count c := Multiset.count_pos.mpr hc
    have hcb : c ≠ b := by
      intro hcb; subst hcb
      have h0 : G.mult s(c, c) = 0 := hl c
      have : (nbrs G c).count c = 0 := by rw [hcount, h0]; simp
      omega
    rw [ite_eq_right (Ne.symm hcb)] at hcount
    by_cases hcV : c ∈ G.verts
    · rw [ite_eq_left hcV] at hcount
      have hm : G.mult s(b, c) ≠ 0 := by omega
      have hcS : c ∈ S := hcV
      have hadj : AdjIn G S b c := ⟨hbV, hcS, hm⟩
      obtain ⟨x, -, hx1, hx2⟩ := (adjIn_groupGraph_iff M).mp hadj
      exact ⟨c, mem_erase.mpr ⟨hcb, mem_erase.mpr ⟨hca, hcS⟩⟩, x, hx1, hx2⟩
    · rw [ite_eq_right hcV] at hcount; omega
  rcases hdata with ⟨h0, c₁, c₂, c₃, c₄, h1, h2, -⟩ | ⟨h1, x, y, h1', h2, -⟩
  · -- σ = 0: both neighbours of `b` differ from `a`
    have hc3 : c₃ ∈ nbrs G b := by rw [h2]; simp
    apply key c₃ hc3
    intro h3a
    have hm := mult_of_nbrs_eq h2 (show a ≠ b from hab)
    rw [Sym2.eq_swap, h0, h3a] at hm
    simp at hm
  · -- σ = 1: the neighbour `y` of `b` differs from `a`
    have hy : y ∈ nbrs G b := by rw [h2]; simp
    apply key y hy
    intro hya
    subst hya
    have hm := mult_of_nbrs_eq h2 (show y ≠ b from hab)
    rw [Sym2.eq_swap, h1] at hm
    simp at hm

/-- A member stays connected after deleting any one atom (N2 Thm 1.15 (F1)(ii) for interior atoms of T-vines). -/
theorem member_erase_connected (hF1 : TVineF1Input.{u, v}) (h : Src.IsSomeVine γ M S a b) (z : V) :
    Vine.GroupConnected M (S.erase z) := by
  rcases member_cases h with ⟨X, hX⟩ | hT
  · exact Vine.isVine_erase_connected hX z
  · obtain ⟨haS, hbS, hab⟩ := member_ends h
    by_cases hzS : z ∈ S
    · by_cases hza : z = a
      · -- deleting the joint `a`
        subst hza
        obtain ⟨w, hwI, hbw⟩ := tvine_joint_adj_interior hT
        have hI := member_interior_connected hF1 h
        have hsub : S \ {z, b} ⊆ S.erase z := by
          intro x hx; simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx
          exact mem_erase.mpr ⟨hx.2.1, hx.1⟩
        have hwI' : w ∈ S \ {z, b} := by
          simp only [mem_erase] at hwI; simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
          exact ⟨hwI.2.2, hwI.2.1, hwI.1⟩
        have hbE : b ∈ S.erase z := mem_erase.mpr ⟨Ne.symm hab, hbS⟩
        have hwE : w ∈ S.erase z := hsub hwI'
        have reach : ∀ x ∈ S.erase z, (Mole.induced M (S.erase z)).SameComponent w x := by
          intro x hx
          by_cases hxb : x = b
          · subst hxb
            exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
              ((Mole.induced_adj_iff M (S.erase z) x w).mpr ⟨hbw, hbE, hwE⟩))
          · have hxI : x ∈ S \ {z, b} := by
              simp only [mem_erase] at hx; simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
              exact ⟨hx.2, hx.1, hxb⟩
            exact Vine.induced_path_mono M hsub (hI w hwI' x hxI)
        intro x hx y hy
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach x hx)) (reach y hy)
      · by_cases hzb : z = b
        · -- deleting the joint `b`
          subst hzb
          have hT' : M.IsTVine S z a := GammaLow.Fama.isTVine_swap hT
          obtain ⟨w, hwI, haw⟩ := tvine_joint_adj_interior hT'
          have hI := member_interior_connected hF1 h
          have hsub : S \ {a, z} ⊆ S.erase z := by
            intro x hx; simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx
            exact mem_erase.mpr ⟨hx.2.2, hx.1⟩
          have hwI' : w ∈ S \ {a, z} := by
            simp only [mem_erase] at hwI; simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
            exact ⟨hwI.2.2, hwI.1, hwI.2.1⟩
          have haE : a ∈ S.erase z := mem_erase.mpr ⟨hab, haS⟩
          have hwE : w ∈ S.erase z := hsub hwI'
          have reach : ∀ x ∈ S.erase z, (Mole.induced M (S.erase z)).SameComponent w x := by
            intro x hx
            by_cases hxa : x = a
            · subst hxa
              exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
                ((Mole.induced_adj_iff M (S.erase z) x w).mpr ⟨haw, haE, hwE⟩))
            · have hxI : x ∈ S \ {a, z} := by
                simp only [mem_erase] at hx; simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
                exact ⟨hx.2, hxa, hx.1⟩
              exact Vine.induced_path_mono M hsub (hI w hwI' x hxI)
          intro x hx y hy
          exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach x hx)) (reach y hy)
        · exact vconn_of_pinned ((hF1 M S a b hT).2 z hzS hza hzb)
    · rw [erase_eq_of_notMem hzS]
      exact member_connected h

/-- Deleting a bond outside the group keeps a member of `𝒱_γ` a member. -/
theorem member_eraseBond (h : Src.IsSomeVine γ M S a b) (e : D) (he : ¬ M.InGroup S e) :
    Src.IsSomeVine γ (Molecule.eraseBond M e) S a b := by
  have hT_of : M.IsTVine S a b → (Molecule.eraseBond M e).IsTVine S a b := by
    intro hT
    rw [isTVine_iff] at hT ⊢
    refine ⟨Stage1.isBlock_eraseBond e hT.1 he, ?_⟩
    have hg : groupGraph (Molecule.eraseBond M e) S = groupGraph M S := by
      refine Core.ext rfl fun f => ?_
      rw [groupGraph_mult, groupGraph_mult, Stage1.eraseBond_groupBonds_eq e he]
    rw [hg]; exact hT.2
  rcases h with ⟨hγ, h | h | h⟩ | ⟨hγ, X, h⟩
  · exact Or.inl ⟨hγ, Or.inl (Stage1.isVine_eraseBond e h he)⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inl (Stage1.isVine_eraseBond e h he))⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inr (hT_of h))⟩
  · exact Or.inr ⟨hγ, X, Stage1.isVine_eraseBond e h he⟩

end WaveTurbulence.TVine.Struct.Drawn.VC

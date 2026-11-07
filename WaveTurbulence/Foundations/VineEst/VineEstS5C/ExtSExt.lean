/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitDec
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsLocal
public import WaveTurbulence.Foundations.Molecule.BlockParent

/-! # An upper-block decoration is determined by the labels at the first leaves of its pairs (V5 Step 4d part C)

`extS_ext_of_pairs`: for the CL parent pattern (the lower joint `b` has an internal parent, the upper joint `a` has none), two decorations of the
upper block `S` with the same boundary `(e, f)` that agree at the first leaf of every regional pair of `S` coincide.  Bottom-up (conservation at
`S.erase b`) the difference `δ` can only be non-zero on the tree ancestors of `b`; at the shallowest such node `n ≠ a` the conservation at its
parent (which lies in `S` by the block degree conditions) forces `δ n = 0`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem extS_ext_of_pairs (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) (hG : G.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (e f : Mom d) (x x' : ExtS RS L base e f)
    (h : ∀ p ∈ clRegionalPairs hG S,
      x.1 (p.firstLeaf hG).toNode = x'.1 (p.firstLeaf hG).toNode) : x = x' := by
  classical
  let δ : GNode G.tree → (Fin d → ℤ) := fun n => x.1 n - x'.1 n
  have hz : ∀ n, n ∉ splitA RS → δ n = 0 := fun n hn => by
    simp only [δ, x.2.1.1 n hn, x'.2.1.1 n hn, sub_self]
  have hcons : ∀ v ∈ S.erase b, δ v.toNode = δ (v.child 0) - δ (v.child 1) + δ (v.child 2) := by
    intro v hv
    have h1 := x.2.1.2.1 v hv
    have h2 := x'.2.1.2.1 v hv
    simp only [δ, h1, h2]
    abel
  have hleaf : ∀ ℓ : GLeaf G.tree, Mole.IsInternalLeaf G S ℓ → δ ℓ.toNode = 0 := by
    intro ℓ hℓ
    obtain ⟨p, hp, hpℓ⟩ := internalLeaf_first_or_second hG ℓ hℓ
    have hfirst : δ (p.firstLeaf hG).toNode = 0 := sub_eq_zero.mpr (h p hp)
    rcases hpℓ with he | he
    · rw [← he]; exact hfirst
    · have h0 := hfirst
      rw [he] at h0
      have hp1 := x.2.1.2.2 ℓ hℓ
      have hp2 := x'.2.1.2.2 ℓ hℓ
      simp only [δ] at h0 ⊢
      rw [hp1, hp2]
      exact h0
  have htop0 : δ a.toNode = 0 := by
    have h1 := x.2.2.1
    have h2 := x'.2.2.1
    have := latticePoint_injective_of_ne_zero hL (h1.trans h2.symm |> fun h => add_left_cancel h)
    simp only [δ, this, sub_self]
  have htop1 : δ (a.child RS.excluded) = 0 := by
    have h1 := x.2.2.2
    have h2 := x'.2.2.2
    have := latticePoint_injective_of_ne_zero hL (h1.trans h2.symm |> fun h => add_left_cancel h)
    simp only [δ, this, sub_self]
  set B := (Finset.univ : Finset (GNode G.tree)).sup fun n => n.1.2.length with hB
  have hle : ∀ n : GNode G.tree, n.1.2.length ≤ B := fun n =>
    Finset.le_sup (f := fun n : GNode G.tree => n.1.2.length) (Finset.mem_univ n)
  -- a node with non-zero difference is the node of an atom of `S`
  have hbr : ∀ n : GNode G.tree, δ n ≠ 0 → ∃ w : GBranch G.tree, w ∈ S ∧ w.toNode = n := by
    intro n hn
    have hns : n ∈ splitA RS := by
      by_contra hno
      exact hn (hz n hno)
    unfold splitA at hns
    rcases Finset.mem_union.mp hns with hr | hb'
    · rcases (Comb.TreePath.mem_nodes_iff _ _).1 n.2 with hl | hbr
      · exact absurd (hleaf ⟨n.1, hl⟩ ((leaf_mem_clRealizationNodes (G := G) (U := S) ⟨n.1, hl⟩).mp hr)) hn
      · exact ⟨⟨n.1, hbr⟩, (branch_mem_clRealizationNodes (G := G) (U := S) ⟨n.1, hbr⟩).mp hr, rfl⟩
    · rcases Finset.mem_insert.mp hb' with h0 | h1
      · exact absurd (h0 ▸ htop0) hn
      · exact absurd ((Finset.mem_singleton.mp h1) ▸ htop1) hn
  -- bottom-up: a non-zero difference sits at a tree ancestor of `b`
  have hanc : ∀ m : ℕ, ∀ n : GNode G.tree, B - n.1.2.length = m → δ n ≠ 0 →
      (n.1.1 = b.1.1 ∧ n.1.2 <+: b.1.2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hm hn
      obtain ⟨w, hwS, rfl⟩ := hbr n hn
      by_cases hwb : w = b
      · subst hwb; exact ⟨rfl, List.prefix_refl _⟩
      · have hv : w ∈ S.erase b := Finset.mem_erase.mpr ⟨hwb, hwS⟩
        have hc := hcons w hv
        have hex : ∃ i : Fin 3, δ (w.child i) ≠ 0 := by
          by_contra hno
          push Not at hno
          rw [hno 0, hno 1, hno 2] at hc
          exact hn (by simpa using hc)
        obtain ⟨i, hi⟩ := hex
        have hlen : (w.child i).1.2.length = w.1.2.length + 1 := by simp [GBranch.child]
        have hlt := hle (w.child i)
        have hwt : (w.toNode).1.2.length = w.1.2.length := rfl
        have hrec := ih (B - (w.child i).1.2.length) (by omega) (w.child i) rfl hi
        exact ⟨hrec.1, (List.prefix_append w.1.2 [i]).trans hrec.2⟩
  -- top-down: the shallowest non-zero difference cannot exist
  have hall : ∀ n, δ n = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n0, hn0⟩ := hcon
    obtain ⟨n, hnmem, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun n : GNode G.tree => δ n ≠ 0)
      (fun n => n.1.2.length) ⟨n0, by simp [hn0]⟩
    have hnδ : δ n ≠ 0 := (Finset.mem_filter.mp hnmem).2
    obtain ⟨w, hwS, rfl⟩ := hbr n hnδ
    have hanc_n := hanc _ w.toNode rfl hnδ
    have hwa : w ≠ a := by
      rintro rfl
      exact hnδ htop0
    have hpar : Mole.InternalParent G S w := by
      by_cases hwb : w = b
      · subst hwb; exact RS.parentPattern.2
      · exact Mole.block_interior_has_parent G hS hwS hwa hwb
    obtain ⟨hne0, hpS⟩ := hpar
    set pb : GBranch G.tree := GNode.parent w.toNode hne0 with hpb
    obtain ⟨j, hjdef⟩ : ∃ j : Fin 3, j = w.1.2.getLast hne0 := ⟨_, rfl⟩
    have hpchild : pb.child j = w.toNode := by
      rw [hjdef]; exact Mole.parent_child_eq_node w.toNode hne0
    have hpath : w.1.2 = pb.1.2 ++ [j] := by
      have := congrArg (fun z : GNode G.tree => z.1.2) hpchild
      exact this.symm
    have hlenw : w.1.2.length = pb.1.2.length + 1 := by rw [hpath]; simp
    have hpb_ne : pb ≠ b := by
      intro hpb'
      have h1 := hanc_n.2.length_le
      rw [← hpb'] at h1
      change w.1.2.length ≤ pb.1.2.length at h1
      omega
    have hpe : pb ∈ S.erase b := Finset.mem_erase.mpr ⟨hpb_ne, hpS⟩
    have hδp : δ pb.toNode = 0 := by
      by_contra hne
      have hmem : pb.toNode ∈ Finset.univ.filter fun n : GNode G.tree => δ n ≠ 0 := by simp [hne]
      have := hmin _ hmem
      change w.1.2.length ≤ pb.1.2.length at this
      omega
    have hsib : ∀ i : Fin 3, i ≠ j → δ (pb.child i) = 0 := by
      intro i hij
      by_contra hne
      have hA := hanc _ (pb.child i) rfl hne
      have hP1 : pb.1.2 ++ [i] <+: b.1.2 := hA.2
      have hP2 : pb.1.2 ++ [j] <+: b.1.2 := hpath ▸ hanc_n.2
      have hl : (pb.1.2 ++ [i]).length ≤ (pb.1.2 ++ [j]).length := by simp
      have hpre := (List.prefix_of_prefix_length_le hP1 hP2 hl).eq_of_length (by simp)
      have := List.append_cancel_left hpre
      exact hij (by simpa using this)
    have hc := hcons pb hpe
    rw [hδp] at hc
    have h0 := fun h => hsib 0 h
    have h1 := fun h => hsib 1 h
    have h2 := fun h => hsib 2 h
    have hfin : δ (pb.child j) = 0 := by
      fin_cases j
      · simp only [Fin.zero_eta] at *
        rw [h1 (by decide), h2 (by decide)] at hc
        simpa using hc.symm
      · simp only [Fin.mk_one] at *
        rw [h0 (by decide), h2 (by decide)] at hc
        simpa using hc.symm
      · rw [h0 (by decide), h1 (by decide)] at hc
        simpa using hc.symm
    rw [hpchild] at hfin
    exact hnδ hfin
  apply Subtype.ext
  funext n
  exact sub_eq_zero.mp (hall n)

end WaveTurbulence.VineEstS5C

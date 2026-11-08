/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CheckP5P7

/-! # D2c-2 PROT-CUT: D3's multiplier with star weights at any node

`multFactors_D3` (MultLocal) asked the star nodes `S` to be branching. D3's `ProtBoundAt` quantifies over every
`S`. A star at a leaf is `(K ℓ, K ℓ, K ℓ, K ℓ)`; a non-root leaf is a child of a branching node, so its factor is
read on its parent's star (`leafKids`). Hence `starWeight S ω` is branch-local as soon as every root in `S` is
branching (`starWeight_branch`), and D3's multiplier factors at every cut without a hypothesis on `S`:

* `CutTermData.multFactors_D3'` ((cut-term), (P4), (P5), (P7));
* `CapData.multFactors_D3_cap'` (cap couples; the cap's factor reads the lone leaf, a child of `𝔫_b`);
* `PairOnly.multFactors_D3` ((P2), with the terminal-child indicator `ind` read on the star of `𝔫_b`);
* `RootData.multFactors_D3` ((P1), (P3), (trace); `ind` moves to the suffix as `indS`, a terminal-child indicator of
  the suffix code, `termChild_indS`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Flower.FlShell (chiD)

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {w d : ℕ}

/-! ### Stars at leaves, read on the parent's star -/

/-- The star factors of the leaf children (in `S`) of a branching node, read on its star. -/
def leafKids {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (b : GBranch G.tree) (ξ : Fin 4 → Mom d) : ℂ :=
  ∏ i : Fin 3, if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
    ω (b.child i) (WithLp.toLp 2 fun _ => ξ i.succ) else 1

/-- One branch's factor of `starWeight S ω` (its own star and its leaf children's). -/
def fS {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ) (b : GBranch G.tree)
    (ξ : Fin 4 → Mom d) : ℂ :=
  (if b.toNode ∈ S then ω b.toNode (WithLp.toLp 2 ξ) else 1) * leafKids S ω b ξ

theorem starMomenta_leaf {T : Fin w → TTree} (K : GNode T → Mom d) (a : GNode T)
    (ha : a.1.2 ∉ (T a.1.1).branching) : IncTop.starMomenta K a = WithLp.toLp 2 fun _ => K a := by
  unfold IncTop.starMomenta IncTop.starNode
  simp only [dif_neg ha]

/-- **`starWeight` is branch-local** when every root in `S` is branching. -/
theorem starWeight_branch {G : Garden w} (S : Finset (GNode G.tree))
    (hroot : ∀ a ∈ S, a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (K : GNode G.tree → Mom d) : IncTop.starWeight S ω K = ∏ b : GBranch G.tree, fS S ω b (bstar K b) := by
  classical
  unfold IncTop.starWeight fS
  rw [Finset.prod_mul_distrib,
    ← Finset.prod_filter_mul_prod_filter_not S (fun a => a.1.2 ∈ (G.tree a.1.1).branching)]
  congr 1
  · rw [prod_branchNodes (S.filter _) (fun a ha => (Finset.mem_filter.mp ha).2)]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hb : b.toNode ∈ S.filter (fun a => a.1.2 ∈ (G.tree a.1.1).branching) ↔ b.toNode ∈ S := by
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.1, fun h => ⟨h, b.2⟩⟩
    by_cases h : b.toNode ∈ S
    · rw [if_pos (hb.mpr h), if_pos h, starMomenta_branch]
    · rw [if_neg (fun h' => h (hb.mp h')), if_neg h]
  · unfold leafKids
    rw [← Fintype.prod_prod_type' (fun (b : GBranch G.tree) (i : Fin 3) =>
      if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
        ω (b.child i) (WithLp.toLp 2 fun _ => bstar K b i.succ) else 1), ← Finset.prod_filter]
    symm
    refine Finset.prod_bij (fun x _ => x.1.child x.2) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_filter.mpr hx
    · intro x _ y _ hxy
      have h1 := congrArg (fun a : GNode G.tree => a.1) hxy
      simp only [GBranch.child, Prod.mk.injEq] at h1
      obtain ⟨h1a, h1b⟩ := h1
      have h2 := List.append_inj' h1b rfl
      have hb : x.1 = y.1 := Subtype.ext (Prod.ext h1a h2.1)
      have hi : x.2 = y.2 := by simpa using h2.2
      exact Prod.ext hb hi
    · intro a ha
      obtain ⟨haS, hab⟩ := Finset.mem_filter.mp ha
      have hne : a.1.2 ≠ [] := fun h0 => hab (hroot a haS h0)
      obtain ⟨p, i, hp⟩ := (List.eq_nil_or_concat a.1.2).resolve_left hne
      have hmem : p ∈ (G.tree a.1.1).branching := by
        have := a.2
        rw [hp, List.concat_eq_append] at this
        exact TTree.branching_of_append_mem _ this
      refine ⟨(⟨(a.1.1, p), hmem⟩, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have e : GBranch.child (⟨(a.1.1, p), hmem⟩ : GBranch G.tree) i = a :=
          Subtype.ext (Prod.ext rfl (by rw [hp, List.concat_eq_append]; rfl))
        rw [e]
        exact ⟨haS, hab⟩
      · exact Subtype.ext (Prod.ext rfl (by rw [hp, List.concat_eq_append]; rfl))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [starMomenta_leaf K _ hx.2]
      rfl

/-! ### D3's multiplier -/

/-- One branch's factor of D3's `starWeight · filtWeight · filtWeight`, leaf stars included. -/
def fD3' {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (b : GBranch G.tree) (ξ : Fin 4 → Mom d) : ℂ :=
  fD3 S ω F ann M Fu Mu b ξ * leafKids S ω b ξ

/-- **D3's `starWeight · filtWeight · filtWeight` is branch-local** (roots in `S` branching). -/
theorem starFilt_local' {G : Garden w} (S : Finset (GNode G.tree))
    (hroot : ∀ a ∈ S, a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching)
    (ω : GNode G.tree → IncTop.Star d → ℂ) (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (K : GNode G.tree → Mom d) :
    IncTop.starWeight S ω K * filtWeight F ann M K * filtWeight Fu (fun _ => false) Mu K =
      ∏ b : GBranch G.tree, fD3' S ω F ann M Fu Mu b (bstar K b) := by
  have h0 := starFilt_local (∅ : Finset (GNode G.tree)) (by simp) ω F ann M Fu Mu K
  have hS0 : IncTop.starWeight (∅ : Finset (GNode G.tree)) ω K = 1 := by simp [IncTop.starWeight]
  rw [hS0, one_mul] at h0
  rw [mul_assoc, h0, starWeight_branch S hroot ω K, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  unfold fD3' fS fD3
  simp only [Finset.notMem_empty, if_false, one_mul]
  ring

/-- The root of a nonempty chain's tree is branching. -/
theorem nil_mem_branching_plug (X : RegChain) (hX : X ≠ .nil) (ζ : ℤˣ) (t : TTree) :
    ([] : Path) ∈ (X.plug ζ t).branching := by
  cases X with
  | nil => exact absurd rfl hX
  | pair m Qr Qg inner rest => exact (mem_node3_nil _).2.2

theorem appendChain_ne_nil (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) :
    appendChain Xp (cpair m Qr Qg inner) ≠ .nil := by
  cases Xp <;> simp [appendChain, cpair]

/-- The roots of a protected tree are branching. -/
theorem hroot_tree {LG : LayeredGarden 1} {X : RegChain} (hX : X ≠ .nil) (hdec : X.DecodesTree LG.garden)
    (S : Finset (GNode LG.garden.tree)) : ∀ a ∈ S, a.1.2 = [] → a.1.2 ∈ (LG.garden.tree a.1.1).branching := by
  intro a _ h0
  rw [h0, Subsingleton.elim a.1.1 0, hdec.1]
  exact nil_mem_branching_plug X hX _ _

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
include D

/-- **D3's multiplier factors at the terminal cut, for every `S`** ((cut-term), (P4), (P5), (P7)). -/
theorem multFactors_D3' (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) :
    D.MultFactors
      (fun κ => IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F ann M Fu Mu D.aBr A * fD3' S ω F ann M Fu Mu D.bBr B * ((indB ind B : ℝ) : ℂ))
      (fun K => ∏ x, fD3' S ω F ann M Fu Mu (D.βP x) (bstar K x))
      (fun K => ∏ x, fD3' S ω F ann M Fu Mu (D.βI x) (bstar K x))
      (fun K => ∏ y, fD3' S ω F ann M Fu Mu (D.βR y) (bstar K y))
      (fun K => ∏ y, fD3' S ω F ann M Fu Mu (D.βG y) (bstar K y)) := by
  intro K
  have h := D.multFactors_local (fD3' S ω F ann M Fu Mu) (fun B => ((indB ind B : ℝ) : ℂ)) K
  try simp only at h ⊢
  rw [starFilt_local' S (hroot_tree (appendChain_ne_nil Xp m Qr Qg inner) D.dec S), D.ind_eq ind hind K]
  exact h

end CutTermData

/-! ### (P2): the indicator on the star of `𝔫_b` -/

namespace PairOnly

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)
include D

theorem ind_eq (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind)
    (K : GNode LG.garden.tree → Mom d) : ind K = indB ind (bstar K D.hp.bB) := by
  unfold indB
  refine hind.2 _ _ fun a _ hne hd => ?_
  rw [dif_pos hne]
  show K a = K (D.hp.bB.child (a.1.2.getLast hne))
  refine congrArg K (Subtype.ext (Prod.ext (Subsingleton.elim _ _) ?_))
  show a.1.2 = bPath m inner ++ [a.1.2.getLast hne]
  have e : (cpair m Qr Qg inner).lonePath.dropLast = bPath m inner := by
    rw [cpair_lonePath, lonePos, List.dropLast_concat]
  rw [← e, ← hd, List.dropLast_append_getLast]

/-- **D3's multiplier factors at the pair, for every `S`, with the terminal-child indicator** ((P2)). -/
theorem multFactors_D3 (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind) :
    D.MultFactors
      (fun κ => IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F ann M Fu Mu D.hp.rootB A * fD3' S ω F ann M Fu Mu D.hp.bB B *
        ((indB ind B : ℝ) : ℂ))
      (fun K => ∏ x, fD3' S ω F ann M Fu Mu (D.hp.βi x) (bstar K x))
      (fun K => ∏ y, fD3' S ω F ann M Fu Mu (D.hp.βr y) (bstar K y))
      (fun K => ∏ y, fD3' S ω F ann M Fu Mu (D.hp.βg y) (bstar K y)) := by
  intro K
  have h := D.multFactors_local (fD3' S ω F ann M Fu Mu) K
  try simp only at h ⊢
  have hX : cpair m Qr Qg inner ≠ .nil := by simp [cpair]
  rw [starFilt_local' S (hroot_tree hX D.dec S), h, D.ind_eq ind hind K, ← D.bstar_bB K]
  ring

end PairOnly

/-! ### (P1), (P3), (trace): the indicator moves to the suffix -/

/-- An indicator of the protected tree, read on a function of the suffix's nodes (placed at `lonePos m inner`). -/
def indS (m : MiniTreeCode) (inner : RegChain) {T T' : Fin 1 → TTree} (ind : (GNode T → Mom d) → ℝ)
    (K' : GNode T' → Mom d) : ℝ :=
  ind fun a => Links.extend K' ((0 : Fin 1), a.1.2.drop (lonePos m inner).length)

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

theorem lonePath_dropLast : (RegChain.pair m Qr Qg inner rest).lonePath.dropLast =
    lonePos m inner ++ rest.lonePath.dropLast := by
  rw [lonePath_eq, List.dropLast_append_of_ne_nil D.rest_lonePath_ne]

theorem ind_eq_S (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (RegChain.pair m Qr Qg inner rest) ind) (K : GNode LG.garden.tree → Mom d) :
    ind K = indS m inner ind (K ∘ D.ιS) := by
  unfold indS
  refine hind.2 _ _ fun a _ hne hd => ?_
  rw [D.lonePath_dropLast] at hd
  set q := rest.lonePath.dropLast ++ [a.1.2.getLast hne] with hq
  have hpath : a.1.2 = lonePos m inner ++ q := by
    rw [hq, ← List.append_assoc, ← hd, List.dropLast_append_getLast]
  have hdrop : a.1.2.drop (lonePos m inner).length = q := by rw [hpath, List.drop_left]
  rw [hdrop]
  have hbot : botAddr (cpair m Qr Qg inner).lonePath ((0 : Fin 1), q) = a.1 := by
    rw [cpair_lonePath]
    exact Prod.ext (Subsingleton.elim _ _) (by simp [botAddr, hpath])
  have hmem : q ∈ (LGs.garden.tree 0).nodes := by
    have := (D.gd.bot_iff ((0 : Fin 1), q)).1.mp
    rw [hbot] at this
    exact this a.2
  have e := extend_node (K ∘ D.ιS) ⟨((0 : Fin 1), q), hmem⟩
  rw [e]
  exact congrArg K (Subtype.ext hbot.symm)

/-- `indS` is a terminal-child indicator of the suffix code. -/
theorem termChild_indS (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (RegChain.pair m Qr Qg inner rest) ind) {T' : Fin 1 → TTree} :
    TermChildIndicator rest (indS m inner ind : (GNode T' → Mom d) → ℝ) := by
  refine ⟨fun K => hind.1 _, fun K K' hKK => hind.2 _ _ fun a _ hne hd => ?_⟩
  rw [D.lonePath_dropLast] at hd
  set q := rest.lonePath.dropLast ++ [a.1.2.getLast hne] with hq
  have hpath : a.1.2 = lonePos m inner ++ q := by
    rw [hq, ← List.append_assoc, ← hd, List.dropLast_append_getLast]
  have hdrop : a.1.2.drop (lonePos m inner).length = q := by rw [hpath, List.drop_left]
  show Links.extend K _ = Links.extend K' _
  rw [hdrop]
  unfold Links.extend
  by_cases hm : q ∈ (T' ((0 : Fin 1), q).1).nodes
  · rw [dif_pos hm, dif_pos hm]
    refine hKK _ rfl (by simp [hq]) ?_
    show q.dropLast = rest.lonePath.dropLast
    rw [hq, List.dropLast_concat]
  · rw [dif_neg hm, dif_neg hm]

/-- **D3's multiplier factors at the root cut, for every `S`, with the terminal-child indicator in the suffix**
((P1), (P3), (trace); `ind = 1` unless the terminal node is designated). -/
theorem multFactors_D3 (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (RegChain.pair m Qr Qg inner rest) ind) :
    D.MultFactors
      (fun κ => IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F ann M Fu Mu D.aR A * fD3' S ω F ann M Fu Mu D.bR B)
      (fun K => ∏ x, fD3' S ω F ann M Fu Mu (D.gd.ofSum (.inl (D.hp.βi x))) (bstar K x))
      (fun K => ∏ y, fD3' S ω F ann M Fu Mu (D.gd.ofSum (.inl (D.hp.βr y))) (bstar K y))
      (fun K => ∏ y, fD3' S ω F ann M Fu Mu (D.gd.ofSum (.inl (D.hp.βg y))) (bstar K y))
      (fun K => (∏ y, fD3' S ω F ann M Fu Mu (D.gd.ofSum (.inr y)) (bstar K y)) * (indS m inner ind K : ℂ)) := by
  intro K
  have h := D.multFactors_local (fD3' S ω F ann M Fu Mu) K
  try simp only at h ⊢
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  rw [starFilt_local' S (hroot_tree hX D.dec S), h, D.ind_eq_S ind hind K]
  ring

end RootData

/-! ### Cap couples: the cap's star reads the lone leaf -/

namespace CapData

variable {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} (D : CapData X LG LG1)
include D

/-- The cap (tree `1`, a leaf). -/
def cap : GNode LG.garden.tree := ⟨((1 : Fin 2), []), by rw [D.tree1]; simp [TTree.nodes]⟩

theorem cap_not_branching : D.cap.1.2 ∉ (LG.garden.tree D.cap.1.1).branching := by
  show ([] : Path) ∉ (LG.garden.tree 1).branching
  rw [D.tree1]
  simp [TTree.branching]

theorem hroot_erase (hX : X ≠ .nil) (S : Finset (GNode LG.garden.tree)) :
    ∀ a ∈ S.erase D.cap, a.1.2 = [] → a.1.2 ∈ (LG.garden.tree a.1.1).branching := by
  intro a ha h0
  by_cases h1 : a.1.1 = 0
  · rw [h0, h1, D.tree0]
    exact nil_mem_branching_plug X hX _ _
  · exfalso
    have e : a = D.cap := Subtype.ext ((D.node_one a h1).trans rfl)
    exact (Finset.mem_erase.mp ha).1 e

/-- The star weight of the cap couple: the cap's factor and the rest. -/
theorem starWeight_cap (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (K : GNode LG.garden.tree → Mom d) :
    IncTop.starWeight S ω K = (if D.cap ∈ S then ω D.cap (WithLp.toLp 2 fun _ => K D.cap) else 1) *
      IncTop.starWeight (S.erase D.cap) ω K := by
  classical
  unfold IncTop.starWeight
  by_cases h : D.cap ∈ S
  · rw [if_pos h, ← Finset.mul_prod_erase S _ h, starMomenta_leaf K _ D.cap_not_branching]
  · rw [if_neg h, one_mul, Finset.erase_eq_of_notMem h]

omit D in
/-- **D3's multiplier of a cap couple factors at the cut of its paired tree, for every `S`.** -/
theorem multFactors_D3_cap' {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2}
    {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    (D : CapData (appendChain Xp (cpair m Qr Qg inner)) LG LG1)
    (C : CutTermData LG1 Xp m Qr Qg inner LGp LGi LGr LGg)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) :
    C.MultFactors
      (D.capM fun κ =>
        IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc C.aBr) A *
        fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc C.bBr) B *
        ((if D.cap ∈ S then ω D.cap (WithLp.toLp 2 fun _ => B (m.lone).succ) else 1) *
          ((indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (D.ρ a)) B : ℝ) : ℂ)))
      (fun K => ∏ x, fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc (C.βP x)) (bstar K x))
      (fun K => ∏ x, fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc (C.βI x)) (bstar K x))
      (fun K => ∏ y, fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc (C.βR y)) (bstar K y))
      (fun K => ∏ y, fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc (C.βG y)) (bstar K y)) := by
  intro K
  have h := C.multFactors_local (fun b => fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc b))
    (fun B => (if D.cap ∈ S then ω D.cap (WithLp.toLp 2 fun _ => B (m.lone).succ) else 1) *
      ((indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (D.ρ a)) B : ℝ) : ℂ)) K
  try simp only at h ⊢
  have hX : appendChain Xp (cpair m Qr Qg inner) ≠ .nil := appendChain_ne_nil Xp m Qr Qg inner
  -- the cap's star reads the lone leaf, the child `m.lone` of `𝔫_b`
  have hlone : K (D.ρ D.cap) = bstar K C.bBr (m.lone).succ := by
    rw [D.ρ_one D.cap (by simp [cap])]
    show K D.lone1 = K (C.bBr.child m.lone)
    refine congrArg K (Subtype.ext (Prod.ext (Subsingleton.elim _ _) ?_))
    show (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ bPath m inner ++ [m.lone]
    rw [appendChain_lonePath, cpair_lonePath, lonePos, List.append_assoc]
  have hi := C.ind_eq _ (D.termChild_cap ind hind) K
  unfold capM
  simp only
  rw [D.starWeight_cap S ω, show ∀ a b c e g : ℂ, a * b * c * e * g = a * (b * c * e) * g from
    fun _ _ _ _ _ => by ring, starFilt_local' (S.erase D.cap) (D.hroot_erase hX S)]
  have e1 : (∏ b : GBranch LG.garden.tree, fD3' (S.erase D.cap) ω F ann M Fu Mu b (bstar (fun a => K (D.ρ a)) b)) =
      ∏ b : GBranch LG1.garden.tree, fD3' (S.erase D.cap) ω F ann M Fu Mu (D.βc b) (bstar K b) := by
    rw [← D.βc.prod_comp]
    simp only [D.bstar_cap]
  rw [e1, hlone]
  rw [show (ind fun a => K (D.ρ a)) = indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (D.ρ a))
    (bstar K C.bBr) from hi]
  rw [← h]
  ring

end CapData

end WaveTurbulence.Flower.ProtCut

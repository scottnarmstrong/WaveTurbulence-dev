/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairTree

/-! # D2c PROT-CUT: the pieces of a closing pair, branch by branch

`PairData G Gi Gr Gg`: `G` is a paired tree decoded by the closing pair `pair m Qr Qg inner nil`, `Gi` a paired
tree decoded by the interior chain `inner` (sign of the slot `m.c`), `Gr`, `Gg` couples decoded by the side
couples `Qr`, `Qg`.

* node maps `ιi`, `ιr`, `ιg` (the lone leaf of `Gi` goes to the terminal node `𝔫_b`), branch maps `βi`, `βr`,
  `βg`, the two cut branches `rootB` (`𝔫_a`) and `bB` (`𝔫_b`);
* `pairBranch`: `Fin 2 ⊕ (Gi ⊕ (Gr ⊕ Gg))` branches `≃` branches of `G` (`pairBranch_bijective`);
* `prod_pairBranch`: products over the branches of `G` split; `order_pair`, `zeta_pair`, `epsDec_pair`,
  `phaseProd_pair`;
* `lt_up_of_chain`: a generic upper-clock propagation along tree paths. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The data of a closing pair and its pieces.** -/
structure PairData (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (G Gi : Garden 1)
    (Gr Gg : Garden 2) : Prop where
  decZ : (RegChain.pair m Qr Qg inner .nil).DecodesTree G
  decI : inner.DecodesTree Gi
  sigI : Gi.sig 0 = slotSign (G.sig 0) m.c
  decR : Qr.Decodes Gr
  decG : Qg.Decodes Gg

namespace PairData

variable {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {G Gi : Garden 1} {Gr Gg : Garden 2}
variable (h : PairData m Qr Qg inner G Gi Gr Gg)
include h

theorem tree0 : G.tree 0 = pairTree m Qr Qg inner (G.sig 0) := h.decZ.1

theorem treeI : Gi.tree 0 = inner.plug (slotSign (G.sig 0) m.c) .leaf := by
  rw [h.decI.1, h.sigI]

theorem treeR (j : Fin 2) : Gr.tree j = rTree Qr j := by
  fin_cases j
  · exact h.decR.2.1
  · exact h.decR.2.2.1

theorem treeG (j : Fin 2) : Gg.tree j = rTree Qg j := by
  fin_cases j
  · exact h.decG.2.1
  · exact h.decG.2.2.1

omit h in
theorem not_lonePath_prefix_of_branching {X : RegChain} {ζ : ℤˣ} {q : Path}
    (hq : q ∈ (X.plug ζ .leaf).branching) : ¬ X.lonePath <+: q := by
  intro hpre
  have := plug_leaf_prefix X ζ (TTree.branching_subset_nodes _ hq) hpre
  subst this
  exact TTree.not_mem_branching_of_mem_leaves _ (lonePath_mem_leaves X ζ) hq

/-! ### Node and branch maps -/

/-- The interior piece, placed below `[m.c]` (its lone leaf goes to `𝔫_b`). -/
def ιi (z : GNode Gi.tree) : GNode G.tree :=
  ⟨((0 : Fin 1), m.c :: z.1.2), by
    have hz := z.2
    rw [show z.1.1 = 0 from Subsingleton.elim _ _, h.treeI] at hz
    show m.c :: z.1.2 ∈ (G.tree 0).nodes
    rw [h.tree0]
    by_cases hp : inner.lonePath <+: z.1.2
    · rw [plug_leaf_prefix inner _ hz hp, ← bPath_eq]
      exact TTree.branching_subset_nodes _ (bPath_mem_branching m Qr Qg inner _)
    · exact (mem_pairTree_inner m Qr Qg inner _ _ hp).1.mpr hz⟩

/-- The red couple, placed at `rBase`. -/
def ιr (z : GNode Gr.tree) : GNode G.tree :=
  ⟨((0 : Fin 1), rBase m inner (G.sig 0) z.1.1 ++ z.1.2), by
    have hz := z.2
    rw [h.treeR] at hz
    show _ ∈ (G.tree 0).nodes
    rw [h.tree0]
    exact (memT_rBase m Qr Qg inner _ z.1.1 z.1.2).1.mpr hz⟩

/-- The green couple, placed at `gBase`. -/
def ιg (z : GNode Gg.tree) : GNode G.tree :=
  ⟨((0 : Fin 1), gBase m inner (G.sig 0) z.1.1 ++ z.1.2), by
    have hz := z.2
    rw [h.treeG] at hz
    show _ ∈ (G.tree 0).nodes
    rw [h.tree0]
    exact (memT_gBase m Qr Qg inner _ z.1.1 z.1.2).1.mpr hz⟩

def βi (x : GBranch Gi.tree) : GBranch G.tree :=
  ⟨((0 : Fin 1), m.c :: x.1.2), by
    have hx := x.2
    rw [show x.1.1 = 0 from Subsingleton.elim _ _, h.treeI] at hx
    show m.c :: x.1.2 ∈ (G.tree 0).branching
    rw [h.tree0]
    exact (mem_pairTree_inner m Qr Qg inner _ _ (not_lonePath_prefix_of_branching hx)).2.2.mpr hx⟩

def βr (y : GBranch Gr.tree) : GBranch G.tree :=
  ⟨((0 : Fin 1), rBase m inner (G.sig 0) y.1.1 ++ y.1.2), by
    have hy := y.2
    rw [h.treeR] at hy
    show _ ∈ (G.tree 0).branching
    rw [h.tree0]
    exact (memT_rBase m Qr Qg inner _ y.1.1 y.1.2).2.2.mpr hy⟩

def βg (y : GBranch Gg.tree) : GBranch G.tree :=
  ⟨((0 : Fin 1), gBase m inner (G.sig 0) y.1.1 ++ y.1.2), by
    have hy := y.2
    rw [h.treeG] at hy
    show _ ∈ (G.tree 0).branching
    rw [h.tree0]
    exact (memT_gBase m Qr Qg inner _ y.1.1 y.1.2).2.2.mpr hy⟩

/-- The root `𝔫_a`. -/
def rootB : GBranch G.tree :=
  ⟨((0 : Fin 1), []), by show [] ∈ (G.tree 0).branching; rw [h.tree0]; exact nil_mem_pairTree_branching _ _ _ _ _⟩

/-- The terminal node `𝔫_b`. -/
def bB : GBranch G.tree :=
  ⟨((0 : Fin 1), bPath m inner), by
    show _ ∈ (G.tree 0).branching; rw [h.tree0]; exact bPath_mem_branching _ _ _ _ _⟩

theorem βi_toNode (x : GBranch Gi.tree) : (h.βi x).toNode = h.ιi x.toNode := rfl
theorem βr_toNode (y : GBranch Gr.tree) : (h.βr y).toNode = h.ιr y.toNode := rfl
theorem βg_toNode (y : GBranch Gg.tree) : (h.βg y).toNode = h.ιg y.toNode := rfl

theorem βi_child (x : GBranch Gi.tree) (k : Fin 3) : (h.βi x).child k = h.ιi (x.child k) := rfl

theorem βr_child (y : GBranch Gr.tree) (k : Fin 3) : (h.βr y).child k = h.ιr (y.child k) := by
  apply Subtype.ext
  show ((0 : Fin 1), (rBase m inner (G.sig 0) y.1.1 ++ y.1.2) ++ [k]) =
    ((0 : Fin 1), rBase m inner (G.sig 0) y.1.1 ++ (y.1.2 ++ [k]))
  rw [List.append_assoc]

theorem βg_child (y : GBranch Gg.tree) (k : Fin 3) : (h.βg y).child k = h.ιg (y.child k) := by
  apply Subtype.ext
  show ((0 : Fin 1), (gBase m inner (G.sig 0) y.1.1 ++ y.1.2) ++ [k]) =
    ((0 : Fin 1), gBase m inner (G.sig 0) y.1.1 ++ (y.1.2 ++ [k]))
  rw [List.append_assoc]

/-! ### The branch bijection -/

/-- **The branches of a closing pair**: the two cut nodes and the branches of the three pieces. -/
def pairBranch : Fin 2 ⊕ (GBranch Gi.tree ⊕ (GBranch Gr.tree ⊕ GBranch Gg.tree)) → GBranch G.tree
  | .inl j => if j = 0 then h.rootB else h.bB
  | .inr (.inl x) => h.βi x
  | .inr (.inr (.inl y)) => h.βr y
  | .inr (.inr (.inr y)) => h.βg y

/-- The region of each branch. -/
def pairBranchReg : Fin 2 ⊕ (GBranch Gi.tree ⊕ (GBranch Gr.tree ⊕ GBranch Gg.tree)) → PReg
  | .inl j => if j = 0 then .root else .bnode
  | .inr (.inl _) => .inner
  | .inr (.inr (.inl y)) => .red y.1.1
  | .inr (.inr (.inr y)) => .green y.1.1

theorem regionOf_pairBranch (z : Fin 2 ⊕ (GBranch Gi.tree ⊕ (GBranch Gr.tree ⊕ GBranch Gg.tree))) :
    regionOf m inner (G.sig 0) (h.pairBranch z).1.2 = pairBranchReg z := by
  rcases z with j | x | y | y
  · fin_cases j
    · exact regionOf_nil m inner _
    · exact regionOf_bPath m inner _
  · have hx := x.2
    rw [show x.1.1 = 0 from Subsingleton.elim _ _, h.treeI] at hx
    exact regionOf_inner m inner _ _ (not_lonePath_prefix_of_branching hx)
  · exact regionOf_rBase m inner _ _ _
  · exact regionOf_gBase m inner _ _ _

theorem pairBranch_injective : Function.Injective h.pairBranch := by
  intro z z' he
  have hr := h.regionOf_pairBranch z
  rw [he, h.regionOf_pairBranch z'] at hr
  have hp : (h.pairBranch z).1.2 = (h.pairBranch z').1.2 := by rw [he]
  rcases z with j | x | y | y <;> rcases z' with j' | x' | y' | y'
  · fin_cases j <;> fin_cases j' <;> first | rfl | (simp [pairBranchReg] at hr)
  · fin_cases j <;> simp [pairBranchReg] at hr
  · fin_cases j <;> simp [pairBranchReg] at hr
  · fin_cases j <;> simp [pairBranchReg] at hr
  · fin_cases j' <;> simp [pairBranchReg] at hr
  · change m.c :: x.1.2 = m.c :: x'.1.2 at hp
    have hx : x.1.2 = x'.1.2 := List.cons_injective hp
    congr 2
    exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) hx)
  · simp [pairBranchReg] at hr
  · simp [pairBranchReg] at hr
  · fin_cases j' <;> simp [pairBranchReg] at hr
  · simp [pairBranchReg] at hr
  · have hj : y.1.1 = y'.1.1 := by simp [pairBranchReg] at hr; exact hr.symm
    change rBase m inner (G.sig 0) y.1.1 ++ y.1.2 = rBase m inner (G.sig 0) y'.1.1 ++ y'.1.2 at hp
    rw [hj] at hp
    congr 3
    exact Subtype.ext (Prod.ext hj (List.append_cancel_left hp))
  · simp [pairBranchReg] at hr
  · fin_cases j' <;> simp [pairBranchReg] at hr
  · simp [pairBranchReg] at hr
  · simp [pairBranchReg] at hr
  · have hj : y.1.1 = y'.1.1 := by simp [pairBranchReg] at hr; exact hr.symm
    change gBase m inner (G.sig 0) y.1.1 ++ y.1.2 = gBase m inner (G.sig 0) y'.1.1 ++ y'.1.2 at hp
    rw [hj] at hp
    congr 3
    exact Subtype.ext (Prod.ext hj (List.append_cancel_left hp))

theorem pairBranch_surjective : Function.Surjective h.pairBranch := by
  intro b
  obtain ⟨⟨j, p⟩, hb⟩ := b
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have hb' : p ∈ (pairTree m Qr Qg inner (G.sig 0)).branching := by rw [← h.tree0]; exact hb
  rcases pairTree_cases m inner (G.sig 0) Qr Qg p (TTree.branching_subset_nodes _ hb') with
    rfl | rfl | rfl | ⟨q, rfl, hq, -⟩ | ⟨j, q, rfl, -⟩ | ⟨j, q, rfl, -⟩
  · exact ⟨.inl 0, rfl⟩
  · exact ⟨.inl 1, rfl⟩
  · exact absurd hb' (TTree.not_mem_branching_of_mem_leaves _ (lonePos_mem_leaves m Qr Qg inner _))
  · have hq' : q ∈ (Gi.tree 0).branching := by
      rw [h.treeI]; exact (mem_pairTree_inner m Qr Qg inner _ q hq).2.2.mp hb'
    exact ⟨.inr (.inl ⟨((0 : Fin 1), q), hq'⟩), rfl⟩
  · have hq' : q ∈ (Gr.tree j).branching := by
      rw [h.treeR]; exact (memT_rBase m Qr Qg inner _ j q).2.2.mp hb'
    exact ⟨.inr (.inr (.inl ⟨(j, q), hq'⟩)), rfl⟩
  · have hq' : q ∈ (Gg.tree j).branching := by
      rw [h.treeG]; exact (memT_gBase m Qr Qg inner _ j q).2.2.mp hb'
    exact ⟨.inr (.inr (.inr ⟨(j, q), hq'⟩)), rfl⟩

theorem pairBranch_bijective : Function.Bijective h.pairBranch :=
  ⟨h.pairBranch_injective, h.pairBranch_surjective⟩

/-- **Products over the branches of a closing pair.** -/
theorem prod_pairBranch {M : Type*} [CommMonoid M] (f : GBranch G.tree → M) :
    ∏ b, f b = f h.rootB * f h.bB * ((∏ x, f (h.βi x)) * ((∏ y, f (h.βr y)) * ∏ y, f (h.βg y))) := by
  rw [← (Equiv.ofBijective _ h.pairBranch_bijective).prod_comp]
  simp only [Fintype.prod_sum_type, Equiv.ofBijective_apply, Fin.prod_univ_two]
  rfl

/-! ### Signs, orders, `ζ`, `ε`, phases -/

theorem sign_ιi (z : GNode Gi.tree) : G.sign (h.ιi z) = Gi.sign z := by
  show pathSign (G.sig 0) (m.c :: z.1.2) = pathSign (Gi.sig z.1.1) z.1.2
  rw [show z.1.1 = 0 from Subsingleton.elim _ _, h.sigI, show m.c :: z.1.2 = [m.c] ++ z.1.2 from rfl,
    Comb.pathSign_append, pathSign_singleton]

theorem sign_rBase (j : Fin 2) :
    pathSign (G.sig 0) (rBase m inner (G.sig 0) j) = Gr.sig j := by
  have hs : Gr.sig = ![1, -1] := h.decR.1.2
  rw [hs]
  have hbot : pathSign (G.sig 0) (bPath m inner ++ [m.red.2]) = -slotSign (G.sig 0) m.red.1 := by
    rw [bPath, Comb.pathSign_append, Comb.pathSign_append, pathSign_singleton, lonePath_sign,
      pathSign_singleton, slotSign_red]
  unfold rBase
  by_cases hs1 : slotSign (G.sig 0) m.red.1 = 1 <;> fin_cases j
  · simp [hs1, pathSign_singleton]
  · simp [hs1, hbot]
  · simp [hs1, hbot, neg_units_eq_one hs1]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, hs1, eq_iff_iff, false_iff, not_false_eq_true,
      ite_true, pathSign_singleton, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rcases Int.units_eq_one_or (slotSign (G.sig 0) m.red.1) with h1 | h1
    · exact absurd h1 hs1
    · exact h1

theorem sign_gBase (j : Fin 2) :
    pathSign (G.sig 0) (gBase m inner (G.sig 0) j) = Gg.sig j := by
  have hs : Gg.sig = ![1, -1] := h.decG.1.2
  rw [hs]
  have hbot : pathSign (G.sig 0) (bPath m inner ++ [m.green.2]) = -slotSign (G.sig 0) m.green.1 := by
    rw [bPath, Comb.pathSign_append, Comb.pathSign_append, pathSign_singleton, lonePath_sign,
      pathSign_singleton, slotSign_green]
  unfold gBase
  by_cases hs1 : slotSign (G.sig 0) m.green.1 = 1 <;> fin_cases j
  · simp [hs1, pathSign_singleton]
  · simp [hs1, hbot]
  · simp [hs1, hbot, neg_units_eq_one hs1]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, hs1, eq_iff_iff, false_iff, not_false_eq_true,
      ite_true, pathSign_singleton, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rcases Int.units_eq_one_or (slotSign (G.sig 0) m.green.1) with h1 | h1
    · exact absurd h1 hs1
    · exact h1

theorem sign_ιr (z : GNode Gr.tree) : G.sign (h.ιr z) = Gr.sign z := by
  show pathSign (G.sig 0) (rBase m inner (G.sig 0) z.1.1 ++ z.1.2) = pathSign (Gr.sig z.1.1) z.1.2
  rw [Comb.pathSign_append, h.sign_rBase]

theorem sign_ιg (z : GNode Gg.tree) : G.sign (h.ιg z) = Gg.sign z := by
  show pathSign (G.sig 0) (gBase m inner (G.sig 0) z.1.1 ++ z.1.2) = pathSign (Gg.sig z.1.1) z.1.2
  rw [Comb.pathSign_append, h.sign_gBase]

omit h in
theorem card_branch {w : ℕ} (G' : Garden w) : Fintype.card (GBranch G'.tree) = G'.order := by
  rw [Comb.card_gbranch]; rfl

theorem order_pair : G.order = Gi.order + Gr.order + Gg.order + 2 := by
  rw [← card_branch, ← card_branch, ← card_branch, ← card_branch,
    ← Fintype.card_congr (Equiv.ofBijective _ h.pairBranch_bijective)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem zeta_pair : G.zeta = (Complex.I * ((G.sign h.rootB.toNode : ℤˣ) : ℤ)) *
    (Complex.I * ((G.sign h.bB.toNode : ℤˣ) : ℤ)) * (Gi.zeta * (Gr.zeta * Gg.zeta)) := by
  unfold Garden.zeta
  rw [h.prod_pairBranch]
  simp only [βi_toNode, βr_toNode, βg_toNode, sign_ιi, sign_ιr, sign_ιg]

theorem epsDec_pair {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) :
    epsDec G κ = epsCoef (κ (h.rootB.child 0)) (κ (h.rootB.child 1)) (κ (h.rootB.child 2)) *
      epsCoef (κ (h.bB.child 0)) (κ (h.bB.child 1)) (κ (h.bB.child 2)) *
      (epsDec Gi (κ ∘ h.ιi) * (epsDec Gr (κ ∘ h.ιr) * epsDec Gg (κ ∘ h.ιg))) := by
  unfold epsDec
  rw [h.prod_pairBranch]
  simp only [βi_child, βr_child, βg_child, Function.comp_apply]

theorem phaseProd_pair (L γ δ : ℝ) {d : ℕ} (K : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    phaseProd L γ δ G K τ =
      Complex.exp ((Real.pi * ((G.sign h.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode G K h.rootB * τ h.rootB : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((G.sign h.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode G K h.bB * τ h.bB : ℝ) * Complex.I) *
        (phaseProd L γ δ Gi (K ∘ h.ιi) (fun x => τ (h.βi x)) *
          (phaseProd L γ δ Gr (K ∘ h.ιr) (fun y => τ (h.βr y)) *
            phaseProd L γ δ Gg (K ∘ h.ιg) (fun y => τ (h.βg y)))) := by
  unfold phaseProd
  rw [h.prod_pairBranch]
  simp only [omegaNode, βi_child, βr_child, βg_child, βi_toNode, βr_toNode, βg_toNode, sign_ιi, sign_ιr,
    sign_ιg, Function.comp_apply]

end PairData

/-! ### Upper clocks along tree paths -/

/-- **Upper-clock propagation**: if consecutive branches decrease in time (whenever one is free), roots are below
the bound of their tree and designated times are at most that bound, every free branch is below it. -/
theorem lt_up_of_chain {w : ℕ} {T : Fin w → TTree} (fix : GBranch T → Option ℝ) (τ : GBranch T → ℝ)
    (U : Fin w → ℝ)
    (hchild : ∀ b b' : GBranch T, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b)
    (hroot : ∀ b : GBranch T, b.1.2 = [] → fix b = none → τ b < U b.1.1)
    (hpin : ∀ b σ, fix b = some σ → τ b = σ ∧ σ ≤ U b.1.1) :
    ∀ b : GBranch T, fix b = none → τ b < U b.1.1 := by
  have key : ∀ (n : ℕ) (b : GBranch T), b.1.2.length = n → τ b ≤ U b.1.1 ∧ (fix b = none → τ b < U b.1.1) := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have hb0 : b.1.2 = [] := List.eq_nil_of_length_eq_zero hb
      cases hf : fix b with
      | none => have := hroot b hb0 hf; exact ⟨this.le, fun _ => this⟩
      | some σ => obtain ⟨h1, h2⟩ := hpin b σ hf; exact ⟨h1 ▸ h2, fun h => by simp at h⟩
    | succ n ih =>
      intro b hb
      obtain ⟨⟨j, p⟩, hbm⟩ := b
      rcases List.eq_nil_or_concat p with hp | ⟨q, k, rfl⟩
      · subst hp; simp at hb
      have hq : q ∈ (T j).branching :=
        TTree.branching_of_append_mem _ (TTree.branching_subset_nodes _ (by simpa using hbm))
      let par : GBranch T := ⟨(j, q), hq⟩
      have hpar := ih par (by simpa [par] using hb)
      have hc : GBranch.IsChildOf (⟨(j, q.concat k), hbm⟩ : GBranch T) par := ⟨rfl, k, by simp [par]⟩
      have hpar' : τ par ≤ U j := hpar.1
      cases hf : fix (⟨(j, q.concat k), hbm⟩ : GBranch T) with
      | none =>
        have := hchild par _ hc (Or.inl hf)
        exact ⟨(this.trans_le hpar').le, fun _ => this.trans_le hpar'⟩
      | some σ =>
        obtain ⟨h1, h2⟩ := hpin _ σ hf
        exact ⟨h1 ▸ h2, fun h => by simp at h⟩
  exact fun b hb => (key _ b rfl).2 hb

end WaveTurbulence.Flower.ProtCut

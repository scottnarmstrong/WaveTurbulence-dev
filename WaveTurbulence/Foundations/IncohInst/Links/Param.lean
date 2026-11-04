/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Construct5
public import WaveTurbulence.Foundations.IncohInst.Links.Omega
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-!
# The unimodular change of variables `(k_ℓ) ↔ (x_𝔫, y_𝔫)_{𝔫 ∈ 𝒩^ch}` (packet C2)

TARGET (incohproof1)–(incohproof2) (L983–L995): for a couple carrier `G` decoded by `Q` with
`n(𝒬) = 2n`, the decorations of `G` with root value `r` (in any additive group: `ℤ^d` for lattice
indices, `ℝ^d` for vectors) are in bijection with `(V × V)^n`, one pair `(x_𝔫, y_𝔫)` per link,
read at its chosen node `𝔫 ∈ 𝒩^ch` (`decEquiv`). Every node value is `r` plus a fixed integer
linear combination of the `x_𝔫, y_𝔫`, the same for every group (`node_linear`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V]

/-- The chosen node of the `j`-th link. -/
def chosenNode (Q : RegCpl) (j : Fin Q.links.length) : Fin 2 × Path := (Q.links.get j).1

theorem chosen_nodup (Q : RegCpl) : (Q.links.map Prod.fst).Nodup := by
  have hnd := couple_links_flat_nodup Q
  refine List.Nodup.sublist ?_ hnd
  clear hnd
  induction Q.links with
  | nil => simp [flatPairs]
  | cons p L ih =>
    simp only [List.map_cons, flatPairs, List.flatMap_cons, List.cons_append] at ih ⊢
    exact List.Sublist.cons_cons _ (List.Sublist.cons _ ih)

/-- The parameters as a function of addresses (zero away from `𝒩^ch`). -/
def paramFun (Q : RegCpl) (θ : Fin Q.links.length → V × V) (z : Fin 2 × Path) : V × V :=
  if h : (Q.links.map Prod.fst).idxOf z < Q.links.length then θ ⟨_, h⟩ else 0

theorem paramFun_chosen (Q : RegCpl) (θ : Fin Q.links.length → V × V) (j : Fin Q.links.length) :
    paramFun Q θ (chosenNode Q j) = θ j := by
  have hidx : (Q.links.map Prod.fst).idxOf (chosenNode Q j) = j := by
    have := (chosen_nodup Q).idxOf_getElem j (by simp)
    simpa [chosenNode] using this
  unfold paramFun
  rw [dite_cond_eq_true (eq_true (by rw [hidx]; exact j.2))]
  congr 1
  exact Fin.ext hidx

theorem indep_roots : Indep ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) :=
  ⟨fun h => by simp [Under] at h, fun h => by simp [Under] at h⟩

/-- The decorations of `G` with root value `r` (TARGET Def `defdec`, with `k_{𝔯^±} = r`). -/
def DecR (G : Garden 2) (V : Type*) [AddCommGroup V] (r : V) : Type _ :=
  {κ : GNode G.tree → V // IsDecoration G κ ∧ ∀ j, κ (GNode.root G.tree j) = r}

variable {G : Garden 2} {Q : RegCpl}

theorem mem_nodes_iff_endpoints (hQ : Q.Decodes G) (x : Fin 2 × Path) :
    x.2 ∈ (G.tree x.1).nodes ↔ x ∈ pairEndpoints Q.links ∪ pairEndpoints Q.raw.2 := by
  rw [Finset.mem_union, mem_pairEndpoints_links_iff hQ, Comb.TreePath.mem_nodes_iff]
  have hl : x ∈ pairEndpoints Q.raw.2 ↔ x.2 ∈ (G.tree x.1).leaves := by
    rw [tree_eq_coupleForest hQ, ← coupleForest_leaf_iff, couple_leafAddresses]; rfl
  rw [hl]; tauto

/-- `x_𝔫` and `y_𝔫` of `extend` of a restriction only read node values. -/
theorem xv_extend_restrict (hQ : Q.Decodes G) (g : Fin 2 × Path → V) {x : Fin 2 × Path}
    (hx : x.2 ∈ (G.tree x.1).branching) :
    xv (extend (fun a : GNode G.tree => g a.1)) x = xv g x ∧
      yv (extend (fun a : GNode G.tree => g a.1)) x = yv g x := by
  have b : GBranch G.tree := ⟨x, hx⟩
  constructor
  · have := xv_extend (fun a : GNode G.tree => g a.1) ⟨x, hx⟩
    rw [this]; rfl
  · have := yv_extend (fun a : GNode G.tree => g a.1) ⟨x, hx⟩
    rw [this]; rfl

/-- The link parameters of a decoration. -/
def decParams (_hQ : Q.Decodes G) {r : V} (κ : DecR G V r) : Fin Q.links.length → V × V :=
  fun j => (xv (extend κ.1) (chosenNode Q j), yv (extend κ.1) (chosenNode Q j))

/-- The decoration with root value `r` and given link parameters. -/
def decOfParams (hQ : Q.Decodes G) (r : V) (θ : Fin Q.links.length → V × V) : DecR G V r :=
  ⟨fun a => cplVal (paramFun Q θ) Q (0, []) (1, []) r a.1,
    isDecoration_of_cplDec hQ (cplDec_cplVal _ Q _ _ r indep_roots), fun j => by
      fin_cases j
      · exact (cplVal_root _ Q _ _ r indep_roots).1
      · exact (cplVal_root _ Q _ _ r indep_roots).2⟩

theorem chosenNode_mem (Q : RegCpl) (j : Fin Q.links.length) :
    (Q.links.get j, chosenNode Q j) = (Q.links.get j, (Q.links.get j).1) := rfl

/-- **The unimodular change of variables** (TARGET (incohproof1)): decorations with root value `r`
correspond bijectively to the link parameters `(x_𝔫, y_𝔫)_{𝔫 ∈ 𝒩^ch}`. -/
def decEquiv (hQ : Q.Decodes G) (hG : IsCouple G) (r : V) :
    DecR G V r ≃ (Fin Q.links.length → V × V) where
  toFun := decParams hQ
  invFun := decOfParams hQ r
  left_inv κ := by
    apply Subtype.ext
    funext a
    have hd := cplDec_of_decoration hQ κ.2.1
    have hr : extend κ.1 ((0 : Fin 2), ([] : Path)) = r :=
      (extend_node κ.1 (GNode.root G.tree 0)).trans (κ.2.2 0)
    have hθ : ∀ l ∈ Q.links, xv (extend κ.1) l.1 = (paramFun Q (decParams hQ κ) l.1).1 ∧
        yv (extend κ.1) l.1 = (paramFun Q (decParams hQ κ) l.1).2 := by
      intro l hl
      obtain ⟨j, rfl⟩ := List.get_of_mem hl
      rw [show (Q.links.get j).1 = chosenNode Q j from rfl, paramFun_chosen]
      exact ⟨rfl, rfl⟩
    have := cplDec_determined (paramFun Q (decParams hQ κ)) Q _ _ r indep_roots (extend κ.1) hd hr hθ
      a.1 ((mem_nodes_iff_endpoints hQ a.1).1 a.2)
    rw [extend_node] at this
    exact this.symm
  right_inv θ := by
    funext j
    have hl : Q.links.get j ∈ Q.links := List.get_mem _ _
    have hb := (link_branching hQ hl).1
    have hp := cplVal_params (paramFun Q θ) Q _ _ r indep_roots _ (fun _ _ => rfl) _ hl
    obtain ⟨e1, e2⟩ := xv_extend_restrict hQ (cplVal (paramFun Q θ) Q (0, []) (1, []) r) hb
    simp only [decParams, decOfParams, chosenNode]
    rw [e1, e2, hp.1, hp.2, show (Q.links.get j).1 = chosenNode Q j from rfl, paramFun_chosen]

/-- The parameters of the decoration built from `θ` are `θ`. -/
theorem decParams_decOfParams (hQ : Q.Decodes G) (hG : IsCouple G) (r : V)
    (θ : Fin Q.links.length → V × V) : decParams hQ (decOfParams hQ r θ) = θ :=
  (decEquiv hQ hG r).right_inv θ

end WaveTurbulence.Links

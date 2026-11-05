/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceLeafProducts

/-! # Literal chain leaf products and the dominant consecutive-pair recursion -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- The actual chain leaf-pair product, excluding the lone continuation input. -/
def chainLeafProduct (F : V → ℂ) (θ : Fin w × Path → V × V)
    (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) : ℂ :=
  ((X.pairsAt ζ a).map (fun p => F (chainVal θ X ζ a u cont p.1))).prod

@[simp] theorem chainLeafProduct_nil (F : V → ℂ) (θ : Fin w × Path → V × V)
    (ζ : ℤˣ) (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    chainLeafProduct F θ .nil ζ a u cont = 1 := rfl

/-- Chain pair endpoints lie above the lone continuation region. -/
theorem chain_pair_fst_region (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (p : (Fin w × Path) × (Fin w × Path)) (hp : p ∈ X.pairsAt ζ a) :
    Under a p.1 ∧ ¬ SUnder (addrExt a X.lonePath) p.1 :=
  chain_endpoints_region X ζ a p.1 (Finset.mem_union_right _
    ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩))

/-- The red source factors are precisely the child couple product with
its sign-determined placement, before any singular integration. -/
theorem chain_red_leaf_product (F : V → ℂ) (θ : Fin w × Path → V × V)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    ((if slotSign ζ m.red.1 = 1 then
        Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])).map
      (fun p => F (chainVal θ (.pair m Qr Qg inner rest) ζ a u cont p.1))).prod =
      if slotSign ζ m.red.1 = 1 then
        cplLeafProduct F θ Qr (addrExt a [m.red.1])
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (childVals u (θ a) m.red.1)
      else cplLeafProduct F θ Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1]) (childVals u (θ a) m.red.1) := by
  simp only [cplLeafProduct]
  split_ifs with hr
  · apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    simpa only [hr,ite_true] using (chain_dispatch θ m Qr Qg inner rest ζ a u cont p.1).1
      (cpl_pair_fst_under Qr _ _ p hp)
  · apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    simpa only [hr,ite_false] using (chain_dispatch θ m Qr Qg inner rest ζ a u cont p.1).1
      (cpl_pair_fst_under Qr _ _ p hp).symm

/-- The green source factors have the analogous original sign-dependent placement. -/
theorem chain_green_leaf_product (F : V → ℂ) (θ : Fin w × Path → V × V)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    ((if slotSign ζ m.green.1 = 1 then
        Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])).map
      (fun p => F (chainVal θ (.pair m Qr Qg inner rest) ζ a u cont p.1))).prod =
      if slotSign ζ m.green.1 = 1 then
        cplLeafProduct F θ Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (childVals u (θ a) m.green.1)
      else cplLeafProduct F θ Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1]) (childVals u (θ a) m.green.1) := by
  simp only [cplLeafProduct]
  split_ifs with hg
  · apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    simpa only [hg,ite_true] using (chain_dispatch θ m Qr Qg inner rest ζ a u cont p.1).2.1
      (cpl_pair_fst_under Qg _ _ p hp)
  · apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    simpa only [hg,ite_false] using (chain_dispatch θ m Qr Qg inner rest ζ a u cont p.1).2.1
      (cpl_pair_fst_under Qg _ _ p hp).symm

/-- The rest of a source chain retains the original root momentum. -/
theorem chain_rest_leaf_product (F : V → ℂ) (θ : Fin w × Path → V × V)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    ((rest.pairsAt (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))).map
      (fun p => F (chainVal θ (.pair m Qr Qg inner rest) ζ a u cont p.1))).prod =
      chainLeafProduct F θ rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) u cont := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  apply congrArg F
  exact (chain_dispatch θ m Qr Qg inner rest ζ a u cont p.1).2.2.1
    (chain_pair_fst_region rest _ _ p hp).1

/-- The inner source factors are evaluated at the actual child-c momentum;
this factor is empty for dominant chains. -/
theorem chain_inner_leaf_product (F : V → ℂ) (θ : Fin w × Path → V × V)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    ((inner.pairsAt (slotSign ζ m.c) (addrExt a [m.c])).map
      (fun p => F (chainVal θ (.pair m Qr Qg inner rest) ζ a u cont p.1))).prod =
      chainLeafProduct F θ inner (slotSign ζ m.c) (addrExt a [m.c])
        (childVals u (θ a) m.c) (fun _ => childVals u (θ a) m.c) := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  apply congrArg F
  have hr := chain_pair_fst_region inner (slotSign ζ m.c) (addrExt a [m.c]) p hp
  exact (chain_dispatch θ m Qr Qg inner rest ζ a u cont p.1).2.2.2 hr.1
    (by simpa only [addrExt_append] using hr.2)

/-- Full literal source chain factorization, before imposing dominance.
The inner factors retain their child-c momentum. -/
theorem chainLeafProduct_pair (F : V → ℂ) (θ : Fin w × Path → V × V)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    chainLeafProduct F θ (.pair m Qr Qg inner rest) ζ a u cont =
      (if slotSign ζ m.red.1 = 1 then
        cplLeafProduct F θ Qr (addrExt a [m.red.1])
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (childVals u (θ a) m.red.1)
      else cplLeafProduct F θ Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1]) (childVals u (θ a) m.red.1)) *
      (if slotSign ζ m.green.1 = 1 then
        cplLeafProduct F θ Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (childVals u (θ a) m.green.1)
      else cplLeafProduct F θ Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1]) (childVals u (θ a) m.green.1)) *
      chainLeafProduct F θ inner (slotSign ζ m.c) (addrExt a [m.c])
        (childVals u (θ a) m.c) (fun _ => childVals u (θ a) m.c) *
      chainLeafProduct F θ rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) u cont := by
  have hr := chain_red_leaf_product F θ m Qr Qg inner rest ζ a u cont
  have hg := chain_green_leaf_product F θ m Qr Qg inner rest ζ a u cont
  have hi := chain_inner_leaf_product F θ m Qr Qg inner rest ζ a u cont
  have ht := chain_rest_leaf_product F θ m Qr Qg inner rest ζ a u cont
  simp only [chainLeafProduct,RegChain.pairsAt,List.map_append,List.prod_append] at hr hg hi ht ⊢
  rw [hr,hg,hi,ht]

/-- Literal consecutive-pair source recursion. Dominance guarantees this
inner=nil shape; no claim is made here for nested non-dominant pairs. -/
theorem chainLeafProduct_pair_nil (F : V → ℂ) (θ : Fin w × Path → V × V)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (cont : Fin w × Path → V) :
    chainLeafProduct F θ (.pair m Qr Qg .nil rest) ζ a u cont =
      (if slotSign ζ m.red.1 = 1 then
        cplLeafProduct F θ Qr (addrExt a [m.red.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2])) (childVals u (θ a) m.red.1)
      else cplLeafProduct F θ Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1]) (childVals u (θ a) m.red.1)) *
      (if slotSign ζ m.green.1 = 1 then
        cplLeafProduct F θ Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2])) (childVals u (θ a) m.green.1)
      else cplLeafProduct F θ Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1]) (childVals u (θ a) m.green.1)) *
      chainLeafProduct F θ rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) u cont := by
  have hr := chain_red_leaf_product F θ m Qr Qg .nil rest ζ a u cont
  have hg := chain_green_leaf_product F θ m Qr Qg .nil rest ζ a u cont
  have ht := chain_rest_leaf_product F θ m Qr Qg .nil rest ζ a u cont
  simp only [chainLeafProduct,RegChain.pairsAt,List.append_nil,List.map_append,List.prod_append] at hr hg ht ⊢
  rw [hr,hg,ht]

/-- The excluded lone input is the only place where the continuation can
enter; all actual paired leaf factors are independent of that continuation. -/
theorem chainLeafProduct_cont_independent (F : V → ℂ) (θ : Fin w × Path → V × V)
    (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V)
    (cont₁ cont₂ : Fin w × Path → V) :
    chainLeafProduct F θ X ζ a u cont₁ = chainLeafProduct F θ X ζ a u cont₂ := by
  cases X with
  | nil => rfl
  | pair m Qr Qg inner rest =>
    rw [chainLeafProduct_pair,chainLeafProduct_pair,
      chainLeafProduct_cont_independent F θ rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) u cont₁ cont₂]
termination_by structural X

end WaveTurbulence.RegAsymp

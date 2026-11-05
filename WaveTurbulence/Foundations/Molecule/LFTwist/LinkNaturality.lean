/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch
public import WaveTurbulence.Foundations.Molecule.LeafInsertion

/-! # Exact local transport of the source coherence links -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

mutual
/-- Couple link decoding commutes with address transport local to its two roots. -/
theorem couple_linksAt_map_local {w v : ℕ} (Q : RegCpl)
    (f : (Fin w × Path) → (Fin v × Path)) (a b : Fin w × Path)
    (ha : RespectsAt f a) (hb : RespectsAt f b) :
    Q.linksAt (f a) (f b) = (Q.linksAt a b).map (fun p => (f p.1,f p.2)) := by
  have hA : ∀ p, f (addrExt a p) = addrExt (f a) p := ha
  have hB : ∀ p, f (addrExt b p) = addrExt (f b) p := hb
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    have hr := couple_linksAt_map_local r f _ _ (ha.child [0]) (hb.child [c.partner 0])
    have hg := couple_linksAt_map_local g f _ _ (hb.child [1]) (ha.child [1])
    have hd := couple_linksAt_map_local d f _ _ (ha.child [2]) (hb.child [c.partner 2])
    simp only [RegCpl.linksAt,List.map_cons,List.map_append,← hA,← hB,hr,hg,hd]
  | type2 p m q =>
    have hp := chain_linksAt_map_local p f a ha 1
    have hm := chain_linksAt_map_local m f b hb (-1)
    have hq := couple_linksAt_map_local q f _ _ (ha.child p.lonePath) (hb.child m.lonePath)
    simp only [RegCpl.linksAt,List.map_cons,List.map_append,← hA,← hB,hp,hm,hq]
termination_by structural Q

/-- Chain link decoding needs address compatibility only below its original root. -/
theorem chain_linksAt_map_local {w v : ℕ} (X : RegChain)
    (f : (Fin w × Path) → (Fin v × Path)) (a : Fin w × Path)
    (ha : RespectsAt f a) (ζ : ℤˣ) :
    X.linksAt ζ (f a) = (X.linksAt ζ a).map (fun p => (f p.1,f p.2)) := by
  have hA : ∀ p, f (addrExt a p) = addrExt (f a) p := ha
  cases X with
  | nil => rfl
  | pair m r g i s =>
    have hR : ∀ p q, r.linksAt (f (addrExt a p)) (f (addrExt a q)) =
        (r.linksAt (addrExt a p) (addrExt a q)).map (fun p => (f p.1,f p.2)) :=
      fun p q => couple_linksAt_map_local r f _ _ (ha.child p) (ha.child q)
    have hG : ∀ p q, g.linksAt (f (addrExt a p)) (f (addrExt a q)) =
        (g.linksAt (addrExt a p) (addrExt a q)).map (fun p => (f p.1,f p.2)) :=
      fun p q => couple_linksAt_map_local g f _ _ (ha.child p) (ha.child q)
    have hI := chain_linksAt_map_local i f _ (ha.child [m.c]) (slotSign ζ m.c)
    have hS := chain_linksAt_map_local s f _
      (ha.child ([m.c] ++ i.lonePath ++ [m.lone])) (slotSign (slotSign ζ m.c) m.lone)
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [RegChain.linksAt,hr,hg,ite_true,ite_false,List.map_cons,List.map_append,← hA,hR,hG,hI,hS]
termination_by structural X
end


/-- Links of a regular tree never enter its terminal lone subtree. -/
theorem chain_link_not_below_lone {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Address w)
    (q : Pair w) (hq : q ∈ X.linksAt ζ a) :
    ¬ Below (addrExt a X.lonePath) q.1 ∧ ¬ Below (addrExt a X.lonePath) q.2 := by
  have hall : pairEndpoints (X.linksAt ζ a) = branchAddresses (X.plug ζ .leaf) a := by
    rw [chain_branchAddresses, branchAddresses_leaf, Finset.union_empty]
  have hnode (z : Address w) (hz : z ∈ pairEndpoints (X.linksAt ζ a)) :
      ¬ Below (addrExt a X.lonePath) z := by
    rw [hall] at hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    intro hb
    have hp : X.lonePath <+: r := (List.prefix_append_right_inj a.2).mp hb.2
    exact Twist.leaf_not_prefix_branch (chain_lone_mem_leaves X ζ) hr hp
  exact ⟨hnode _ ((mem_pairEndpoints_iff _ _).mpr ⟨q,hq,Or.inl rfl⟩),
    hnode _ ((mem_pairEndpoints_iff _ _).mpr ⟨q,hq,Or.inr rfl⟩)⟩

/-- Prefix insertion below the terminal hole fixes every existing link. -/
theorem chain_links_image_fixed_below_lone {w : ℕ} (X : RegChain) (ζ : ℤˣ)
    (a target : Address w) (p : Path) (ht : Below (addrExt a X.lonePath) target) :
    (X.linksAt ζ a).map (fun q => (stretch target p q.1,stretch target p q.2)) = X.linksAt ζ a := by
  have hm : (X.linksAt ζ a).map (fun q => (stretch target p q.1,stretch target p q.2)) =
      (X.linksAt ζ a).map id := by
    apply List.map_congr_left
    intro q hq
    have hn := chain_link_not_below_lone X ζ a q hq
    exact Prod.ext
      (stretch_outside target p q.1 (fun hb => hn.1 (below_trans ht hb)))
      (stretch_outside target p q.2 (fun hb => hn.2 (below_trans ht hb)))
  simpa only [List.map_id] using hm

end WaveTurbulence.LFTwist

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Equal

/-!
# Labelled chains: the layering of a coherent chain from its spine layers

A coherent chain is layered by its top-level spine layers. Every node in the region of a top-level pair (below
the pair's root, not below the next spine position) is in that pair's layer, and the nodes below the lone
position are in a default layer `d`. This file has:

* `chainNodes_region`: chain nodes lie below the root and not below the lone position, and the parts of a pair
  are not below the next spine position (`own_region`);
* `LabOK d X ls u`: labels non-increasing in `[d, u]`, one per top-level pair;
* `chainLay X ls d a z`: the layer of `z` in the labelled chain; its bounds, monotonicity along `Under`, and its
  value `d` below the lone position;
* `chainPairLayers_of_lay`: the layering `chainLay` satisfies `ChainPairLayers`;
* `lay_pairs_eq`, `lay_links_eq`: both ends of every leaf pair and every link get the same layer;
* `chainPairLayers_push`: `ChainPairLayers` transported forward along an address map.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w v : ℕ}

theorem miniTree_facts (m : MiniTreeCode) :
    m.red.1 ≠ m.c ∧ m.green.1 ≠ m.c ∧ m.red.2 ≠ m.lone ∧ m.green.2 ≠ m.lone := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

theorem cplNodes_region {Q : RegCpl} {x y z : Fin w × Path} (hz : z ∈ cplNodes Q x y) :
    Under x z ∨ Under y z := by
  unfold cplNodes at hz
  rw [← couple_branchAddresses Q x y, ← couple_leafAddresses Q x y] at hz
  simp only [Finset.mem_union, branchAddresses, leafAddresses, Finset.mem_image] at hz
  rcases hz with ((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | (⟨p, -, rfl⟩ | ⟨p, -, rfl⟩))
  · exact Or.inl (under_ext _ _)
  · exact Or.inr (under_ext _ _)
  · exact Or.inl (under_ext _ _)
  · exact Or.inr (under_ext _ _)

theorem orientedNodes_region {P : Prop} [Decidable P] {Q : RegCpl} {x y z : Fin w × Path}
    (hz : z ∈ orientedNodes P Q x y) : Under x z ∨ Under y z := by
  unfold orientedNodes at hz
  split_ifs at hz
  · exact cplNodes_region hz
  · exact (cplNodes_region hz).symm

theorem next_eq (a : Fin w × Path) (m : MiniTreeCode) (inner : RegChain) :
    nextAddr a m inner = addrExt (addrExt a ([m.c] ++ inner.lonePath)) [m.lone] := by
  rw [addrExt_append]
  rfl

theorem lone_eq (a : Fin w × Path) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) :
    addrExt a (RegChain.pair m Qr Qg inner rest).lonePath = addrExt (nextAddr a m inner) rest.lonePath := by
  show addrExt a ([m.c] ++ inner.lonePath ++ [m.lone] ++ rest.lonePath) = _
  rw [← addrExt_append]
  rfl

/-- The own parts of a top-level pair. -/
def OwnPart (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (ζ : ℤˣ) (a z : Fin w × Path) : Prop :=
  z = a ∨ z = addrExt a ([m.c] ++ inner.lonePath) ∨
    z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) ∨
    z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) ∨
    z ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c])

/-- **The own parts of a pair are below its root and not below the next spine position.** -/
theorem own_region {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {ζ : ℤˣ} {a z : Fin w × Path}
    (hin : ∀ z ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]),
      Under (addrExt a [m.c]) z ∧ ¬ Under (addrExt (addrExt a [m.c]) inner.lonePath) z)
    (hz : OwnPart m Qr Qg inner ζ a z) : Under a z ∧ ¬ Under (nextAddr a m inner) z := by
  obtain ⟨hr1, hg1, hr2, hg2⟩ := miniTree_facts m
  have hnext := next_eq a m inner
  rcases hz with rfl | rfl | hz | hz | hz
  · refine ⟨under_refl _, fun h => ?_⟩
    have := under_length h
    simp [nextAddr, addrExt] at this
  · refine ⟨under_ext _ _, fun h => ?_⟩
    rw [hnext] at h
    have := under_length h
    simp [addrExt] at this
  · rcases orientedNodes_region hz with h | h
    · refine ⟨under_trans (under_ext _ _) h, fun hn => ?_⟩
      exact not_under_both hr1 [] (inner.lonePath ++ [m.lone]) h hn
    · refine ⟨under_trans (under_ext _ _) h, fun hn => ?_⟩
      have h' : Under (addrExt (addrExt a ([m.c] ++ inner.lonePath)) [m.red.2]) z := by
        rwa [addrExt_append]
      rw [hnext] at hn
      exact not_under_both hr2 [] [] h' hn
  · rcases orientedNodes_region hz with h | h
    · refine ⟨under_trans (under_ext _ _) h, fun hn => ?_⟩
      exact not_under_both hg1 [] (inner.lonePath ++ [m.lone]) h hn
    · refine ⟨under_trans (under_ext _ _) h, fun hn => ?_⟩
      have h' : Under (addrExt (addrExt a ([m.c] ++ inner.lonePath)) [m.green.2]) z := by
        rwa [addrExt_append]
      rw [hnext] at hn
      exact not_under_both hg2 [] [] h' hn
  · obtain ⟨h1, h2⟩ := hin z hz
    refine ⟨under_trans (under_ext _ _) h1, fun hn => h2 ?_⟩
    rw [addrExt_append]
    rw [hnext] at hn
    exact under_trans (under_ext _ _) hn

theorem ownPart_of_mem {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin w × Path} (hz : z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a) :
    OwnPart m Qr Qg inner ζ a z ∨
      z ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (nextAddr a m inner) := by
  rcases mem_chainNodesSet_pair hz with h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr h

/-- **Chain nodes lie below the root and not below the lone position.** -/
theorem chainNodes_region : ∀ (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path), z ∈ chainNodesSet X ζ a →
    Under a z ∧ ¬ Under (addrExt a X.lonePath) z
  | .nil, _, _, _, hz => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt] at hz
  | .pair m Qr Qg inner rest, ζ, a, z, hz => by
    rw [lone_eq]
    rcases ownPart_of_mem hz with h | h
    · obtain ⟨h1, h2⟩ := own_region (fun z hz => chainNodes_region inner _ _ z hz) h
      exact ⟨h1, fun hl => h2 (under_trans (under_ext _ _) hl)⟩
    · obtain ⟨h1, h2⟩ := chainNodes_region rest _ _ z h
      exact ⟨under_trans (under_ext _ _) h1, h2⟩

theorem own_not_next {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {ζ : ℤˣ} {a z : Fin w × Path}
    (hz : OwnPart m Qr Qg inner ζ a z) : ¬ Under (nextAddr a m inner) z :=
  (own_region (fun z hz => chainNodes_region inner _ _ z hz) hz).2

/-! ### Labels and the labelled layer -/

/-- Labels `ls` of the top-level pairs of `X`: one per pair, non-increasing, in `[d, u]`. -/
def LabOK (d : ℕ) : RegChain → List ℕ → ℕ → Prop
  | .nil, ls, _ => ls = []
  | .pair _ _ _ _ _, [], _ => False
  | .pair _ _ _ _ rest, l :: ls, u => d ≤ l ∧ l ≤ u ∧ LabOK d rest ls l

/-- **The layer of `z` in a labelled chain rooted at `a`**, default `d` below the lone position. -/
def chainLay : RegChain → List ℕ → ℕ → (Fin w × Path) → (Fin w × Path) → ℕ
  | .nil, _, d, _, _ => d
  | .pair _ _ _ _ _, [], d, _, _ => d
  | .pair m _ _ inner rest, l :: ls, d, a, z =>
    if Under (nextAddr a m inner) z then chainLay rest ls d (nextAddr a m inner) z else l

theorem chainLay_pair (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (l : ℕ) (ls : List ℕ)
    (d : ℕ) (a z : Fin w × Path) :
    chainLay (.pair m Qr Qg inner rest) (l :: ls) d a z =
      if Under (nextAddr a m inner) z then chainLay rest ls d (nextAddr a m inner) z else l := rfl

variable {d : ℕ}

theorem chainLay_le : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ) (a z : Fin w × Path), LabOK d X ls u → d ≤ u →
    chainLay X ls d a z ≤ u
  | .nil, _, _, _, _, _, hdu => hdu
  | .pair .., [], _, _, _, h, _ => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, a, z, ⟨h1, h2, h3⟩, _ => by
    rw [chainLay_pair]
    split_ifs
    · exact (chainLay_le rest ls l _ z h3 h1).trans h2
    · exact h2

theorem le_chainLay : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ) (a z : Fin w × Path), LabOK d X ls u →
    d ≤ chainLay X ls d a z
  | .nil, _, _, _, _, _ => le_rfl
  | .pair .., [], _, _, _, h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, a, z, ⟨h1, _, h3⟩ => by
    rw [chainLay_pair]
    split_ifs
    · exact le_chainLay rest ls l _ z h3
    · exact h1

theorem chainLay_mono : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ) (a z z' : Fin w × Path), LabOK d X ls u →
    d ≤ u → Under z z' → chainLay X ls d a z' ≤ chainLay X ls d a z
  | .nil, _, _, _, _, _, _, _, _ => le_rfl
  | .pair .., [], _, _, _, _, h, _, _ => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, a, z, z', ⟨h1, _, h3⟩, _, hzz => by
    rw [chainLay_pair, chainLay_pair]
    by_cases hz : Under (nextAddr a m inner) z
    · rw [ite_eq_left (under_trans hz hzz), ite_eq_left hz]
      exact chainLay_mono rest ls l _ z z' h3 h1 hzz
    · rw [ite_eq_right hz]
      split_ifs
      · exact chainLay_le rest ls l _ z' h3 h1
      · exact le_rfl

theorem chainLay_lone : ∀ (X : RegChain) (ls : List ℕ) (a z : Fin w × Path),
    Under (addrExt a X.lonePath) z → chainLay X ls d a z = d
  | .nil, _, _, _, _ => rfl
  | .pair .., [], _, _, _ => rfl
  | .pair m Qr Qg inner rest, l :: ls, a, z, h => by
    rw [lone_eq] at h
    rw [chainLay_pair, ite_eq_left (under_trans (under_ext _ _) h)]
    exact chainLay_lone rest ls _ z h

theorem chainLay_own {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ} {l : ℕ}
    {ls : List ℕ} {a z : Fin w × Path} (hz : OwnPart m Qr Qg inner ζ a z) :
    chainLay (.pair m Qr Qg inner rest) (l :: ls) d a z = l := by
  rw [chainLay_pair, ite_eq_right (own_not_next hz)]

theorem chainLay_rest {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ} {l : ℕ}
    {ls : List ℕ} {a z : Fin w × Path}
    (hz : z ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (nextAddr a m inner)) :
    chainLay (.pair m Qr Qg inner rest) (l :: ls) d a z = chainLay rest ls d (nextAddr a m inner) z := by
  rw [chainLay_pair, ite_eq_left (chainNodes_region rest _ _ z hz).1]

/-- **The labelled layering satisfies `ChainPairLayers`.** -/
theorem chainPairLayers_of_lay {LG : LayeredGarden w} : ∀ (X : RegChain) (ζ : ℤˣ) (ls : List ℕ)
    (a : Fin w × Path), (∀ z ∈ chainNodesSet X ζ a, layerAt LG z = chainLay X ls d a z) →
    ChainPairLayers LG X ζ a
  | .nil, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, [], a, h => chainPairLayers_of_const (c := d) _ _ _ fun z hz => h z hz
  | .pair m Qr Qg inner rest, ζ, l :: ls, a, h => by
    have hown : ∀ z, OwnPart m Qr Qg inner ζ a z → z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a →
        layerAt LG z = l := fun z ho hz => (h z hz).trans (chainLay_own ho)
    have ha := hown a (Or.inl rfl) (Links.root_mem_chainNodesSet _ _ _ _ _ _ _)
    refine ⟨?_, fun z hz => ?_, fun z hz => ?_, ?_, ?_⟩
    · rw [ha]
      exact hown _ (Or.inr (Or.inl rfl)) (mem_chainNodesSet_innerLone _ _ _ _ _ _ _)
    · rw [ha]
      exact hown z (Or.inr (Or.inr (Or.inl hz))) (mem_chainNodesSet_red hz)
    · rw [ha]
      exact hown z (Or.inr (Or.inr (Or.inr (Or.inl hz)))) (mem_chainNodesSet_green hz)
    · exact chainPairLayers_of_const (c := l) _ _ _ fun z hz =>
        hown z (Or.inr (Or.inr (Or.inr (Or.inr hz)))) (mem_chainNodesSet_inner hz)
    · exact chainPairLayers_of_lay rest _ ls _ fun z hz =>
        (h z (mem_chainNodesSet_rest hz)).trans (chainLay_rest hz)

theorem mem_pairEndpoints_fst {α : Type*} [DecidableEq α] {P : List (α × α)} {x : α × α} (hx : x ∈ P) :
    x.1 ∈ pairEndpoints P := (mem_pairEndpoints_iff P _).2 ⟨x, hx, Or.inl rfl⟩

theorem mem_pairEndpoints_snd {α : Type*} [DecidableEq α] {P : List (α × α)} {x : α × α} (hx : x ∈ P) :
    x.2 ∈ pairEndpoints P := (mem_pairEndpoints_iff P _).2 ⟨x, hx, Or.inr rfl⟩

/-- **Both ends of a leaf pair of a labelled chain have the same layer.** -/
theorem lay_pairs_eq : ∀ (X : RegChain) (ζ : ℤˣ) (ls : List ℕ) (a : Fin w × Path),
    ∀ x ∈ X.pairsAt ζ a, chainLay X ls d a x.1 = chainLay X ls d a x.2
  | .nil, _, _, _, x, hx => by simp [RegChain.pairsAt] at hx
  | .pair m Qr Qg inner rest, ζ, [], a, x, _ => rfl
  | .pair m Qr Qg inner rest, ζ, l :: ls, a, x, hx => by
    simp only [RegChain.pairsAt, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · rw [chainLay_own (Or.inr (Or.inr (Or.inl (mem_oriented_of_pairs (mem_pairEndpoints_fst hx))))),
        chainLay_own (Or.inr (Or.inr (Or.inl (mem_oriented_of_pairs (mem_pairEndpoints_snd hx)))))]
    · rw [chainLay_own (Or.inr (Or.inr (Or.inr (Or.inl
          (mem_oriented_of_pairs (mem_pairEndpoints_fst hx)))))),
        chainLay_own (Or.inr (Or.inr (Or.inr (Or.inl (mem_oriented_of_pairs (mem_pairEndpoints_snd hx))))))]
    · have h1 : x.1 ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]) :=
        Finset.mem_union_right _ (mem_pairEndpoints_fst hx)
      have h2 : x.2 ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]) :=
        Finset.mem_union_right _ (mem_pairEndpoints_snd hx)
      rw [chainLay_own (Or.inr (Or.inr (Or.inr (Or.inr h1)))), chainLay_own (Or.inr (Or.inr (Or.inr (Or.inr h2))))]
    · have h1 : x.1 ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (nextAddr a m inner) :=
        Finset.mem_union_right _ (mem_pairEndpoints_fst hx)
      have h2 : x.2 ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (nextAddr a m inner) :=
        Finset.mem_union_right _ (mem_pairEndpoints_snd hx)
      rw [chainLay_rest h1, chainLay_rest h2]
      exact lay_pairs_eq rest _ ls _ x hx

/-- **Both ends of a link of a labelled chain have the same layer.** -/
theorem lay_links_eq : ∀ (X : RegChain) (ζ : ℤˣ) (ls : List ℕ) (a : Fin w × Path),
    ∀ x ∈ X.linksAt ζ a, chainLay X ls d a x.1 = chainLay X ls d a x.2
  | .nil, _, _, _, x, hx => by simp [RegChain.linksAt] at hx
  | .pair m Qr Qg inner rest, ζ, [], a, x, _ => rfl
  | .pair m Qr Qg inner rest, ζ, l :: ls, a, x, hx => by
    simp only [RegChain.linksAt, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | ((hx | hx) | hx) | hx
    · rw [chainLay_own (ζ := ζ) (Or.inl rfl), chainLay_own (ζ := ζ) (Or.inr (Or.inl rfl))]
    · rw [chainLay_own (Or.inr (Or.inr (Or.inl (mem_oriented_of_links (mem_pairEndpoints_fst hx))))),
        chainLay_own (Or.inr (Or.inr (Or.inl (mem_oriented_of_links (mem_pairEndpoints_snd hx)))))]
    · rw [chainLay_own (Or.inr (Or.inr (Or.inr (Or.inl
          (mem_oriented_of_links (mem_pairEndpoints_fst hx)))))),
        chainLay_own (Or.inr (Or.inr (Or.inr (Or.inl (mem_oriented_of_links (mem_pairEndpoints_snd hx))))))]
    · have h1 : x.1 ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]) :=
        Finset.mem_union_left _ (mem_pairEndpoints_fst hx)
      have h2 : x.2 ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]) :=
        Finset.mem_union_left _ (mem_pairEndpoints_snd hx)
      rw [chainLay_own (Or.inr (Or.inr (Or.inr (Or.inr h1)))), chainLay_own (Or.inr (Or.inr (Or.inr (Or.inr h2))))]
    · have h1 : x.1 ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (nextAddr a m inner) :=
        Finset.mem_union_left _ (mem_pairEndpoints_fst hx)
      have h2 : x.2 ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (nextAddr a m inner) :=
        Finset.mem_union_left _ (mem_pairEndpoints_snd hx)
      rw [chainLay_rest h1, chainLay_rest h2]
      exact lay_links_eq rest _ ls _ x hx

/-! ### Transport forward along an address map -/

section Push

variable (LG : LayeredGarden w) (LG' : LayeredGarden v) (f : (Fin v × Path) → (Fin w × Path))
  (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (hlay : ∀ z, layerAt LG' z = layerAt LG (f z))
include hf hlay

theorem chainPairLayers_push :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin v × Path), ChainPairLayers LG' X ζ a → ChainPairLayers LG X ζ (f a)
  | .nil, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, ⟨h1, h2, h3, h4, h5⟩ => by
    refine ⟨?_, fun z hz => ?_, fun z hz => ?_, ?_, ?_⟩
    · rw [← hf, ← hlay, ← hlay]
      exact h1
    · rw [← hf, ← hf, orientedNodes_map _ Qr f hf] at hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      rw [← hlay, ← hlay]
      exact h2 z' hz'
    · rw [← hf, ← hf, orientedNodes_map _ Qg f hf] at hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      rw [← hlay, ← hlay]
      exact h3 z' hz'
    · rw [← hf]
      exact chainPairLayers_push inner _ _ h4
    · rw [← hf]
      exact chainPairLayers_push rest _ _ h5

end Push

end WaveTurbulence.PL234

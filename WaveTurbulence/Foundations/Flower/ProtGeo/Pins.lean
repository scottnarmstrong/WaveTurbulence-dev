/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Couple

/-! # D2b PROT-GEO (4): item (ii), the intrinsic pins of a protected object (o104 Prop 7.2 (G1))

`objCfg LG J pat X u` is the configuration of the stem chain at `u` (chain code `X`), read from the pattern of its
tree and the position of its lone leaf:
* `term`: the lone leaf is the capped flower (o73 (13.1), (P6) when `π` is pinned by `dParent` and the lone leaf is the
  flower parent);
* `root`/`rootTerm`: `dRoot` with the object rooted at the tree root ((P1), (P2)/(P3));
* `penTerm`: `dParent` with the flower parent terminal and its chain parent in the object ((P4)/(P5));
* `termChild i`: `dChild i` with the flower parent terminal and its branching child `i` ((P7)).

`fixCap_eq_pins`: at every branching vertex of the object, `fixCap = (objCfg …).pins.lookup`; `objCfg_valid`: the
configuration is `ProtCfg.Valid` (for `termChild`, `CapPatValid` gives layer `p`); it is never `trace`. The
extraction forms are `fixCap_objTree`/`objCfg_valid_objTree` and `fixCap_objCpl`/`objCfg_valid_objCpl`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ}

/-- **The configuration of a protected object** (by its tree's pattern and its lone leaf). -/
def objCfg (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (X : RegChain)
    (u : Fin w × Path) : ProtCfg :=
  match pat u.1 with
  | .plain => if PortFlower LG J X u then .term else .none
  | .dRoot => if PortFlower LG J X u then (if u.2 = [] ∧ 2 ≤ X.lonePath.length then .rootTerm else .term)
      else if u.2 = [] then .root else .none
  | .dParent => if PortFlower LG J X u then (if 2 ≤ X.lonePath.length then .penTerm else .term)
      else if PortFP LG J X u then .term else .none
  | .dChild i => if PortFlower LG J X u then
        (if u.2 ++ X.lonePath.dropLast ++ [i] ∈ (LG.garden.tree u.1).branching then .termChild i else .term)
      else .none

theorem lookup_cons' {β : Type*} (a k : Path) (v : β) (l : List (Path × β)) :
    ((k, v) :: l).lookup a = if a = k then some v else l.lookup a := by
  by_cases h : a = k
  · subst h; simp [List.lookup]
  · have h' : (a == k) = false := by simpa using h
    simp [List.lookup, h', h]

/-! ## Path arithmetic -/

theorem eq_of_prefix_len {l₁ l₂ : Path} (h : l₁ <+: l₂) (hl : l₂.length ≤ l₁.length) : l₁ = l₂ :=
  h.eq_of_length (le_antisymm h.length_le hl)

theorem prefix_one_or_two {r : Path} {k k' : Fin 3} (h : r <+: [k, k']) (hr : r ≠ []) :
    r = [k] ∨ r = [k, k'] := by
  obtain ⟨t, ht⟩ := h
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩
  · exact absurd rfl hr
  · left; simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht; rw [ht.1]
  · right; simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht; rw [ht.1, ht.2.1]
  · simp at ht

theorem dropLast_ne_self {P : Path} (hP : P ≠ []) : P.dropLast ≠ P := by
  intro h
  have := congrArg List.length h
  rw [List.length_dropLast] at this
  have : P.length ≠ 0 := fun h0 => hP (List.length_eq_zero_iff.mp h0)
  omega

/-! ## The four pin predicates on the object's branching vertices -/

section Iff

variable {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path}
  {h : TTree}

/-- The flower parent of the lone leaf, when the lone leaf is a capped flower. -/
theorem port_fp (hq0 : X.lonePath ≠ []) (hpf : PortFlower LG J X u)
    (b : GBranch LG.garden.tree) (hb : b.1 = addrExt u X.lonePath.dropLast) : IsCapFlowerParent LG J b := by
  obtain ⟨f, hf, hfe⟩ := hpf
  refine ⟨f, hf, ?_, X.lonePath.getLast hq0, ?_⟩
  · rw [hfe, hb]; rfl
  · rw [hfe, hb]; simp [addrExt, List.append_assoc, List.dropLast_append_getLast hq0]

/-- **(F1)** A branching vertex of the object is a capped flower parent iff the lone leaf is the capped flower and the
vertex is the terminal chain node. -/
theorem fp_iff (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) {b : GBranch LG.garden.tree} {q : Path}
    (hq : q ∈ (X.plug ζ .leaf).branching) (hb : b.1 = addrExt u q) :
    IsCapFlowerParent LG J b ↔ PortFlower LG J X u ∧ q = X.lonePath.dropLast := by
  have hq0 := lone_ne_nil_of_branch X ζ hq
  constructor
  · rintro ⟨f, hf, hf1, i, hfi⟩
    have hU : Under (addrExt u q) f.1 := ⟨by rw [← hb]; exact hf1.symm, by rw [hfi, hb]; exact List.prefix_append _ _⟩
    have hP := port_below_flower hG.cap_leaf hS.emb hq hf hU
    obtain ⟨hlt, hne⟩ := branch_lt_lone hG.cap_leaf hS.emb hq hf hU
    have h2 : u.2 ++ X.lonePath <+: u.2 ++ (q ++ [i]) := by
      have := hP.2; rw [hfi, hb] at this; simpa [addrExt, List.append_assoc] using this
    have h3 := (List.prefix_append_right_inj u.2).mp h2
    have hlen : X.lonePath.length = q.length + 1 := by
      have a1 := h3.length_le
      have a2 : q.length < X.lonePath.length := by
        rcases hlt with ⟨r, hr⟩
        have : r ≠ [] := fun h0 => hne (by rw [← hr, h0, List.append_nil])
        rw [← hr, List.length_append]
        have : r.length ≠ 0 := fun h0 => this (List.length_eq_zero_iff.mp h0)
        omega
      simp at a1; omega
    have he : X.lonePath = q ++ [i] := eq_of_prefix_len h3 (by simp; omega)
    refine ⟨⟨f, hf, ?_⟩, by rw [he, List.dropLast_concat]⟩
    apply Prod.ext
    · rw [hf1, hb]; rfl
    · rw [hfi, hb, he]; simp [addrExt, List.append_assoc]
  · rintro ⟨hpf, rfl⟩
    exact port_fp hq0 hpf b hb

/-- **(F3)** The `dParent` pin condition on a branching vertex of the object. -/
theorem parentPin_iff (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) {b : GBranch LG.garden.tree} {q : Path}
    (hq : q ∈ (X.plug ζ .leaf).branching) (hb : b.1 = addrExt u q) :
    (∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.IsChildOf b) ↔
      (PortFlower LG J X u ∧ 2 ≤ X.lonePath.length ∧ q = X.lonePath.dropLast.dropLast) ∨
        (PortFP LG J X u ∧ q = X.lonePath.dropLast) := by
  have hq0 := lone_ne_nil_of_branch X ζ hq
  constructor
  · rintro ⟨c, ⟨f, hf, hf1, k', hfk⟩, hc1, k, hck⟩
    have hU : Under (addrExt u q) f.1 := ⟨by rw [← hb, ← hc1]; exact hf1.symm,
      by rw [hfk, hck, hb]; simp [addrExt, List.append_assoc]⟩
    have hP := port_below_flower hG.cap_leaf hS.emb hq hf hU
    obtain ⟨⟨r, hr⟩, hne⟩ := branch_lt_lone hG.cap_leaf hS.emb hq hf hU
    have hr0 : r ≠ [] := fun h0 => hne (by rw [← hr, h0, List.append_nil])
    have h2 : u.2 ++ (q ++ r) <+: u.2 ++ (q ++ [k, k']) := by
      have := hP.2; rw [hfk, hck, hb, ← hr] at this; simpa [addrExt, List.append_assoc] using this
    have h3 : r <+: [k, k'] := (List.prefix_append_right_inj q).mp ((List.prefix_append_right_inj u.2).mp h2)
    rcases prefix_one_or_two h3 hr0 with rfl | rfl
    · right
      refine ⟨⟨c, ⟨f, hf, hf1, k', hfk⟩, ?_⟩, by rw [← hr, List.dropLast_concat]⟩
      rw [← hr]; apply Prod.ext
      · rw [hc1, hb]; rfl
      · rw [hck, hb]; simp [addrExt, List.append_assoc]
    · left
      refine ⟨⟨f, hf, ?_⟩, by rw [← hr]; simp, by rw [← hr]; simp [List.dropLast_append_of_ne_nil]⟩
      rw [← hr]; apply Prod.ext
      · rw [hf1, hc1, hb]; rfl
      · rw [hfk, hck, hb]; simp [addrExt, List.append_assoc]
  · rintro (⟨hpf, h2, rfl⟩ | ⟨⟨c, hc, hce⟩, rfl⟩)
    · have hne : X.lonePath.dropLast ≠ [] := by
        intro h0; have := congrArg List.length h0; rw [List.length_dropLast] at this; simp at this; omega
      have hdq : X.lonePath.dropLast <+: X.lonePath := List.dropLast_prefix _
      let c := embBr hS.emb _ (prefix_lone_branching X ζ hdq (dropLast_ne_self hq0))
      refine ⟨c, port_fp hq0 hpf c rfl, ?_, X.lonePath.dropLast.getLast hne, ?_⟩
      · show u.1 = b.1.1; rw [hb]; rfl
      · show u.2 ++ X.lonePath.dropLast = b.1.2 ++ _
        rw [hb]; simp [addrExt, List.append_assoc, List.dropLast_append_getLast hne]
    · refine ⟨c, hc, ?_, X.lonePath.getLast hq0, ?_⟩
      · rw [hce, hb]; rfl
      · rw [hce, hb]; simp [addrExt, List.append_assoc, List.dropLast_append_getLast hq0]

/-- **(F4)** The `dChild i` pin condition on a branching vertex of the object (uses one flower per tree). -/
theorem childPin_iff (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) {b : GBranch LG.garden.tree} {q : Path}
    (hq : q ∈ (X.plug ζ .leaf).branching) (hb : b.1 = addrExt u q) (i : Fin 3) :
    (∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]) ↔
      PortFlower LG J X u ∧ q = X.lonePath.dropLast ++ [i] := by
  have hq0 := lone_ne_nil_of_branch X ζ hq
  constructor
  · rintro ⟨c, hc, hbc1, hbc2⟩
    by_cases hqn : q = []
    · exfalso
      subst hqn
      obtain ⟨fc, hfc, hfc1, k, hfck⟩ := hc
      obtain ⟨v, hv, f0, hf0, hvf⟩ := hS.meets
      obtain ⟨q', hq', hvq⟩ := mem_branchAddresses'.mp hv
      have hU : Under (addrExt u q') f0.1 := ⟨by rw [← hvq]; exact hvf.1, by rw [← hvq]; exact hvf.2⟩
      have hP := port_below_flower hG.cap_leaf hS.emb hq' hf0 hU
      have htree : f0.1.1 = fc.1.1 := by
        rw [← hP.1, hfc1, ← hbc1, hb]; rfl
      have hff := hG.one_flower f0 fc hf0 hfc htree
      subst hff
      have h1 : u.2 ++ X.lonePath <+: c.1.2 ++ [k] := by rw [← hfck]; exact hP.2
      have h2 : u.2 = c.1.2 ++ [i] := by rw [← hbc2, hb]; simp [addrExt]
      rw [h2, List.append_assoc] at h1
      have h3 := (List.prefix_append_right_inj c.1.2).mp h1
      have hl := h3.length_le
      simp only [List.singleton_append, List.length_cons, List.length_nil] at hl
      exact hq0 (List.length_eq_zero_iff.mp (by omega))
    · have hqd : q.dropLast ++ [q.getLast hqn] = q := List.dropLast_append_getLast hqn
      have hdb : q.dropLast ∈ (X.plug ζ .leaf).branching :=
        Comb.TreePath.branching_of_append_mem _ (by rw [hqd]; exact TTree.branching_subset_nodes _ hq)
      have hc2 : c.1.2 = u.2 ++ q.dropLast := by
        have e : u.2 ++ q = c.1.2 ++ [i] := by rw [← hbc2, hb]; rfl
        rw [← hqd, ← List.append_assoc] at e
        exact (List.append_inj' e rfl).1.symm
      have hi : q.getLast hqn = i := by
        have e : u.2 ++ q = c.1.2 ++ [i] := by rw [← hbc2, hb]; rfl
        rw [← hqd, ← List.append_assoc] at e
        simpa using (List.append_inj' e rfl).2
      have hce : c.1 = addrExt u q.dropLast := by
        apply Prod.ext
        · rw [← hbc1, hb]; rfl
        · exact hc2
      obtain ⟨hpf, hdl⟩ := (fp_iff hG hS hdb hce).mp hc
      refine ⟨hpf, ?_⟩
      rw [← hqd, hdl, hi]
  · rintro ⟨hpf, rfl⟩
    have hdq : X.lonePath.dropLast <+: X.lonePath := List.dropLast_prefix _
    let c := embBr hS.emb _ (prefix_lone_branching X ζ hdq (dropLast_ne_self hq0))
    refine ⟨c, port_fp hq0 hpf c rfl, ?_, ?_⟩
    · rw [hb]; rfl
    · rw [hb]; simp [c, embBr, addrExt, List.append_assoc]

end Iff

end WaveTurbulence.Flower.ProtGeo

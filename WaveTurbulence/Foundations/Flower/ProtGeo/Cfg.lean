/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Pins

/-! # D2b PROT-GEO (5): item (ii), `fixCap = ProtCfg.fix` on a protected object, and validity

* `fixCap_eq_pins` (address form): on every branching vertex `addrExt u q` of a stem chain, the intrinsic pins are
  `((objCfg LG J pat X u).pins X s t up).lookup q`.
* `fixCap_objTree`, `fixCap_objCpl` (extraction forms): `fixCap … (lift b') = (objCfg …).fix X s t up b'`.
* `objCfg_valid_objTree`, `objCfg_valid_objCpl`: `ProtCfg.Valid` (o104 PatValid transported; the `termChild` vertex is
  in layer `p` by `CapPatValid`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {X : RegChain} {ζ : ℤˣ}
  {u : Fin w × Path} {h : TTree}

/-- The lone position is never both a capped flower (a leaf) and a capped flower parent (a branch). -/
theorem not_portFlower_and_portFP : ¬ (PortFlower LG J X u ∧ PortFP LG J X u) := by
  rintro ⟨⟨f, -, hf⟩, ⟨c, -, hc⟩⟩
  have hl := f.2
  have hb := c.2
  rw [hf] at hl; rw [hc] at hb
  exact TTree.not_mem_branching_of_mem_leaves _ hl hb

theorem dropLast_nil_of_short {P : Path} (hP : P ≠ []) (h2 : ¬ 2 ≤ P.length) : P.dropLast = [] := by
  rw [← List.length_eq_zero_iff, List.length_dropLast]
  have : P.length ≠ 0 := fun h0 => hP (List.length_eq_zero_iff.mp h0)
  omega

theorem dropLast_ne_nil_of_long {P : Path} (h2 : 2 ≤ P.length) : P.dropLast ≠ [] := by
  intro h0
  have := congrArg List.length h0
  rw [List.length_dropLast] at this; simp at this; omega

theorem dropLast_ne_dropLast_dropLast {P : Path} (hP : P.dropLast ≠ []) : P.dropLast.dropLast ≠ P.dropLast :=
  dropLast_ne_self hP

/-- **(ii), address form (o104 Prop 7.2 (G1)).** On the branching vertices of a stem chain, the intrinsic pins
`fixCap` are the pins of the configuration `objCfg`. -/
theorem fixCap_eq_pins (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) (pat : Fin w → FixPat) (t s up : ℝ)
    {b : GBranch LG.garden.tree} {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) (hb : b.1 = addrExt u q) :
    fixCap LG J pat t s b = ((objCfg LG J pat X u).pins X s t up).lookup q := by
  have hq0 := lone_ne_nil_of_branch X ζ hq
  have hpat : pat b.1.1 = pat u.1 := by rw [hb]; rfl
  have hroot : b.1.2 = [] ↔ u.2 = [] ∧ q = [] := by
    rw [hb]; exact List.append_eq_nil_iff
  have hnb := @not_portFlower_and_portFP w LG J X u
  unfold fixCap objCfg
  simp only [fp_iff hG hS hq hb, hpat]
  cases hp : pat u.1 with
  | plain =>
    by_cases hpf : PortFlower LG J X u <;> simp [hpf, ProtCfg.pins, lookup_cons']
  | dRoot =>
    simp only [hroot]
    by_cases hpf : PortFlower LG J X u
    · by_cases hu : u.2 = [] ∧ 2 ≤ X.lonePath.length
      · have hdl := dropLast_ne_nil_of_long hu.2
        by_cases hq1 : q = []
        · subst hq1; simp [hpf, hu, ProtCfg.pins, Ne.symm hdl]
        · simp [hpf, hu, ProtCfg.pins, lookup_cons', hq1]
      · have key : ¬ (q ≠ X.lonePath.dropLast ∧ u.2 = [] ∧ q = []) := by
          rintro ⟨hne, hu2, rfl⟩
          exact hne (dropLast_nil_of_short hq0 (fun h2 => hu ⟨hu2, h2⟩)).symm
        by_cases hq1 : q = X.lonePath.dropLast
        · simp [hpf, hu, ProtCfg.pins, hq1]
        · have : ¬ (u.2 = [] ∧ q = []) := fun h' => key ⟨hq1, h'⟩
          simp [hpf, hu, ProtCfg.pins, lookup_cons', hq1, this]
    · by_cases hu : u.2 = []
      · simp [hpf, hu, ProtCfg.pins, lookup_cons']
      · simp [hpf, hu, ProtCfg.pins]
  | dParent =>
    simp only [parentPin_iff hG hS hq hb]
    by_cases hpf : PortFlower LG J X u
    · have hfp : ¬ PortFP LG J X u := fun h' => hnb ⟨hpf, h'⟩
      by_cases h2 : 2 ≤ X.lonePath.length
      · have hdl := dropLast_ne_nil_of_long h2
        by_cases hq1 : q = X.lonePath.dropLast
        · subst hq1
          simp [hpf, h2, ProtCfg.pins, lookup_cons']
        · simp [hpf, hfp, h2, ProtCfg.pins, lookup_cons', hq1]
      · simp [hpf, hfp, h2, ProtCfg.pins, lookup_cons']
    · by_cases hfp : PortFP LG J X u
      · simp [hpf, hfp, ProtCfg.pins, lookup_cons']
      · simp [hpf, hfp, ProtCfg.pins]
  | dChild i =>
    simp only [childPin_iff hG hS hq hb i]
    by_cases hpf : PortFlower LG J X u
    · by_cases hbr : u.2 ++ X.lonePath.dropLast ++ [i] ∈ (LG.garden.tree u.1).branching
      · have hbr' : u.2 ++ (X.lonePath.dropLast ++ [i]) ∈ (LG.garden.tree u.1).branching := by
          simpa [List.append_assoc] using hbr
        by_cases hq1 : q = X.lonePath.dropLast
        · subst hq1
          have : X.lonePath.dropLast ≠ X.lonePath.dropLast ++ [i] := by simp
          simp [hpf, hbr', ProtCfg.pins]
        · simp [hpf, hbr', ProtCfg.pins, lookup_cons', hq1]
      · have hbr' : u.2 ++ (X.lonePath.dropLast ++ [i]) ∉ (LG.garden.tree u.1).branching := by
          simpa [List.append_assoc] using hbr
        have hne : q ≠ X.lonePath.dropLast ++ [i] := by
          rintro rfl
          exact hbr' (emb_branch_mem hS.emb hq)
        simp [hpf, hbr', ProtCfg.pins, lookup_cons', hne]
    · simp [hpf, ProtCfg.pins]

/-! ## Validity -/

/-- The data of a `termChild i` configuration: the child is not toward the lone leaf, is a branching vertex of the
object, and lies in layer `p`. -/
theorem termChild_data {pat : Fin w → FixPat} (hpat : CapPatValid LG J pat p)
    (hS : StemChain LG J X ζ u h) (hq0 : X.lonePath ≠ []) (hpf : PortFlower LG J X u) {i : Fin 3}
    (hpi : pat u.1 = FixPat.dChild i)
    (hbr : u.2 ++ X.lonePath.dropLast ++ [i] ∈ (LG.garden.tree u.1).branching) :
    X.lonePath.getLast? ≠ some i ∧ X.lonePath.dropLast ++ [i] ∈ (X.plug ζ .leaf).branching ∧
      layerAt LG (addrExt u (X.lonePath.dropLast ++ [i])) = p := by
  obtain ⟨f, hf, hfe⟩ := hpf
  have hlast : X.lonePath.getLast? ≠ some i := by
    intro hi
    have hP : X.lonePath = X.lonePath.dropLast ++ [i] := by
      rw [List.getLast?_eq_some_getLast hq0] at hi
      rw [← Option.some.inj hi, List.dropLast_append_getLast hq0]
    have hl := f.2
    rw [hfe] at hl
    have hl' : u.2 ++ X.lonePath.dropLast ++ [i] ∈ (LG.garden.tree u.1).leaves := by
      have : (addrExt u X.lonePath).2 = u.2 ++ X.lonePath.dropLast ++ [i] := by
        show u.2 ++ X.lonePath = _; rw [List.append_assoc, ← hP]
      rw [this] at hl; exact hl
    exact TTree.not_mem_branching_of_mem_leaves _ hl' hbr
  have hbrT : X.lonePath.dropLast ++ [i] ∈ (X.plug ζ h).branching := by
    have := (node_iff_of_subtree hS.emb.node hS.emb.tree (X.lonePath.dropLast ++ [i])).2.2.1
    exact this (by simpa [addrExt, List.append_assoc] using hbr)
  have hnot : ¬ X.lonePath <+: X.lonePath.dropLast ++ [i] := by
    intro hP
    have hlen : (X.lonePath.dropLast ++ [i]).length ≤ X.lonePath.length := by
      simp [List.length_dropLast]
      have : X.lonePath.length ≠ 0 := fun h0 => hq0 (List.length_eq_zero_iff.mp h0)
      omega
    have he := eq_of_prefix_len hP hlen
    apply hlast; rw [he]; simp
  refine ⟨hlast, branching_plug_of X ζ h hbrT hnot, ?_⟩
  have hdq : X.lonePath.dropLast <+: X.lonePath := List.dropLast_prefix _
  let c := embBr hS.emb _ (prefix_lone_branching X ζ hdq (dropLast_ne_self hq0))
  have hc : IsCapFlowerParent LG J c := port_fp hq0 ⟨f, hf, hfe⟩ c rfl
  let B : GBranch LG.garden.tree := ⟨addrExt u (X.lonePath.dropLast ++ [i]), by
    simpa [addrExt, List.append_assoc] using hbr⟩
  have hl := hpat B c i hc hpi (by simp [B, c, embBr, addrExt, List.append_assoc])
  rw [layerAt_of_mem LG (TTree.branching_subset_nodes _ B.2)]
  exact hl

/-- **(ii), validity for paired trees.** -/
theorem objCfg_valid_objTree {pat : Fin w → FixPat} (hpat : CapPatValid LG J pat p)
    (hS : StemChain LG J X ζ u h) : (objCfg LG J pat X u).Valid X (objTree LG X ζ u hS.emb) p := by
  obtain ⟨v, hv, -⟩ := hS.meets
  obtain ⟨q, hq, -⟩ := mem_branchAddresses'.mp hv
  have hq0 := lone_ne_nil_of_branch X ζ hq
  cases hp : pat u.1 with
  | plain => simp only [objCfg, hp]; split_ifs <;> first | exact hq0 | trivial
  | dRoot => simp only [objCfg, hp]; split_ifs with h1 h2 <;> first | exact hq0 | exact h2.2 | trivial
  | dParent => simp only [objCfg, hp]; split_ifs with h1 h2 <;> first | exact hq0 | exact h2 | trivial
  | dChild i =>
    simp only [objCfg, hp]
    split_ifs with h1 h2
    · obtain ⟨hl, hbr, hlay⟩ := termChild_data hpat hS hq0 h1 hp h2
      exact ⟨hq0, hl, ⟨((0 : Fin 1), X.lonePath.dropLast ++ [i]), hbr⟩, rfl, rfl, hlay⟩
    · exact hq0
    · trivial

/-- **(ii), validity for cap couples** (code `normChain ζ X`, same lone path). -/
theorem objCfg_valid_objCpl {pat : Fin w → FixPat} (hpat : CapPatValid LG J pat p)
    {c : Fin w} (hC : CapChain LG J X ζ u c) :
    (objCfg LG J pat X u).Valid (normChain ζ X) (objCpl LG X ζ u c hC.stem.emb hC.pair) p := by
  have hS := hC.stem
  obtain ⟨v, hv, -⟩ := hS.meets
  obtain ⟨q, hq, -⟩ := mem_branchAddresses'.mp hv
  have hq0 := lone_ne_nil_of_branch X ζ hq
  have hL := normChain_lonePath ζ X
  have hq0' : (normChain ζ X).lonePath ≠ [] := by rw [hL]; exact hq0
  have hlen : (normChain ζ X).lonePath.length = X.lonePath.length := by rw [hL]
  cases hp : pat u.1 with
  | plain => simp only [objCfg, hp]; split_ifs <;> first | exact hq0' | trivial
  | dRoot =>
    simp only [objCfg, hp]
    split_ifs with h1 h2 <;> first | exact hq0' | exact (hlen ▸ h2.2 : 2 ≤ (normChain ζ X).lonePath.length) | trivial
  | dParent =>
    simp only [objCfg, hp]
    split_ifs with h1 h2 <;> first | exact hq0' | exact (hlen ▸ h2 : 2 ≤ (normChain ζ X).lonePath.length) | trivial
  | dChild i =>
    simp only [objCfg, hp]
    split_ifs with h1 h2
    · obtain ⟨hl, hbr, hlay⟩ := termChild_data hpat hS hq0 h1 hp h2
      have hbr' : X.lonePath.dropLast ++ [i] ∈ ((decodedCouple (capCode ζ X)).tree 0).branching := by
        rw [decodedCouple_capCode_tree]; simpa using hbr
      refine ⟨hq0', by rw [hL]; exact hl, ⟨((0 : Fin 2), X.lonePath.dropLast ++ [i]), hbr'⟩,
        rfl, by rw [hL], ?_⟩
      show cplLayer LG u c ((0 : Fin 2), X.lonePath.dropLast ++ [i]) = p
      rw [cplLayer_of_zero rfl]; exact hlay
    · exact hq0'
    · trivial

/-! ## Extraction forms -/

/-- **(ii), paired trees.** `fixCap` at the lifted branch equals `ProtCfg.fix` of `objCfg` on `objTree`. -/
theorem fixCap_objTree (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) (pat : Fin w → FixPat) (t s up : ℝ)
    (b' : GBranch (objTree LG X ζ u hS.emb).garden.tree) :
    fixCap LG J pat t s (embBr hS.emb b'.1.2 b'.2) = (objCfg LG J pat X u).fix X s t up b' := by
  rw [fixCap_eq_pins hG hS pat t s up (q := b'.1.2) b'.2 rfl]
  unfold ProtCfg.fix
  rw [ite_eq_left (Fin.val_eq_zero b'.1.1)]

/-- **(ii), cap couples.** `fixCap` at the lifted branch equals `ProtCfg.fix` of `objCfg` on `objCpl`. -/
theorem fixCap_objCpl (hG : CapGeo LG J p) {c : Fin w} (hC : CapChain LG J X ζ u c) (pat : Fin w → FixPat)
    (t s up : ℝ) (b' : GBranch (objCpl LG X ζ u c hC.stem.emb hC.pair).garden.tree) :
    fixCap LG J pat t s (embBr hC.stem.emb b'.1.2 (capCode_branch b').2) =
      (objCfg LG J pat X u).fix (normChain ζ X) s t up b' := by
  rw [fixCap_eq_pins hG hC.stem pat t s up (q := b'.1.2) (capCode_branch b').2 rfl]
  unfold ProtCfg.fix
  have h0 : b'.1.1.val = 0 := congrArg Fin.val (capCode_branch b').1
  rw [ite_eq_left h0, pins_congr _ (normChain_lonePath ζ X).symm]

end WaveTurbulence.Flower.ProtGeo

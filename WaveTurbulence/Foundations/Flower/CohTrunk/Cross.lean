/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Lay
public import WaveTurbulence.Foundations.Spine.PL234Draft.BlockLayers
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Spine
public import WaveTurbulence.Foundations.IncohInst.Links.Bridge
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks

/-!
# COH-TRUNK: the unique frontier crossing along a layered chain (Lemma 5.1)

For a layered chain `X` embedded at `a` in a layered garden, with root parent layer `u ≤ p`, the nodes that cross
the frontier (layer `< p`, parent layer `= p`) form a single node of the spine, present iff `u = p` and the lone
position lies below `p` (`chain_cross`).  The decoration momentum is constant along the spine (`spine_dec`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CohTrunk
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree

variable {w : ℕ} {LG : LayeredGarden w} {p : ℕ}

/-- The frontier-crossing predicate at an address; the chain root `a` has parent layer `u`. -/
def Cr (LG : LayeredGarden w) (p : ℕ) (a : Fin w × Path) (u : ℕ) (z : Fin w × Path) : Prop :=
  layerAt LG z < p ∧ (if z = a then u else parAt LG p z) = p

theorem parAt_le_layer_of_under {x z : Fin w × Path} (hx : x.2 ∈ (LG.garden.tree x.1).nodes)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (hu : Under x z) (hne : z ≠ x) :
    parAt LG p z ≤ layerAt LG x := by
  obtain ⟨h1, q, hq⟩ := hu
  have hq0 : q ≠ [] := by
    rintro rfl
    apply hne
    exact Prod.ext h1.symm (by simpa using hq.symm)
  have hz2 : z.2 ≠ [] := by
    rw [← hq]
    simp [hq0]
  rw [parAt_of_mem LG p hz]
  unfold LayeredGarden.parentLayer
  rw [if_neg hz2]
  have hpar : ((z.1, z.2.dropLast) : Fin w × Path).2 ∈
      (LG.garden.tree (z.1, z.2.dropLast).1).nodes := TTree.dropLast_mem_nodes _ hz
  have hU : Under x ((z.1, z.2.dropLast) : Fin w × Path) := by
    refine ⟨h1, q.dropLast, ?_⟩
    show x.2 ++ q.dropLast = z.2.dropLast
    rw [← hq, List.dropLast_append_of_ne_nil hq0]
  have h3 := layerAt_le_of_under LG hx hpar hU
  rw [layerAt_of_mem LG hpar] at h3
  exact h3

theorem own_layer {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ} {a : Fin w × Path}
    {h : TTree} (hC : ChainEmb LG.garden (.pair m Qr Qg inner rest) ζ a h)
    (hL : ChainPairLayers LG (.pair m Qr Qg inner rest) ζ a) {z : Fin w × Path}
    (hz : OwnPart m Qr Qg inner ζ a z) : layerAt LG z = layerAt LG a := by
  obtain ⟨hb, hr, hg, hi, hs⟩ := hL
  obtain ⟨-, -, hCi, -⟩ := hC.parts
  have nA := hC.node
  have nI := hCi.node
  have nB := nodeOfChainEmb hCi
  have eB : addrExt (addrExt a [m.c]) inner.lonePath = addrExt a ([m.c] ++ inner.lonePath) :=
    addrExt_append _ _ _
  rw [eB] at nB
  have lI : layerAt LG (addrExt a [m.c]) = layerAt LG a :=
    layer_sandwich nA nI nB (under_ext a _) (by rw [← eB]; exact under_ext _ _) rfl hb
  rcases hz with rfl | rfl | hz | hz | hz
  · rfl
  · exact hb
  · exact hr z hz
  · exact hg z hz
  · exact chainNodes_layer_of_ends hCi hi lI (by rw [eB]; exact hb) z hz

theorem lone_mem_spinePos : ∀ (X : RegChain) (a : Fin w × Path), addrExt a X.lonePath ∈ spinePos X a
  | .nil, a => by simp [spinePos, RegChain.lonePath, addrExt_nil]
  | .pair m Qr Qg inner rest, a => by
    have hsp : spinePos (.pair m Qr Qg inner rest) a =
        a :: spinePos rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := rfl
    rw [hsp, chain_lonePath_eq m Qr Qg inner rest a]
    exact List.mem_cons_of_mem _ (lone_mem_spinePos rest _)

theorem chain_cross (hp : ∀ z : GNode LG.garden.tree, LG.layer z ≤ p) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (h : TTree), ChainEmb LG.garden X ζ a h →
      ChainPairLayers LG X ζ a → ∀ u : ℕ, layerAt LG a ≤ u → u ≤ p →
      (∀ z ∈ chainNodesSet X ζ a, Cr LG p a u z → z ∈ spinePos X a) ∧
      (∀ z ∈ spinePos X a, ∀ z' ∈ spinePos X a, Cr LG p a u z → Cr LG p a u z' → z = z') ∧
      ((∃ z ∈ spinePos X a, Cr LG p a u z) ↔ (u = p ∧ layerAt LG (addrExt a X.lonePath) < p))
  | .nil, ζ, a, h, hC, hPL, u, hu, hup => by
    refine ⟨fun z hz => ?_, ?_, ?_⟩
    · simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt] at hz
    · intro z hz z' hz' _ _
      simp only [spinePos, List.mem_singleton] at hz hz'
      rw [hz, hz']
    · simp only [spinePos, List.mem_singleton, exists_eq_left, Cr, RegChain.lonePath, addrExt_nil,
        if_true]
      exact and_comm
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hPL, u, hu, hup => by
    obtain ⟨-, -, -, ES⟩ := hC.parts
    have hPLr := hPL.2.2.2.2
    have nA := hC.node
    have nN := ES.node
    have hlone_node := nodeOfChainEmb hC
    have hb : layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) = layerAt LG a := hPL.1
    have hparN : parAt LG p (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) = layerAt LG a := by
      rw [parAt_bottom ([m.c] ++ inner.lonePath) m.lone nN, hb]
    have hmono : layerAt LG (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) ≤ layerAt LG a :=
      layerAt_le_of_under LG nA nN (under_ext a _)
    have hl : layerAt LG a ≤ p := hu.trans hup
    have hlone : layerAt LG (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) ≤ layerAt LG a :=
      layerAt_le_of_under LG nA hlone_node (under_ext a _)
    have hsub : ∀ z, Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z → z ≠ a ∧ Under a z := by
      intro z hz
      refine ⟨fun hza => ?_, under_trans (under_ext a _) hz⟩
      have h1 := under_length hz
      subst hza
      simp [addrExt] at h1
    have hsp : spinePos (.pair m Qr Qg inner rest) a =
        a :: spinePos rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := rfl
    have hsp' : ∀ y ∈ spinePos (.pair m Qr Qg inner rest) a,
        Under a y ∧ y.2 ∈ (LG.garden.tree y.1).nodes := by
      intro y hy
      rw [hsp] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨under_refl _, nA⟩
      · exact ⟨under_trans (under_ext a _) (spinePos_under _ _ y hy).1, spinePos_node ES hy⟩
    have hCriff : ∀ z, Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z →
        (Cr LG p a u z ↔
          Cr LG p (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (layerAt LG a) z) := by
      intro z hz
      have hza := (hsub z hz).1
      unfold Cr
      by_cases hzn : z = addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])
      · subst hzn
        rw [if_neg hza, if_pos rfl, hparN]
      · rw [if_neg hza, if_neg hzn]
    rcases lt_or_eq_of_le hl with hlt | heq
    · have noCr : ∀ z, z.2 ∈ (LG.garden.tree z.1).nodes → Under a z → z ≠ a → ¬ Cr LG p a u z := by
        intro z hz huz hne hc
        obtain ⟨h1, h2⟩ := hc
        rw [if_neg hne] at h2
        have := parAt_le_layer_of_under (p := p) nA hz huz hne
        omega
      have crEq : ∀ z, z.2 ∈ (LG.garden.tree z.1).nodes → Under a z → Cr LG p a u z → z = a :=
        fun z hz huz hc => by_contra fun hne => noCr z hz huz hne hc
      refine ⟨?_, ?_, ?_⟩
      · intro z hz hc
        have := crEq z (hC.mem_nodes hz) (chainNodes_region _ _ _ z hz).1 hc
        rw [hsp, this]
        exact List.mem_cons_self
      · intro z hz z' hz' hc hc'
        rw [crEq z (hsp' z hz).2 (hsp' z hz).1 hc, crEq z' (hsp' z' hz').2 (hsp' z' hz').1 hc']
      · constructor
        · rintro ⟨z, hz, hc⟩
          have hza := crEq z (hsp' z hz).2 (hsp' z hz).1 hc
          subst hza
          obtain ⟨h1, h2⟩ := hc
          rw [if_pos rfl] at h2
          exact ⟨h2, lt_of_le_of_lt hlone hlt⟩
        · rintro ⟨hu', _⟩
          refine ⟨a, by rw [hsp]; exact List.mem_cons_self, hlt, ?_⟩
          rw [if_pos rfl]
          exact hu'
    · have hup' : u = p := by
        rw [heq] at hu
        exact le_antisymm hup hu
      have hCa : ¬ Cr LG p a u a := fun hc => by
        have := hc.1
        omega
      have hOwn : ∀ z, OwnPart m Qr Qg inner ζ a z → ¬ Cr LG p a u z := by
        intro z hz hc
        have h1 := hc.1
        rw [own_layer hC hPL hz, heq] at h1
        omega
      obtain ⟨ihA, ihB, ihC⟩ := chain_cross hp rest _ _ _ ES hPLr (layerAt LG a) hmono hl
      refine ⟨?_, ?_, ?_⟩
      · intro z hz hc
        rcases ownPart_of_mem hz with ho | hr
        · exact absurd hc (hOwn z ho)
        · rw [hsp]
          exact List.mem_cons_of_mem _
            (ihA z hr ((hCriff z (chainNodes_region _ _ _ z hr).1).1 hc))
      · intro z hz z' hz' hc hc'
        rw [hsp] at hz hz'
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hc hCa
        rcases List.mem_cons.mp hz' with rfl | hz'
        · exact absurd hc' hCa
        exact ihB z hz z' hz' ((hCriff z (spinePos_under _ _ z hz).1).1 hc)
          ((hCriff z' (spinePos_under _ _ z' hz').1).1 hc')
      · rw [hsp, chain_lonePath_eq m Qr Qg inner rest a]
        constructor
        · rintro ⟨z, hz, hc⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · exact absurd hc hCa
          · exact ⟨hup', (ihC.1 ⟨z, hz, (hCriff z (spinePos_under _ _ z hz).1).1 hc⟩).2⟩
        · rintro ⟨_, hlt'⟩
          obtain ⟨z, hz, hc⟩ := ihC.2 ⟨heq, hlt'⟩
          exact ⟨z, List.mem_cons_of_mem _ hz, (hCriff z (spinePos_under _ _ z hz).1).2 hc⟩

/-! ### The decoration momentum is constant along the spine -/

section Dec

variable {V : Type*} [AddCommGroup V]

theorem chainDec_next_eq (f : Fin w × Path → V) {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain}
    {ζ : ℤˣ} {a : Fin w × Path} (h : ChainDec f (.pair m Qr Qg inner rest) ζ a) :
    f a = f (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := by
  obtain ⟨ha, hb, hr, hg, hi, hs⟩ := h
  have er := oriented_eq (fun x y hh => cplDec_root_eq f Qr x y hh) hr
  have eg := oriented_eq (fun x y hh => cplDec_root_eq f Qg x y hh) hg
  have ei := chainDec_lone_eq f inner _ _ hi
  rw [addrExt_append] at ei
  exact miniTree_local m (f a) (f (addrExt a ([m.c] ++ inner.lonePath)))
    (fun i => f (addrExt a [i])) (fun i => f (addrExt a ([m.c] ++ inner.lonePath ++ [i])))
    ha (by rw [hb]; simp only [addrExt_append, List.append_assoc]) ei er eg

theorem spine_dec (f : Fin w × Path → V) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path), ChainDec f X ζ a → ∀ s ∈ spinePos X a, f s = f a
  | .nil, ζ, a, _, s, hs => by
    simp only [spinePos, List.mem_singleton] at hs
    rw [hs]
  | .pair m Qr Qg inner rest, ζ, a, h, s, hs => by
    have hsp : spinePos (.pair m Qr Qg inner rest) a =
        a :: spinePos rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := rfl
    rw [hsp] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · rfl
    · rw [spine_dec f rest _ _ h.2.2.2.2.2 s hs]
      exact (chainDec_next_eq f h).symm

end Dec

end WaveTurbulence.Flower.CohTrunk

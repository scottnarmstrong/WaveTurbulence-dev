/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootCut

/-! # D2c PROT-CUT: the root cut — configurations, existence, sizes, multiplier

* `cfg_root_fix`, `cfg_trace_fix`: `ProtCfg.root.fix X s t up = rootFix t`, `ProtCfg.trace.fix X s t up = rootFix up`.
* **`RootData.exists_of_wf`**: the pieces of the root cut exist for a well-formed code `pair m Qr Qg inner rest`
  (`rest ≠ nil`) decoding `LG`.
* `size_rootCut`: `X.size = rest.size + inner.size + Qr.size + Qg.size + 2`.
* **`RootData.multFactors_local`**: a branch-local multiplier factors at the root cut (D3's multiplier for the
  configurations `root`, `trace`, where `ind = 1`: `starFilt_local`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-! ### The configurations -/

theorem cfg_root_fix (X : RegChain) (s t up : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.root.fix X s t up : GBranch T → Option ℝ) = rootFix t := by
  funext b
  unfold ProtCfg.fix rootFix ProtCfg.pins
  rw [if_pos (Fin.val_eq_zero _)]
  by_cases h : b.1.2 = []
  · rw [h, if_pos rfl]; rfl
  · rw [if_neg h]
    obtain ⟨⟨j, p⟩, hp⟩ := b
    cases p with
    | nil => exact absurd rfl h
    | cons a l => rfl

theorem cfg_trace_fix (X : RegChain) (s t up : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.trace.fix X s t up : GBranch T → Option ℝ) = rootFix up := by
  funext b
  unfold ProtCfg.fix rootFix ProtCfg.pins
  rw [if_pos (Fin.val_eq_zero _)]
  by_cases h : b.1.2 = []
  · rw [h, if_pos rfl]; rfl
  · rw [if_neg h]
    obtain ⟨⟨j, p⟩, hp⟩ := b
    cases p with
    | nil => exact absurd rfl h
    | cons a l => rfl

theorem size_rootCut (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) :
    (RegChain.pair m Qr Qg inner rest).size = rest.size + inner.size + Qr.size + Qg.size + 2 := by
  simp only [RegChain.size]
  ring

/-! ### Existence of the pieces -/

/-- **The pieces of the root cut exist.** -/
theorem RootData.exists_of_wf (LG : LayeredGarden 1) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain)
    (hX : (RegChain.pair m Qr Qg inner rest).DecodesTree LG.garden)
    (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) (hrest : rest ≠ .nil) :
    ∃ (LGZ LGi LGs : LayeredGarden 1) (LGr LGg : LayeredGarden 2),
      RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg := by
  set ζ := LG.garden.sig 0
  have hX' : (appendChain (cpair m Qr Qg inner) rest).DecodesTree LG.garden := hX
  have hwf' := hwf
  simp only [RegChain.wf, Bool.and_eq_true] at hwf'
  obtain ⟨⟨⟨hwr, hwg⟩, hwi⟩, hws⟩ := hwf'
  have hwZ : (cpair m Qr Qg inner).wf = true := by
    simp [cpair, RegChain.wf, hwr, hwg, hwi]
  obtain ⟨GZ, hsZ, hdZ, -⟩ := Reg.wf_chain_exists_regular_decodesTree _ hwZ ζ
  obtain ⟨Gs, hss, hds, -⟩ := Reg.wf_chain_exists_regular_decodesTree rest hws ζ
  obtain ⟨Gi, hsi, hdi, -⟩ := Reg.wf_chain_exists_regular_decodesTree inner hwi (slotSign ζ m.c)
  obtain ⟨Gr, hdr, -⟩ := Reg.wf_code_exists_regular_decodes Qr hwr
  obtain ⟨Gg, hdg, -⟩ := Reg.wf_code_exists_regular_decodes Qg hwg
  have gd : GlueData LG.garden GZ Gs (cpair m Qr Qg inner) := glueData_tree hX' hdZ hsZ hds hss
  have hp : PairData m Qr Qg inner GZ Gi Gr Gg := ⟨hdZ, hdi, by rw [hsi, hsZ], hdr, hdg⟩
  -- the placements
  let φz : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), x.2)
  let φs : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), lonePos m inner ++ x.2)
  let φi : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), m.c :: x.2)
  let φr : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), rBase m inner ζ x.1 ++ x.2)
  let φg : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), gBase m inner ζ x.1 ++ x.2)
  have hφz : ∀ x q, φz (addrExt x q) = addrExt (φz x) q := by intro x q; simp [φz, addrExt]
  have hφs : ∀ x q, φs (addrExt x q) = addrExt (φs x) q := by intro x q; simp [φs, addrExt]
  have hφi : ∀ x q, φi (addrExt x q) = addrExt (φi x) q := by intro x q; simp [φi, addrExt]
  have hφr : ∀ x q, φr (addrExt x q) = addrExt (φr x) q := by intro x q; simp [φr, addrExt]
  have hφg : ∀ x q, φg (addrExt x q) = addrExt (φg x) q := by intro x q; simp [φg, addrExt]
  -- the pairs of X
  have hXpairs : (appendChain (cpair m Qr Qg inner) rest).pairsAt ζ ((0 : Fin 1), []) =
      (cpair m Qr Qg inner).pairsAt ζ ((0 : Fin 1), []) ++ rest.pairsAt ζ ((0 : Fin 1), lonePos m inner) := by
    rw [appendChain_pairsAt, cpair_lonePath]; simp [addrExt]
  have hZpairs : ∀ p ∈ (cpair m Qr Qg inner).pairsAt ζ ((0 : Fin 1), []),
      p ∈ (RegChain.pair m Qr Qg inner rest).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    show p ∈ (appendChain (cpair m Qr Qg inner) rest).pairsAt ζ ((0 : Fin 1), [])
    rw [hXpairs]; exact List.mem_append_left _ hp'
  -- branch placements
  have bZ : ∀ x : GBranch GZ.tree, (φz x.1).2 ∈ (LG.garden.tree (φz x.1).1).branching :=
    fun x => (gd.ofSum (.inl x)).2
  have bS : ∀ x : GBranch Gs.tree, (φs x.1).2 ∈ (LG.garden.tree (φs x.1).1).branching := by
    intro x
    have h := (gd.ofSum (.inr x)).2
    rw [glue_ofSum_inr_path gd, cpair_lonePath] at h
    exact h
  have bI : ∀ x : GBranch Gi.tree, (φi x.1).2 ∈ (LG.garden.tree (φi x.1).1).branching :=
    fun x => (gd.ofSum (.inl (hp.βi x))).2
  have bR : ∀ x : GBranch Gr.tree, (φr x.1).2 ∈ (LG.garden.tree (φr x.1).1).branching := by
    intro x
    have h := (gd.ofSum (.inl (hp.βr x))).2
    simpa [PairData.βr, hsZ, φr, GlueData.ofSum, topAddr] using h
  have bG : ∀ x : GBranch Gg.tree, (φg x.1).2 ∈ (LG.garden.tree (φg x.1).1).branching := by
    intro x
    have h := (gd.ofSum (.inl (hp.βg x))).2
    simpa [PairData.βg, hsZ, φg, GlueData.ofSum, topAddr] using h
  -- pair inclusions
  have sZ : ∀ p ∈ (cpair m Qr Qg inner).pairsAt (GZ.sig 0) (φz ((0 : Fin 1), [])),
      p ∈ (RegChain.pair m Qr Qg inner rest).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    rw [hsZ] at hp'
    exact hZpairs p (by simpa [φz] using hp')
  have sS : ∀ p ∈ rest.pairsAt (Gs.sig 0) (φs ((0 : Fin 1), [])),
      p ∈ (RegChain.pair m Qr Qg inner rest).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    show p ∈ (appendChain (cpair m Qr Qg inner) rest).pairsAt ζ ((0 : Fin 1), [])
    rw [hXpairs, hss] at *
    exact List.mem_append_right _ (by simpa [φs] using hp')
  have sI : ∀ p ∈ inner.pairsAt (Gi.sig 0) (φi ((0 : Fin 1), [])),
      p ∈ (RegChain.pair m Qr Qg inner rest).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    refine hZpairs p ?_
    simp only [cpair, RegChain.pairsAt, List.mem_append]
    left; right
    rw [hsi] at hp'
    simpa [φi, addrExt] using hp'
  have sR : ∀ p ∈ Qr.pairsAt (φr ((0 : Fin 2), [])) (φr ((1 : Fin 2), [])),
      p ∈ (RegChain.pair m Qr Qg inner rest).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    refine hZpairs p ?_
    simp only [cpair, RegChain.pairsAt, List.mem_append]
    left; left; left
    by_cases hs : slotSign ζ m.red.1 = 1 <;> simpa [φr, rBase, hs, addrExt, bPath] using hp'
  have sG : ∀ p ∈ Qg.pairsAt (φg ((0 : Fin 2), [])) (φg ((1 : Fin 2), [])),
      p ∈ (RegChain.pair m Qr Qg inner rest).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    refine hZpairs p ?_
    simp only [cpair, RegChain.pairsAt, List.mem_append]
    left; left; right
    by_cases hs : slotSign ζ m.green.1 = 1 <;> simpa [φg, gBase, hs, addrExt, bPath] using hp'
  refine ⟨⟨GZ, fun z => layerAt LG (φz z.1),
      isLayering_pullback LG GZ φz hφz bZ (pair_layer_tree LG hX hdZ φz hφz sZ)⟩,
    ⟨Gi, fun z => layerAt LG (φi z.1),
      isLayering_pullback LG Gi φi hφi bI (pair_layer_tree LG hX hdi φi hφi sI)⟩,
    ⟨Gs, fun z => layerAt LG (φs z.1),
      isLayering_pullback LG Gs φs hφs bS (pair_layer_tree LG hX hds φs hφs sS)⟩,
    ⟨Gr, fun z => layerAt LG (φr z.1),
      isLayering_pullback LG Gr φr hφr bR (pair_layer_couple LG hX hdr φr hφr sR)⟩,
    ⟨Gg, fun z => layerAt LG (φg z.1),
      isLayering_pullback LG Gg φg hφg bG (pair_layer_couple LG hX hdg φg hφg sG)⟩,
    ⟨hX, hrest, hdZ, hsZ, hds, hss, hdi, hsi, hdr, hdg, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl⟩⟩

/-! ### The multiplier -/

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

theorem prod_branch_root {α : Type*} [CommMonoid α] (φ : GBranch LG.garden.tree → α) :
    ∏ b, φ b = φ D.aR * φ D.bR * ((∏ y, φ (D.gd.ofSum (.inr y))) * ((∏ x, φ (D.gd.ofSum (.inl (D.hp.βi x)))) *
      ((∏ y, φ (D.gd.ofSum (.inl (D.hp.βr y)))) * ∏ y, φ (D.gd.ofSum (.inl (D.hp.βg y)))))) := by
  rw [D.gd.prod_branch, D.hp.prod_pairBranch (fun x => φ (D.gd.ofSum (.inl x)))]
  unfold aR bR
  ac_rfl

theorem bstar_inl {d : ℕ} (K : GNode LG.garden.tree → Mom d) (x : GBranch LGZ.garden.tree) :
    bstar K (D.gd.ofSum (.inl x)) = bstar (K ∘ D.gd.ι₁) x := by
  funext i
  exact Fin.cases rfl (fun j => rfl) i

theorem bstar_inr {d : ℕ} (K : GNode LG.garden.tree → Mom d) (y : GBranch LGs.garden.tree) :
    bstar K (D.gd.ofSum (.inr y)) = bstar (K ∘ D.ιS) y := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact congrArg K (D.gd.ofSum_inr_child y j)

theorem bstar_aR {d : ℕ} (K : GNode LG.garden.tree → Mom d) :
    (fun i => extend K (aAddr .nil i)) = bstar K D.aR := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact extend_node K D.aR.toNode
  · exact extend_node K (D.aR.child j)

theorem bstar_bR {d : ℕ} (K : GNode LG.garden.tree → Mom d) :
    (fun i => extend K (bAddr .nil m inner i)) = bstar K D.bR := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have e : bAddr .nil m inner 0 = D.bR.toNode.1 := by
      simp only [bAddr, RegChain.lonePath, List.nil_append, Fin.cases_zero] <;> rfl
    rw [e]
    exact extend_node K D.bR.toNode
  · have e : bAddr .nil m inner j.succ = (D.bR.child j).1 := by
      simp only [bAddr, RegChain.lonePath, List.nil_append, Fin.cases_succ] <;> rfl
    rw [e]
    exact extend_node K (D.bR.child j)

/-- **A branch-local multiplier factors at the root cut.** -/
theorem multFactors_local {d : ℕ} (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) :
    D.MultFactors (fun K => ∏ b, f b (bstar K b))
      (fun A B => f D.aR A * f D.bR B)
      (fun K => ∏ x, f (D.gd.ofSum (.inl (D.hp.βi x))) (bstar K x))
      (fun K => ∏ y, f (D.gd.ofSum (.inl (D.hp.βr y))) (bstar K y))
      (fun K => ∏ y, f (D.gd.ofSum (.inl (D.hp.βg y))) (bstar K y))
      (fun K => ∏ y, f (D.gd.ofSum (.inr y)) (bstar K y)) := by
  intro K
  simp only
  rw [D.bstar_aR K, D.bstar_bR K, D.prod_branch_root]
  have hi : ∀ x, bstar K (D.gd.ofSum (.inl (D.hp.βi x))) = bstar (K ∘ D.ιI) x := by
    intro x; rw [D.bstar_inl]; funext i; exact Fin.cases rfl (fun j => rfl) i
  have hr : ∀ y, bstar K (D.gd.ofSum (.inl (D.hp.βr y))) = bstar (K ∘ D.ιR) y := by
    intro y; rw [D.bstar_inl]; funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg (K ∘ D.gd.ι₁) (D.hp.βr_child y j)
  have hg : ∀ y, bstar K (D.gd.ofSum (.inl (D.hp.βg y))) = bstar (K ∘ D.ιG) y := by
    intro y; rw [D.bstar_inl]; funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg (K ∘ D.gd.ι₁) (D.hp.βg_child y j)
  simp only [D.bstar_inr, hi, hr, hg]

end RootData

end WaveTurbulence.Flower.ProtCut

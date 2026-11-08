/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildOps
public import WaveTurbulence.Foundations.Flower.ProtPin.PieceStar
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStar
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckD2c3

/-! # D3 PROT-PIN (P7): the bookkeeping of a type-1 couple (o104 Prop 7.4 (b))

For `T1Data c Q₁ Q₂ Q₃ LGr LG₁ LG₂ LG₃` with the layers of `LGr`: sizes and well-formedness of the three sub-couples,
the incoherency split (`tc_t1_incoh`, with the root link), the input leaves and leaf control, the piece embeddings, D3's
multiplier in gate form on the sub-couples (`tc_t1_mult`), the star cost split (`tc_t1_cost`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}

/-! ### Sizes -/

theorem tc_t1_wf (hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true) : Q₁.wf = true ∧ Q₂.wf = true ∧ Q₃.wf = true := by
  simp only [RegCpl.wf, Bool.and_eq_true] at hwf
  exact ⟨hwf.1.1, hwf.1.2, hwf.2⟩

theorem tc_t1_sizes {n : ℕ} (hsz : (RegCpl.type1 c Q₁ Q₂ Q₃).size = 2 * n) :
    ∃ n₁ n₂ n₃ : ℕ, Q₁.size = 2 * n₁ ∧ Q₂.size = 2 * n₂ ∧ Q₃.size = 2 * n₃ ∧ n₁ + n₂ + n₃ + 1 = n := by
  obtain ⟨n₁, h₁⟩ := code_size_even Q₁
  obtain ⟨n₂, h₂⟩ := code_size_even Q₂
  obtain ⟨n₃, h₃⟩ := code_size_even Q₃
  refine ⟨n₁, n₂, n₃, by omega, by omega, by omega, ?_⟩
  simp only [RegCpl.size] at hsz
  omega

/-! ### Layers, leaves -/

section Data

variable (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
include h

theorem tc_t1_layerA (hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (x : Fin 2 × Path)
    (hx : x.2 ∈ (LG₁.garden.tree x.1).nodes) :
    layerAt LG₁ x = layerAt LGr (t1A c x) :=
  (layerAt_node LG₁ (⟨x, hx⟩ : GNode LG₁.garden.tree)).trans ((hlA _).trans (layerAt_node LGr (h.ιA ⟨x, hx⟩)).symm)

theorem tc_t1_layerB (hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z)) (x : Fin 2 × Path)
    (hx : x.2 ∈ (LG₂.garden.tree x.1).nodes) :
    layerAt LG₂ x = layerAt LGr (t1B x) :=
  (layerAt_node LG₂ (⟨x, hx⟩ : GNode LG₂.garden.tree)).trans ((hlB _).trans (layerAt_node LGr (h.ιB ⟨x, hx⟩)).symm)

theorem tc_t1_layerC (hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z)) (x : Fin 2 × Path)
    (hx : x.2 ∈ (LG₃.garden.tree x.1).nodes) :
    layerAt LG₃ x = layerAt LGr (t1C c x) :=
  (layerAt_node LG₃ (⟨x, hx⟩ : GNode LG₃.garden.tree)).trans ((hlC _).trans (layerAt_node LGr (h.ιC ⟨x, hx⟩)).symm)

/-- **The incoherency of a type-1 couple splits**, with its root link. -/
theorem tc_t1_incoh (hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z)) :
    LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links =
      LG₁.incoherency Q₁.links + LG₂.incoherency Q₂.links + LG₃.incoherency Q₃.links +
        (if layerAt LGr ((0 : Fin 2), []) = layerAt LGr ((1 : Fin 2), []) then 0 else 1) := by
  set P : (Fin 2 × Path) × (Fin 2 × Path) → Bool := fun l => decide (layerAt LGr l.1 ≠ layerAt LGr l.2)
  rw [incoherency_eq_count h.dec, incoherency_eq_count h.dec₁, incoherency_eq_count h.dec₂,
    incoherency_eq_count h.dec₃]
  have hA : (Q₁.linksAt (t1A c ((0 : Fin 2), [])) (t1A c ((1 : Fin 2), []))).filter P =
      ((Q₁.links).filter (fun l => layerAt LG₁ l.1 ≠ layerAt LG₁ l.2)).map (fun l => (t1A c l.1, t1A c l.2)) := by
    rw [couple_linksAt_map Q₁ (t1A c) (t1A_hom c), RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching h.dec₁ hl
    simp only [Function.comp_apply, P]
    rw [tc_t1_layerA h hlA l.1 (TTree.branching_subset_nodes _ hb.1),
      tc_t1_layerA h hlA l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  have hB : (Q₂.linksAt (t1B ((0 : Fin 2), [])) (t1B ((1 : Fin 2), []))).filter P =
      ((Q₂.links).filter (fun l => layerAt LG₂ l.1 ≠ layerAt LG₂ l.2)).map (fun l => (t1B l.1, t1B l.2)) := by
    rw [couple_linksAt_map Q₂ t1B t1B_hom, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching h.dec₂ hl
    simp only [Function.comp_apply, P]
    rw [tc_t1_layerB h hlB l.1 (TTree.branching_subset_nodes _ hb.1),
      tc_t1_layerB h hlB l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  have hC : (Q₃.linksAt (t1C c ((0 : Fin 2), [])) (t1C c ((1 : Fin 2), []))).filter P =
      ((Q₃.links).filter (fun l => layerAt LG₃ l.1 ≠ layerAt LG₃ l.2)).map (fun l => (t1C c l.1, t1C c l.2)) := by
    rw [couple_linksAt_map Q₃ (t1C c) (t1C_hom c), RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching h.dec₃ hl
    simp only [Function.comp_apply, P]
    rw [tc_t1_layerC h hlC l.1 (TTree.branching_subset_nodes _ hb.1),
      tc_t1_layerC h hlC l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  have hL : (RegCpl.type1 c Q₁ Q₂ Q₃).links =
      (((0 : Fin 2), []), ((1 : Fin 2), [])) ::
        (Q₁.linksAt (t1A c ((0 : Fin 2), [])) (t1A c ((1 : Fin 2), [])) ++
          Q₂.linksAt (t1B ((0 : Fin 2), [])) (t1B ((1 : Fin 2), [])) ++
          Q₃.linksAt (t1C c ((0 : Fin 2), [])) (t1C c ((1 : Fin 2), []))) := by
    rfl
  rw [hL]
  simp only [List.filter_append, List.filter_cons]
  rw [show List.filter (fun l => decide (layerAt LGr l.1 ≠ layerAt LGr l.2))
      (Q₁.linksAt (t1A c ((0 : Fin 2), [])) (t1A c ((1 : Fin 2), []))) =
      (Q₁.linksAt (t1A c ((0 : Fin 2), [])) (t1A c ((1 : Fin 2), []))).filter P from rfl, hA,
    show List.filter (fun l => decide (layerAt LGr l.1 ≠ layerAt LGr l.2))
      (Q₂.linksAt (t1B ((0 : Fin 2), [])) (t1B ((1 : Fin 2), []))) =
      (Q₂.linksAt (t1B ((0 : Fin 2), [])) (t1B ((1 : Fin 2), []))).filter P from rfl, hB,
    show List.filter (fun l => decide (layerAt LGr l.1 ≠ layerAt LGr l.2))
      (Q₃.linksAt (t1C c ((0 : Fin 2), [])) (t1C c ((1 : Fin 2), []))) =
      (Q₃.linksAt (t1C c ((0 : Fin 2), [])) (t1C c ((1 : Fin 2), []))).filter P from rfl, hC]
  try simp only [List.length_map]
  split_ifs with h1 h2 h2 <;> simp_all <;> omega

/-- The leaf bounds of the sub-couples. -/
def tcBA (c : MiniCplCode) (B : (Fin 2 × Path) → NNReal) : (Fin 2 × Path) → NNReal := fun a => B (t1A c a)
def tcBB (B : (Fin 2 × Path) → NNReal) : (Fin 2 × Path) → NNReal := fun a => B (t1B a)
def tcBC (c : MiniCplCode) (B : (Fin 2 × Path) → NNReal) : (Fin 2 × Path) → NNReal := fun a => B (t1C c a)

theorem tc_t1_leafwise {d : ℕ} {H : LeafProfiles 2 d} {B : (Fin 2 × Path) → NNReal}
    (hH : LeafwiseControlled LGr H B) :
    LeafwiseControlled LG₁ (t1HA c H) (tcBA c B) ∧ LeafwiseControlled LG₂ (t1HB H) (tcBB B) ∧
      LeafwiseControlled LG₃ (t1HC c H) (tcBC c B) :=
  ⟨fun ℓ hℓ => hH (h.lfA ℓ) (h.lfA_input ℓ hℓ), fun ℓ hℓ => hH (h.lfB ℓ) (h.lfB_input ℓ hℓ),
    fun ℓ hℓ => hH (h.lfC ℓ) (h.lfC_input ℓ hℓ)⟩

theorem tc_t1_leafSize (B : (Fin 2 × Path) → NNReal) :
    leafSizeProduct LGr B = leafSizeProduct LG₁ (tcBA c B) * leafSizeProduct LG₂ (tcBB B) *
      leafSizeProduct LG₃ (tcBC c B) := by
  unfold leafSizeProduct
  rw [h.prod_inputLeaves_t1 (fun a => (B a : ℝ))]
  simp only [tcBA, tcBB, tcBC]
  ring

/-! ### Embeddings, multiplier, star cost -/

theorem tc_embA : PieceEmb h.ιA h.βA := ⟨h.βA_toNode, h.βA_child⟩
theorem tc_embB : PieceEmb h.ιB h.βB := ⟨h.βB_toNode, h.βB_child⟩
theorem tc_embC : PieceEmb h.ιC h.βC := ⟨h.βC_toNode, h.βC_child⟩

theorem tc_t1_hroot (S : Finset (GNode LGr.garden.tree)) :
    ∀ a ∈ S, a.1.2 = [] → a.1.2 ∈ (LGr.garden.tree a.1.1).branching := by
  intro a _ h0
  rw [h0]
  exact h.root_mem a.1.1

/-- **D3's gate-form multiplier of a type-1 couple factors at its two roots**, the sub-couples in gate form. -/
theorem tc_t1_mult {d : ℕ} (S : Finset (GNode LGr.garden.tree)) (ω : GNode LGr.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LGr.garden.tree)) (M : GBranch LGr.garden.tree → ℝ) (Fu : Finset (GBranch LGr.garden.tree))
    (Mu : GBranch LGr.garden.tree → ℝ) :
    h.MultFactors (gateM S ω F M Fu Mu)
      (fun A B => fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) A * fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) B)
      (pullMult h.ιA h.βA S ω F M Fu Mu) (pullMult h.ιB h.βB S ω F M Fu Mu) (pullMult h.ιC h.βC S ω F M Fu Mu) := by
  intro K
  have hl := h.multFactors_local (fD3' S ω F (fun _ => false) M Fu Mu) K
  simp only at hl
  have e : gateM S ω F M Fu Mu K = ∏ b, fD3' S ω F (fun _ => false) M Fu Mu b (bstar K b) :=
    starFilt_local' S (tc_t1_hroot h S) ω F (fun _ => false) M Fu Mu K
  rw [e, hl, pull_mult (tc_embA h), pull_mult (tc_embB h), pull_mult (tc_embC h)]
  rfl

/-- **The star cost of a type-1 couple splits** at its two roots and the three sub-couples. -/
theorem tc_t1_cost (S : Finset (GNode LGr.garden.tree)) (cω : GNode LGr.garden.tree → ℝ) :
    starCost S cω = costB S cω (h.rt 0) * costB S cω (h.rt 1) *
      (starCost (pullS h.ιA S) (fun z => cω (h.ιA z)) * (starCost (pullS h.ιB S) (fun z => cω (h.ιB z)) *
        starCost (pullS h.ιC S) (fun z => cω (h.ιC z)))) := by
  unfold starCost
  rw [prod_cost_branch S (tc_t1_hroot h S) cω, h.prod_t1Branch, pull_cost (tc_embA h), pull_cost (tc_embB h),
    pull_cost (tc_embC h)]

end Data

end WaveTurbulence.Flower.ProtPin

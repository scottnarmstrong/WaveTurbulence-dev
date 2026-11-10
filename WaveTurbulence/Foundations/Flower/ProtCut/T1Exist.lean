/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Ker

/-! # D2c-3 PROT-CUT: the pieces of a type-1 couple exist; branch-local multipliers factor at its roots

* `isLayering_pullback2`, `pair_layer_couple2`: a couple layering pulled back to a decoded sub-couple.
* **`T1Data.exists_of_decodes`**: a well-formed `type1 c Q₁ Q₂ Q₃` decoding a layered couple `LG` has its three
  sub-couples as layered couples with the layers of `LG` (the layer hypotheses of `kernelProt_t1Trace`).
* **`T1Data.multFactors_local`**: `K ↦ ∏_b f b (bstar K b)` satisfies `T1Data.MultFactors`, with
  `Mc A B = f ρ₀ A · f ρ₁ B` and `Mᵢ K = ∏_x f (βᵢ x) (bstar K x)`; `multFactors_local_bound`. This covers D3's
  side-couple multipliers (`CutTermData.multFactors_D3'` gives them in this form). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- A couple layering pulled back along an address map that sends branching nodes to branching nodes. -/
theorem isLayering_pullback2 (LG : LayeredGarden 2) (G' : Garden 2)
    (φ : Fin 2 × Path → Fin 2 × Path) (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (hb : ∀ x : GBranch G'.tree, (φ x.1).2 ∈ (LG.garden.tree (φ x.1).1).branching)
    (hpair : ∀ ℓ : GLeaf G'.tree, layerAt LG (φ ℓ.1) = layerAt LG (φ (G'.pair ℓ).1)) :
    IsLayering G' (fun z => layerAt LG (φ z.1)) := by
  refine ⟨fun b i => ?_, hpair⟩
  let B : GBranch LG.garden.tree := ⟨φ b.1, hb b⟩
  have h := LG.isLayering.1 B i
  have e1 : layerAt LG (φ (b.child i).1) = LG.layer (B.child i) := by
    rw [← layerAt_node]
    exact congrArg (layerAt LG) (hφ b.1 [i])
  have e2 : layerAt LG (φ b.toNode.1) = LG.layer B.toNode := layerAt_node LG B.toNode
  show layerAt LG (φ (b.child i).1) ≤ layerAt LG (φ b.toNode.1)
  rw [e1, e2]
  exact h

/-- Leaf pairs of a decoded sub-couple of a decoded couple keep their layers. -/
theorem pair_layer_couple2 (LG : LayeredGarden 2) {Q : RegCpl} (hQ : Q.Decodes LG.garden) {G' : Garden 2}
    {Q' : RegCpl} (hQ' : Q'.Decodes G') (φ : Fin 2 × Path → Fin 2 × Path)
    (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (hsub : ∀ p ∈ Q'.pairsAt (φ ((0 : Fin 2), [])) (φ ((1 : Fin 2), [])), p ∈ Q.pairsAt (0, []) (1, []))
    (ℓ : GLeaf G'.tree) : layerAt LG (φ ℓ.1) = layerAt LG (φ (G'.pair ℓ).1) := by
  have hm := hQ'.2.2.2 ℓ
  rw [mem_symmPairs] at hm
  have key : ∀ u v : Fin 2 × Path, (u, v) ∈ Q'.raw.2 → layerAt LG (φ u) = layerAt LG (φ v) := by
    intro u v huv
    refine layer_eq_of_decoded_pair hQ (p := (φ u, φ v)) (hsub _ ?_)
    rw [couple_pairsAt_map Q' φ hφ]
    exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
  rcases hm with hm | hm
  · exact key _ _ hm
  · exact (key _ _ hm).symm

/-- **The sub-couples of a type-1 couple exist**, with the layers of the couple. -/
theorem T1Data.exists_of_decodes (LG : LayeredGarden 2) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    (hd : (RegCpl.type1 c Q₁ Q₂ Q₃).Decodes LG.garden) (hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true) :
    ∃ (LG₁ LG₂ LG₃ : LayeredGarden 2) (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden),
      (∀ z, LG₁.layer z = LG.layer (h.ιA z)) ∧ (∀ z, LG₂.layer z = LG.layer (h.ιB z)) ∧
        ∀ z, LG₃.layer z = LG.layer (h.ιC z) := by
  simp only [RegCpl.wf, Bool.and_eq_true] at hwf
  obtain ⟨⟨hw₁, hw₂⟩, hw₃⟩ := hwf
  obtain ⟨G₁, hd₁, -⟩ := Reg.wf_code_exists_regular_decodes Q₁ hw₁
  obtain ⟨G₂, hd₂, -⟩ := Reg.wf_code_exists_regular_decodes Q₂ hw₂
  obtain ⟨G₃, hd₃, -⟩ := Reg.wf_code_exists_regular_decodes Q₃ hw₃
  have h : T1Data c Q₁ Q₂ Q₃ LG.garden G₁ G₂ G₃ := ⟨hd, hd₁, hd₂, hd₃⟩
  have sA : ∀ p ∈ Q₁.pairsAt (t1A c ((0 : Fin 2), [])) (t1A c ((1 : Fin 2), [])),
      p ∈ (RegCpl.type1 c Q₁ Q₂ Q₃).pairsAt (0, []) (1, []) := fun p hp => by
    simp only [RegCpl.pairsAt, List.mem_append]
    left; left; exact hp
  have sB : ∀ p ∈ Q₂.pairsAt (t1B ((0 : Fin 2), [])) (t1B ((1 : Fin 2), [])),
      p ∈ (RegCpl.type1 c Q₁ Q₂ Q₃).pairsAt (0, []) (1, []) := fun p hp => by
    simp only [RegCpl.pairsAt, List.mem_append]
    left; right; exact hp
  have sC : ∀ p ∈ Q₃.pairsAt (t1C c ((0 : Fin 2), [])) (t1C c ((1 : Fin 2), [])),
      p ∈ (RegCpl.type1 c Q₁ Q₂ Q₃).pairsAt (0, []) (1, []) := fun p hp => by
    simp only [RegCpl.pairsAt, List.mem_append]
    right; exact hp
  refine ⟨⟨G₁, fun z => layerAt LG (t1A c z.1), isLayering_pullback2 LG G₁ (t1A c) (t1A_hom c)
      (fun x => (h.βA x).2) (pair_layer_couple2 LG hd hd₁ (t1A c) (t1A_hom c) sA)⟩,
    ⟨G₂, fun z => layerAt LG (t1B z.1), isLayering_pullback2 LG G₂ t1B t1B_hom
      (fun x => (h.βB x).2) (pair_layer_couple2 LG hd hd₂ t1B t1B_hom sB)⟩,
    ⟨G₃, fun z => layerAt LG (t1C c z.1), isLayering_pullback2 LG G₃ (t1C c) (t1C_hom c)
      (fun x => (h.βC x).2) (pair_layer_couple2 LG hd hd₃ (t1C c) (t1C_hom c) sC)⟩, h,
    fun z => layerAt_node LG (h.ιA z), fun z => layerAt_node LG (h.ιB z), fun z => layerAt_node LG (h.ιC z)⟩

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
variable (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden)
include h

variable {d : ℕ}

theorem bstar_βA (K : GNode LG.garden.tree → Mom d) (x : GBranch LG₁.garden.tree) :
    bstar K (h.βA x) = bstar (K ∘ h.ιA) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show K ((h.βA x).child j) = K (h.ιA (x.child j))
    rw [h.βA_child]

theorem bstar_βB (K : GNode LG.garden.tree → Mom d) (x : GBranch LG₂.garden.tree) :
    bstar K (h.βB x) = bstar (K ∘ h.ιB) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show K ((h.βB x).child j) = K (h.ιB (x.child j))
    rw [h.βB_child]

theorem bstar_βC (K : GNode LG.garden.tree → Mom d) (x : GBranch LG₃.garden.tree) :
    bstar K (h.βC x) = bstar (K ∘ h.ιC) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show K ((h.βC x).child j) = K (h.ιC (x.child j))
    rw [h.βC_child]

/-- **A branch-local multiplier factors at the two roots of a type-1 couple.** -/
theorem multFactors_local (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) :
    h.MultFactors (fun K => ∏ b, f b (bstar K b)) (fun A B => f (h.rt 0) A * f (h.rt 1) B)
      (fun K => ∏ x, f (h.βA x) (bstar K x)) (fun K => ∏ x, f (h.βB x) (bstar K x))
      (fun K => ∏ x, f (h.βC x) (bstar K x)) := by
  intro K
  simp only
  rw [h.prod_t1Branch]
  simp only [h.bstar_βA, h.bstar_βB, h.bstar_βC]

end T1Data

end WaveTurbulence.Flower.ProtCut

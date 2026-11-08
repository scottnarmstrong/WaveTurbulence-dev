/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ABook

/-! # D3-HELPER (P7), shape (a+): D3's multiplier and star cost on the pieces

D3's gate-form multiplier `gateM S …` of the couple is branch-local (`starFilt_local'`) except for stars at leaf roots:
when `Xm = nil` and `Qlp = triv` (well formed) the root of tree `1` is a leaf, and its star reads the decoration only
at that leaf, a node of the rest couple. So:

* `tc2aSb S` (stars away from leaf roots) is branch-local and splits over the glue and the closing pair
  (`Root2Data.multFactors_local`, `pull_mult`);
* `tc2aSl S` (stars at leaf roots) is pulled back to the rest couple (`tc2aSlB`); the rest couple carries the star set
  `tc2aSB = tc2aSlB ∪ pullS ι₂ (tc2aSb S)` in gate form.

`tc2a_mult`: the hypotheses `hMg`, `hMZ` of `Root2Data.kernelProt_root2` with gate-form pieces; `tc2a_cost`: the star
cost splits; `tc2a_presB`: the rest couple's stars are presented. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The stars away from leaf roots. -/
def tc2aSb {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) : Finset (GNode G.tree) :=
  S.filter fun a => a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching

/-- The stars at leaf roots. -/
def tc2aSl {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) : Finset (GNode G.tree) :=
  S.filter fun a => ¬ (a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching)

theorem tc2a_Sb_sub {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) : tc2aSb S ⊆ S := Finset.filter_subset _ _

theorem tc2a_Sl_sub {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) : tc2aSl S ⊆ S := Finset.filter_subset _ _

theorem tc2a_Sb_root {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) :
    ∀ a ∈ tc2aSb S, a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching :=
  fun a ha => (Finset.mem_filter.mp ha).2

theorem tc2a_gateM_split {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree))
    (ω : GNode G.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (K : GNode G.tree → Mom d) :
    gateM S ω F M Fu Mu K = Flower.IncTop.starWeight (tc2aSl S) ω K * gateM (tc2aSb S) ω F M Fu Mu K := by
  unfold gateM Flower.IncTop.starWeight tc2aSl tc2aSb
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun a => a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching)]
  ring

theorem tc2a_cost_split {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (cω : GNode G.tree → ℝ) :
    starCost S cω = starCost (tc2aSl S) cω * starCost (tc2aSb S) cω := by
  unfold starCost tc2aSl tc2aSb
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun a => a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching)]
  ring

section Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D

theorem tc2a_ι₂_inj : Function.Injective D.gd.ι₂ := by
  intro y y' h
  apply Subtype.ext
  have := congrArg (fun z : GNode LG.garden.tree => GlueData.unbot (cpair m Qr Qg inner).lonePath z.1) h
  simpa [GlueData.ι₂_val, GlueData.unbot_botAddr] using this

/-- The root of tree `0` (the chain root) is a branching node. -/
theorem tc2a_root0 : ([] : TTree.Path) ∈ (LG.garden.tree 0).branching := by
  rw [D.gd.tree0]
  simp only [RegChain.plug]
  exact (mem_node3_nil _).2.2

/-- Leaf roots of the couple lie in the rest couple. -/
theorem tc2a_Sl_range (S : Finset (GNode LG.garden.tree)) (a : GNode LG.garden.tree) (ha : a ∈ tc2aSl S) :
    a ∈ Set.range D.gd.ι₂ := by
  have h2 := (Finset.mem_filter.mp ha).2
  push_neg at h2
  obtain ⟨h0, hb⟩ := h2
  have h1 : a.1.1 ≠ 0 := by
    intro h
    apply hb
    rw [h0, h]
    exact tc2a_root0 D
  have hbot : botAddr (cpair m Qr Qg inner).lonePath a.1 = a.1 := by
    unfold botAddr; rw [if_neg h1]
  have hm : a.1.2 ∈ (LGB.garden.tree a.1.1).nodes := by
    have h3 := a.2
    have := (D.gd.bot_iff a.1).1
    rw [hbot] at this
    exact this.mp h3
  exact ⟨⟨a.1, hm⟩, Subtype.ext hbot⟩

/-- The leaf-root stars, pulled back to the rest couple. -/
def tc2aSlB (S : Finset (GNode LG.garden.tree)) : Finset (GNode LGB.garden.tree) :=
  (tc2aSl S).preimage D.gd.ι₂ (fun _ _ _ _ h => tc2a_ι₂_inj D h)

/-- The star set of the rest couple. -/
def tc2aSB (S : Finset (GNode LG.garden.tree)) : Finset (GNode LGB.garden.tree) :=
  tc2aSlB D S ∪ pullS D.gd.ι₂ (tc2aSb S)

theorem tc2a_mem_SlB (S : Finset (GNode LG.garden.tree)) (z : GNode LGB.garden.tree) :
    z ∈ tc2aSlB D S ↔ D.gd.ι₂ z ∈ tc2aSl S := by
  unfold tc2aSlB; exact Finset.mem_preimage

theorem tc2a_SB_disj (S : Finset (GNode LG.garden.tree)) : Disjoint (tc2aSlB D S) (pullS D.gd.ι₂ (tc2aSb S)) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [tc2a_mem_SlB] at hz
  have h1 := (Finset.mem_filter.mp hz').2.1
  have hl := (Finset.mem_filter.mp hz).2
  have hb := (Finset.mem_filter.mp h1).2
  exact hl hb

theorem tc2a_starMomenta_leaf {d : ℕ} (K : GNode LG.garden.tree → Mom d) (z : GNode LGB.garden.tree)
    (hz : (D.gd.ι₂ z).1.2 ∉ (LG.garden.tree (D.gd.ι₂ z).1.1).branching) :
    Flower.IncTop.starMomenta (K ∘ D.gd.ι₂) z = Flower.IncTop.starMomenta K (D.gd.ι₂ z) := by
  have hz' : z.1.2 ∉ (LGB.garden.tree z.1.1).branching := fun h => hz ((D.gd.bot_iff z.1).2.2.mpr h)
  unfold Flower.IncTop.starMomenta Flower.IncTop.starNode
  simp only [dif_neg hz', dif_neg hz, Function.comp_apply]

theorem tc2a_starWeight_Sl {d : ℕ} (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (K : GNode LG.garden.tree → Mom d) :
    Flower.IncTop.starWeight (tc2aSl S) ω K =
      Flower.IncTop.starWeight (tc2aSlB D S) (fun z => ω (D.gd.ι₂ z)) (K ∘ D.gd.ι₂) := by
  unfold Flower.IncTop.starWeight tc2aSlB
  have e : ∀ z ∈ (tc2aSl S).preimage D.gd.ι₂ (fun _ _ _ _ h => tc2a_ι₂_inj D h),
      ω (D.gd.ι₂ z) (Flower.IncTop.starMomenta (K ∘ D.gd.ι₂) z) =
        ω (D.gd.ι₂ z) (Flower.IncTop.starMomenta K (D.gd.ι₂ z)) := by
    intro z hz
    have hb := (Finset.mem_filter.mp (Finset.mem_preimage.mp hz)).2
    push_neg at hb
    rw [tc2a_starMomenta_leaf D K z hb.2]
  rw [Finset.prod_congr rfl e]
  exact (Finset.prod_preimage D.gd.ι₂ (tc2aSl S) (fun _ _ _ _ h => tc2a_ι₂_inj D h)
    (fun a => ω a (Flower.IncTop.starMomenta K a))
    (fun a ha hr => absurd (tc2a_Sl_range D S a ha) hr)).symm

theorem tc2a_cost_Sl (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) :
    starCost (tc2aSl S) cω = starCost (tc2aSlB D S) (fun z => cω (D.gd.ι₂ z)) := by
  unfold starCost tc2aSlB
  exact (Finset.prod_preimage D.gd.ι₂ (tc2aSl S) (fun _ _ _ _ h => tc2a_ι₂_inj D h)
    (fun a => max (cω a) 0) (fun a ha hr => absurd (tc2a_Sl_range D S a ha) hr)).symm

/-- The rest couple's stars are presented. -/
theorem tc2a_presB {d J : ℕ} {S : Finset (GNode LG.garden.tree)} {ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ}
    {cω : GNode LG.garden.tree → ℝ} (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a)) :
    ∀ z ∈ tc2aSB D S, Flower.IncTop.StarPresented J (ω (D.gd.ι₂ z)) (cω (D.gd.ι₂ z)) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rw [tc2a_mem_SlB] at hz
    exact hpres _ (tc2a_Sl_sub S hz)
  · exact hpres _ (tc2a_Sb_sub S (Finset.mem_filter.mp hz).2.1)

omit D in
theorem tc2a_presSb {d J : ℕ} {S : Finset (GNode LG.garden.tree)} {ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ}
    {cω : GNode LG.garden.tree → ℝ} (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a)) :
    ∀ a ∈ tc2aSb S, Flower.IncTop.StarPresented J (ω a) (cω a) :=
  fun a ha => hpres a (tc2a_Sb_sub S ha)

include P

/-- **D3's multiplier on the pieces**: the hypotheses `hMg`, `hMZ` of `Root2Data.kernelProt_root2`. -/
theorem tc2a_mult {d : ℕ} (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) :
    (∀ K, gateM S ω F M Fu Mu K =
        (fun K' => ∏ x, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.gd.ofSum (.inl x)) (bstar K' x))
          (K ∘ D.gd.ι₁) *
        gateM (tc2aSB D S) (fun z => ω (D.gd.ι₂ z)) (pullF (fun y => D.gd.ofSum (.inr y)) F)
          (fun y => M (D.gd.ofSum (.inr y))) (pullF (fun y => D.gd.ofSum (.inr y)) Fu)
          (fun y => Mu (D.gd.ofSum (.inr y))) (K ∘ D.gd.ι₂)) ∧
    P.MultFactors (fun K' => ∏ x, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.gd.ofSum (.inl x)) (bstar K' x))
      (fun A B => fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.aR P) A *
        fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.bR P) B)
      (pullMult (fun z => D.gd.ι₁ (P.hp.ιi z)) (fun x => D.gd.ofSum (.inl (P.hp.βi x))) (tc2aSb S) ω F M Fu Mu)
      (pullMult (fun z => D.gd.ι₁ (P.hp.ιr z)) (fun y => D.gd.ofSum (.inl (P.hp.βr y))) (tc2aSb S) ω F M Fu Mu)
      (pullMult (fun z => D.gd.ι₁ (P.hp.ιg z)) (fun y => D.gd.ofSum (.inl (P.hp.βg y))) (tc2aSb S) ω F M Fu Mu) := by
  have h := D.multFactors_local P (fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu)
  have eI : (fun K => ∏ x, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.gd.ofSum (.inl (P.hp.βi x))) (bstar K x)) =
      pullMult (fun z => D.gd.ι₁ (P.hp.ιi z)) (fun x => D.gd.ofSum (.inl (P.hp.βi x))) (tc2aSb S) ω F M Fu Mu :=
    funext fun K => pull_mult (tc2a_embI D P) (tc2aSb S) ω F M Fu Mu K
  have eR : (fun K => ∏ y, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.gd.ofSum (.inl (P.hp.βr y))) (bstar K y)) =
      pullMult (fun z => D.gd.ι₁ (P.hp.ιr z)) (fun y => D.gd.ofSum (.inl (P.hp.βr y))) (tc2aSb S) ω F M Fu Mu :=
    funext fun K => pull_mult (tc2a_embR D P) (tc2aSb S) ω F M Fu Mu K
  have eG : (fun K => ∏ y, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.gd.ofSum (.inl (P.hp.βg y))) (bstar K y)) =
      pullMult (fun z => D.gd.ι₁ (P.hp.ιg z)) (fun y => D.gd.ofSum (.inl (P.hp.βg y))) (tc2aSb S) ω F M Fu Mu :=
    funext fun K => pull_mult (tc2a_embG D P) (tc2aSb S) ω F M Fu Mu K
  rw [eI, eR, eG] at h
  refine ⟨fun K => ?_, h.2⟩
  have hB : gateM (tc2aSB D S) (fun z => ω (D.gd.ι₂ z)) (pullF (fun y => D.gd.ofSum (.inr y)) F)
      (fun y => M (D.gd.ofSum (.inr y))) (pullF (fun y => D.gd.ofSum (.inr y)) Fu)
      (fun y => Mu (D.gd.ofSum (.inr y))) (K ∘ D.gd.ι₂) =
      Flower.IncTop.starWeight (tc2aSlB D S) (fun z => ω (D.gd.ι₂ z)) (K ∘ D.gd.ι₂) *
        ∏ y, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.gd.ofSum (.inr y)) (bstar (K ∘ D.gd.ι₂) y) := by
    rw [pull_mult (tc2a_embB D) (tc2aSb S) ω F M Fu Mu (K ∘ D.gd.ι₂)]
    unfold gateM tc2aSB Flower.IncTop.starWeight
    rw [Finset.prod_union (tc2a_SB_disj D S)]
    ring
  rw [hB, tc2a_gateM_split S ω F M Fu Mu K, tc2a_starWeight_Sl D S ω K]
  have e1 : gateM (tc2aSb S) ω F M Fu Mu K = ∏ b, fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu b (bstar K b) :=
    starFilt_local' (tc2aSb S) (tc2a_Sb_root S) ω F (fun _ => false) M Fu Mu K
  rw [e1, h.1 K]
  ring

/-- The cut factor is bounded by the costs of the two linked nodes. -/
theorem tc2a_Mc_le {d : ℕ} (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) {J : ℕ} (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (A B : Fin 4 → Mom d) :
    ‖fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.aR P) A * fD3' (tc2aSb S) ω F (fun _ => false) M Fu Mu (D.bR P) B‖ ≤
      costB (tc2aSb S) cω (D.aR P) * costB (tc2aSb S) cω (D.bR P) := by
  rw [norm_mul]
  exact mul_le_mul (norm_fD3'_le _ ω cω (tc2a_presSb hpres) F M Fu Mu _ _)
    (norm_fD3'_le _ ω cω (tc2a_presSb hpres) F M Fu Mu _ _) (norm_nonneg _) (costB_nonneg _ _ _)

/-- **The star cost splits** at the two linked nodes and the four pieces. -/
theorem tc2a_cost (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) :
    starCost S cω = costB (tc2aSb S) cω (D.aR P) * costB (tc2aSb S) cω (D.bR P) *
      (starCost (tc2aSB D S) (fun z => cω (D.gd.ι₂ z)) *
        (starCost (pullS (fun z => D.gd.ι₁ (P.hp.ιi z)) (tc2aSb S)) (fun z => cω (D.gd.ι₁ (P.hp.ιi z))) *
          (starCost (pullS (fun z => D.gd.ι₁ (P.hp.ιr z)) (tc2aSb S)) (fun z => cω (D.gd.ι₁ (P.hp.ιr z))) *
            starCost (pullS (fun z => D.gd.ι₁ (P.hp.ιg z)) (tc2aSb S)) (fun z => cω (D.gd.ι₁ (P.hp.ιg z)))))) := by
  rw [tc2a_cost_split S cω, tc2a_cost_Sl D S cω]
  have hSb : starCost (tc2aSb S) cω = ∏ b : GBranch LG.garden.tree, costB (tc2aSb S) cω b :=
    prod_cost_branch (tc2aSb S) (tc2a_Sb_root S) cω
  rw [hSb, tc2a_prod_branch D P, pull_cost (tc2a_embB D), pull_cost (tc2a_embI D P), pull_cost (tc2a_embR D P),
    pull_cost (tc2a_embG D P)]
  have hU : starCost (tc2aSB D S) (fun z => cω (D.gd.ι₂ z)) =
      starCost (tc2aSlB D S) (fun z => cω (D.gd.ι₂ z)) *
        ∏ a ∈ pullS D.gd.ι₂ (tc2aSb S), max (cω (D.gd.ι₂ a)) 0 := by
    unfold starCost tc2aSB
    rw [Finset.prod_union (tc2a_SB_disj D S)]
  rw [hU]
  unfold starCost
  ring

end Data

end WaveTurbulence.Flower.ProtPin

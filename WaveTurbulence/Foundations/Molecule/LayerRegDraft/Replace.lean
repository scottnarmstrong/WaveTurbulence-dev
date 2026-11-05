/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Part2

/-!
# TARGET Prop `layerreg1` (2): replacing a coherent regular couple

TARGET L905–L907: "if we fix `(q, q')` and the structure and layering of the rest of the garden, but
replace the regular couple `𝒬` by any other regular couple with layering satisfying all the above
assumptions, then the resulting garden also belongs to `𝒢_{p+1}`. [...] all the above results hold if
the garden `𝒢` is replaced by a couple, and `𝒢_{p+1}` is replaced by `𝒞_{p+1}`."

* `OutAgree LG LG' a b`: the two layered gardens have the same nodes, leaves and layers outside the
  subtrees at `a`, `b`, and the same partners for the leaves outside them ("the structure and layering of
  the rest of the garden" are fixed). The parent layers `(q, q')` of `a`, `b` then agree (`parAt_eq`).
* **`layerreg1_replace`**: two plain layered gardens agreeing off `(a, b)`, each with an embedded regular
  couple at `(a, b)` carrying the layering of part (1) (`LayerPattern`), satisfy the canonicity criterion
  together (via the characterization `layerreg1_part2`).
* **`layerreg1_replace_canonG`**, **`layerreg1_replace_canonC`**: TARGET's statement. If `LG ∈ 𝒢_{p+1}`
  (resp. `𝒞_{p+1}`) contains a coherent embedded regular couple `𝒬` at `(a, b)`, and `LG'` agrees with `LG`
  off `(a, b)` and carries at `(a, b)` a regular couple `𝒬'` with `LayerPattern`, then `LG' ∈ 𝒢_{p+1}`
  (resp. `𝒞_{p+1}`, given the same signature). Plainness and irreducibility of `LG'` are derived.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **Two layered gardens agree off the subtrees at `a, b`.** -/
structure OutAgree (LG LG' : LayeredGarden w) (a b : Fin w × Path) : Prop where
  node : ∀ z : Fin w × Path, ¬ InRegion a b z →
    (z.2 ∈ (LG.garden.tree z.1).nodes ↔ z.2 ∈ (LG'.garden.tree z.1).nodes)
  leaf : ∀ z : Fin w × Path, ¬ InRegion a b z →
    (z.2 ∈ (LG.garden.tree z.1).leaves ↔ z.2 ∈ (LG'.garden.tree z.1).leaves)
  layer : ∀ z : Fin w × Path, ¬ InRegion a b z → layerAt LG z = layerAt LG' z
  pair : ∀ (ℓ : GLeaf LG.garden.tree) (ℓ' : GLeaf LG'.garden.tree), ¬ InRegion a b ℓ.1 → ℓ.1 = ℓ'.1 →
    (LG.garden.pair ℓ).1 = (LG'.garden.pair ℓ').1

/-! ### Pairs of a placed couple join independent leaves -/

mutual
theorem cpl_pair_indep : ∀ (Q : RegCpl) (a b : Fin w × Path), Indep a b →
    ∀ q ∈ Q.pairsAt a b, Indep q.1 q.2
  | .triv, a, b, h, q, hq => by
    simp only [RegCpl.pairsAt, List.mem_singleton] at hq
    subst hq; exact h
  | .type1 c Q₁ Q₂ Q₃, a, b, h, q, hq => by
    simp only [RegCpl.pairsAt, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact cpl_pair_indep Q₁ _ _ (h.ext _ _) q hq
    · exact cpl_pair_indep Q₂ _ _ (h.symm.ext _ _) q hq
    · exact cpl_pair_indep Q₃ _ _ (h.ext _ _) q hq
  | .type2 Xp Xm Qlp, a, b, h, q, hq => by
    simp only [RegCpl.pairsAt, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact chain_pair_indep Xp 1 a q hq
    · exact chain_pair_indep Xm (-1) b q hq
    · exact cpl_pair_indep Qlp _ _ (h.ext _ _) q hq

theorem chain_pair_indep : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path),
    ∀ q ∈ X.pairsAt ζ a, Indep q.1 q.2
  | .nil, _, _, q, hq => by simp [RegChain.pairsAt] at hq
  | .pair m Qr Qg inner rest, ζ, a, q, hq => by
    simp only [RegChain.pairsAt, List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · split_ifs at hq
      · exact cpl_pair_indep Qr _ _ (indep_red m inner.lonePath a) q hq
      · exact cpl_pair_indep Qr _ _ (indep_red m inner.lonePath a).symm q hq
    · split_ifs at hq
      · exact cpl_pair_indep Qg _ _ (indep_green m inner.lonePath a) q hq
      · exact cpl_pair_indep Qg _ _ (indep_green m inner.lonePath a).symm q hq
    · exact chain_pair_indep inner _ _ q hq
    · exact chain_pair_indep rest _ _ q hq
end

/-! ### Transfer along an agreement -/

variable {LG LG' : LayeredGarden w} {a b : Fin w × Path} {p : ℕ}

theorem OutAgree.symm (h : OutAgree LG LG' a b) : OutAgree LG' LG a b :=
  ⟨fun z hz => (h.node z hz).symm, fun z hz => (h.leaf z hz).symm, fun z hz => (h.layer z hz).symm,
    fun ℓ ℓ' hr e => (h.pair ℓ' ℓ (by rw [← e]; exact hr) e.symm).symm⟩

/-- Parent layers agree at nodes whose parent lies outside the region. -/
theorem OutAgree.parAt_eq (hA : OutAgree LG LG' a b) {z : Fin w × Path}
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (hz' : z.2 ∈ (LG'.garden.tree z.1).nodes)
    (hpar : ∀ (x : Fin w × Path) (k : Fin 3), z = addrExt x [k] → ¬ InRegion a b x) :
    parAt LG p z = parAt LG' p z := by
  rcases z with ⟨j, s⟩
  rcases List.eq_nil_or_concat s with rfl | ⟨q, k, rfl⟩
  · rw [parAt_root, parAt_root]
  · have e : ((j, q.concat k) : Fin w × Path) = addrExt (j, q) [k] := by
      simp [addrExt, List.concat_eq_append]
    have h1 : (addrExt (j, q) [k]).2 ∈ (LG.garden.tree (addrExt (j, q) [k]).1).nodes := by
      rw [← e]; exact hz
    have h2 : (addrExt (j, q) [k]).2 ∈ (LG'.garden.tree (addrExt (j, q) [k]).1).nodes := by
      rw [← e]; exact hz'
    rw [e, parAt_child LG p k h1, parAt_child LG' p k h2]
    exact hA.layer _ (hpar _ _ e)

theorem OutAgree.parAt_eq_a (hA : OutAgree LG LG' a b) (hab : Indep a b)
    (ha : a.2 ∈ (LG.garden.tree a.1).nodes) (ha' : a.2 ∈ (LG'.garden.tree a.1).nodes) :
    parAt LG p a = parAt LG' p a :=
  hA.parAt_eq ha ha' (fun _ _ e => root_parent_out hab e)

theorem OutAgree.parAt_eq_b (hA : OutAgree LG LG' a b) (hab : Indep a b)
    (hb : b.2 ∈ (LG.garden.tree b.1).nodes) (hb' : b.2 ∈ (LG'.garden.tree b.1).nodes) :
    parAt LG p b = parAt LG' p b :=
  hA.parAt_eq hb hb' (fun _ _ e hr => root_parent_out hab.symm e hr.symm)

theorem OutAgree.parAt_eq_out (hA : OutAgree LG LG' a b) {z : Fin w × Path} (hr : ¬ InRegion a b z)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (hz' : z.2 ∈ (LG'.garden.tree z.1).nodes) :
    parAt LG p z = parAt LG' p z :=
  hA.parAt_eq hz hz' (fun _ _ e hx => hr (region_of_child e hx))

/-- Complete pairing of a region-saturated set of leaves is the same in both gardens. -/
theorem cp_transfer (hA : OutAgree LG LG' a b) (hplain : LG.garden.IsPlain)
    (hplain' : LG'.garden.IsPlain) {Q Q' : RegCpl} (hE : Embeds LG.garden Q a b)
    (hE' : Embeds LG'.garden Q' a b) (σ : Fin w × Path → Prop) (hsa : ∀ z, Under a z → (σ z ↔ σ a))
    (hsb : ∀ z, Under b z → (σ z ↔ σ b)) (S : Finset (GLeaf LG.garden.tree))
    (S' : Finset (GLeaf LG'.garden.tree)) (hS : ∀ ℓ, ℓ ∈ S ↔ σ ℓ.1) (hS' : ∀ ℓ, ℓ ∈ S' ↔ σ ℓ.1) :
    LG.garden.CompletelyPaired S ↔ LG'.garden.CompletelyPaired S' := by
  rw [cp_iff hplain hE σ hsa hsb S hS, cp_iff hplain' hE' σ hsa hsb S' hS']
  refine and_congr ⟨fun h ℓ' hr hσ => ?_, fun h ℓ hr hσ => ?_⟩ Iff.rfl
  · have hl : ℓ'.1.2 ∈ (LG.garden.tree ℓ'.1.1).leaves := (hA.leaf _ hr).2 ℓ'.2
    rw [← hA.pair ⟨ℓ'.1, hl⟩ ℓ' hr rfl]
    exact h ⟨ℓ'.1, hl⟩ hr hσ
  · have hl : ℓ.1.2 ∈ (LG'.garden.tree ℓ.1.1).leaves := (hA.leaf _ hr).1 ℓ.2
    rw [hA.pair ℓ ⟨ℓ.1, hl⟩ hr rfl]
    exact h ⟨ℓ.1, hl⟩ hr hσ

theorem sat_out {c x y z : Fin w × Path} (hx : ¬ Under c x) (hy : ¬ Under c y) (hcz : Under c z) :
    (Under x z ∨ Under y z) ↔ (Under x c ∨ Under y c) :=
  ⟨fun h => h.imp (under_of_out hx hcz) (under_of_out hy hcz),
    fun h => h.imp (fun h' => under_trans h' hcz) (fun h' => under_trans h' hcz)⟩

theorem sat_self {c y z : Fin w × Path} (hcz : Under c z) :
    (Under c z ∨ Under y z) ↔ (Under c c ∨ Under y c) :=
  ⟨fun _ => Or.inl (under_refl _), fun _ => Or.inl hcz⟩

theorem sat_root {c d y z : Fin w × Path} (hcd : Indep c d) (hyd : ¬ Under d y) (hdz : Under d z) :
    (Under c z ∨ Under y z) ↔ (Under c d ∨ Under y d) := by
  constructor
  · rintro (h | h)
    · exact absurd hdz (fun h' => hcd.not_both h h')
    · exact Or.inr (under_of_out hyd hdz h)
  · rintro (h | h)
    · exact absurd h hcd.1
    · exact Or.inr (under_trans h hdz)

theorem critOut_transfer (hA : OutAgree LG LG' a b) (hplain : LG.garden.IsPlain)
    (hplain' : LG'.garden.IsPlain) {Q Q' : RegCpl} (hE : Embeds LG.garden Q a b)
    (hE' : Embeds LG'.garden Q' a b) (h : CritOut LG p a b) : CritOut LG' p a b := by
  intro x y hx hy hinc hcp
  have nx := (hA.node _ hx).2 x.2
  have ny := (hA.node _ hy).2 y.2
  have hxo := not_or.1 hx
  have hyo := not_or.1 hy
  have hcp' : LG.garden.CompletelyPaired (GNode.leavesBelow (⟨x.1, nx⟩ : GNode LG.garden.tree) ∪
      GNode.leavesBelow (⟨y.1, ny⟩ : GNode LG.garden.tree)) :=
    (cp_transfer hA hplain hplain' hE hE' (fun z => Under x.1 z ∨ Under y.1 z)
      (fun _ hz => sat_out hxo.1 hyo.1 hz) (fun _ hz => sat_out hxo.2 hyo.2 hz) _ _
      (mem_leavesBelow_union (⟨x.1, nx⟩ : GNode LG.garden.tree) ⟨y.1, ny⟩)
      (mem_leavesBelow_union x y)).2 hcp
  have := h ⟨x.1, nx⟩ ⟨y.1, ny⟩ hx hy hinc hcp'
  rw [← parAt_of_mem LG p nx, ← parAt_of_mem LG p ny, ← layerAt_of_mem LG nx,
    ← layerAt_of_mem LG ny, hA.parAt_eq_out hx nx x.2, hA.parAt_eq_out hy ny y.2, hA.layer _ hx,
    hA.layer _ hy] at this
  rwa [← parAt_node, ← parAt_node, ← layerAt_node, ← layerAt_node]

theorem critAttach_transfer (hA : OutAgree LG LG' a b) (hplain : LG.garden.IsPlain)
    (hplain' : LG'.garden.IsPlain) {Q Q' : RegCpl} (hE : Embeds LG.garden Q a b)
    (hE' : Embeds LG'.garden Q' a b) {r : ℕ} (h : CritAttach LG p a b r) : CritAttach LG' p a b r := by
  intro x y hx hy hinc hcp
  have hab := hE.indep
  have nx : x.1.2 ∈ (LG.garden.tree x.1.1).nodes := by
    rcases hx with e | e <;> rw [e]
    exacts [hE.nodeA, hE.nodeB]
  have ny := (hA.node _ hy).2 y.2
  have hyo := not_or.1 hy
  have hsa : ∀ z, Under a z → ((Under x.1 z ∨ Under y.1 z) ↔ (Under x.1 a ∨ Under y.1 a)) := by
    intro z hz
    rcases hx with e | e <;> rw [e]
    · exact sat_self hz
    · exact sat_root hab.symm hyo.1 hz
  have hsb : ∀ z, Under b z → ((Under x.1 z ∨ Under y.1 z) ↔ (Under x.1 b ∨ Under y.1 b)) := by
    intro z hz
    rcases hx with e | e <;> rw [e]
    · exact sat_root hab hyo.2 hz
    · exact sat_self hz
  have hcp' : LG.garden.CompletelyPaired (GNode.leavesBelow (⟨x.1, nx⟩ : GNode LG.garden.tree) ∪
      GNode.leavesBelow (⟨y.1, ny⟩ : GNode LG.garden.tree)) :=
    (cp_transfer hA hplain hplain' hE hE' (fun z => Under x.1 z ∨ Under y.1 z) hsa hsb _ _
      (mem_leavesBelow_union (⟨x.1, nx⟩ : GNode LG.garden.tree) ⟨y.1, ny⟩)
      (mem_leavesBelow_union x y)).2 hcp
  have := h ⟨x.1, nx⟩ ⟨y.1, ny⟩ hx hy hinc hcp'
  have hpx : parAt LG p x.1 = parAt LG' p x.1 := by
    rcases hx with e | e <;> rw [e]
    · exact hA.parAt_eq_a hab hE.nodeA hE'.nodeA
    · exact hA.parAt_eq_b hab hE.nodeB hE'.nodeB
  rw [← parAt_of_mem LG p nx, ← parAt_of_mem LG p ny, ← layerAt_of_mem LG ny, hpx,
    hA.parAt_eq_out hy ny y.2, hA.layer _ hy] at this
  rwa [← parAt_node, ← parAt_node, ← layerAt_node]

theorem crit_i_transfer (hA : OutAgree LG LG' a b) (hab : Indep a b)
    (ha : a.2 ∈ (LG.garden.tree a.1).nodes) (ha' : a.2 ∈ (LG'.garden.tree a.1).nodes)
    (hb : b.2 ∈ (LG.garden.tree b.1).nodes) (hb' : b.2 ∈ (LG'.garden.tree b.1).nodes)
    (hp : ∀ x, LG.layer x ≤ p) (hua : layerAt LG' a ≤ parAt LG' p a)
    (hub : layerAt LG' b ≤ parAt LG' p b) : ∀ x, LG'.layer x ≤ p := by
  intro x
  rw [← layerAt_node]
  by_cases hr : InRegion a b x.1
  · rcases hr with h | h
    · calc layerAt LG' x.1 ≤ layerAt LG' a := layerAt_le_of_under LG' ha' x.2 h
        _ ≤ parAt LG' p a := hua
        _ = parAt LG p a := (hA.parAt_eq_a hab ha ha').symm
        _ ≤ p := parAt_le LG p hp a
    · calc layerAt LG' x.1 ≤ layerAt LG' b := layerAt_le_of_under LG' hb' x.2 h
        _ ≤ parAt LG' p b := hub
        _ = parAt LG p b := (hA.parAt_eq_b hab hb hb').symm
        _ ≤ p := parAt_le LG p hp b
  · rw [← hA.layer _ hr]; exact layerAt_le LG p hp _

/-! ### The replacement -/

/-- **TARGET Prop `layerreg1` (2), criterion form.** Two plain layered gardens that agree off the
subtrees at `a`, `b`, and carry there embedded regular couples with the layering of part (1), satisfy the
canonicity criterion at depth `p + 1` together. -/
theorem layerreg1_replace (hA : OutAgree LG LG' a b) (hplain : LG.garden.IsPlain)
    (hplain' : LG'.garden.IsPlain) {Q Q' : RegCpl} (hE : Embeds LG.garden Q a b)
    (hE' : Embeds LG'.garden Q' a b) (hP : LayerPattern LG p Q a b)
    (hP' : LayerPattern LG' p Q' a b) : LG.CanonCriterion p ↔ LG'.CanonCriterion p := by
  have hab := hE.indep
  have ea : parAt LG p a = parAt LG' p a := hA.parAt_eq_a hab hE.nodeA hE'.nodeA
  have eb : parAt LG p b = parAt LG' p b := hA.parAt_eq_b hab hE.nodeB hE'.nodeB
  have pf := patternFacts hE hP
  have pf' := patternFacts hE' hP'
  rw [layerreg1_part2 hplain hE hP, layerreg1_part2 hplain' hE' hP', ← ea, ← eb]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨crit_i_transfer hA hab hE.nodeA hE'.nodeA hE.nodeB hE'.nodeB h1 pf'.upper.1 pf'.upper.2,
      critOut_transfer hA hplain hplain' hE hE' h2, critAttach_transfer hA hplain hplain' hE hE' h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨crit_i_transfer hA.symm hab hE'.nodeA hE.nodeA hE'.nodeB hE.nodeB h1 pf.upper.1
      pf.upper.2, critOut_transfer hA.symm hplain' hplain hE' hE h2,
      critAttach_transfer hA.symm hplain' hplain hE' hE h3⟩

/-- The replaced garden is plain. -/
theorem plain_transfer (hA : OutAgree LG LG' a b) (hplain : LG.garden.IsPlain) {Q' : RegCpl}
    (hE' : Embeds LG'.garden Q' a b) : LG'.garden.IsPlain := by
  intro ℓ'
  have hne : LG'.garden.pair ℓ' ≠ ℓ' := by
    intro h
    by_cases hr : InRegion a b ℓ'.1
    · obtain ⟨q, hq, e⟩ := hE'.partner ℓ' hr
      have hi := cpl_pair_indep Q' a b hE'.indep q hq
      rw [h] at e
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hi.1 (by rw [← e1, ← e2]; exact under_refl _)
      · exact hi.1 (by rw [← e1, ← e2]; exact under_refl _)
    · have hl := (hA.leaf _ hr).2 ℓ'.2
      have e := hA.pair ⟨ℓ'.1, hl⟩ ℓ' hr rfl
      rw [h] at e
      exact ((LG.garden.pair_eq_iff _).1 (Subtype.ext e)) (hplain _)
  by_contra hm
  exact hne ((LG'.garden.pair_eq_iff ℓ').2 hm)

/-- The replaced garden is irreducible if the original one is. -/
theorem irreducible_transfer (hA : OutAgree LG LG' a b) (hplain : LG.garden.IsPlain)
    (hplain' : LG'.garden.IsPlain) {Q Q' : RegCpl} (hE : Embeds LG.garden Q a b)
    (hE' : Embeds LG'.garden Q' a b) (h : LG.garden.Irreducible) : LG'.garden.Irreducible := by
  intro A hA1 hA2 hcp
  refine h A hA1 hA2 ((cp_transfer hA hplain hplain' hE hE' (fun z => z.1 ∈ A)
    (fun z hz => by rw [hz.1]) (fun z hz => by rw [hz.1]) _ _ (fun ℓ => ?_) (fun ℓ => ?_)).2 hcp)
  · simp [Garden.leavesOf]
  · simp [Garden.leavesOf]

/-- **TARGET Prop `layerreg1` (2), gardens.** If `LG ∈ 𝒢_{p+1}` contains a coherent embedded regular
couple `𝒬` with roots `a`, `b`, and `LG'` agrees with `LG` off the subtrees at `a`, `b` and contains there
a regular couple `𝒬'` with the layering of part (1) (for the same `(q, q')`), then `LG' ∈ 𝒢_{p+1}`. -/
theorem layerreg1_replace_canonG {Q Q' : RegCpl} (hcan : IsCanonG (p + 1) LG) (hwf : Q.wf = true)
    (hE : Embeds LG.garden Q a b) (hcoh : CohOn LG (Q.linksAt a b)) (hA : OutAgree LG LG' a b)
    (hE' : Embeds LG'.garden Q' a b) (hP' : LayerPattern LG' p Q' a b) : IsCanonG (p + 1) LG' := by
  obtain ⟨hw, hplain, hirr, hcrit⟩ := hcan
  have hplain' := plain_transfer hA hplain hE'
  have hP := layerPattern_of_canon hcrit hplain hwf hE hcoh
  exact ⟨hw, hplain', irreducible_transfer hA hplain hplain' hE hE' hirr,
    (layerreg1_replace hA hplain hplain' hE hE' hP hP').1 hcrit⟩

/-- **TARGET Prop `layerreg1` (2), couples (`𝒞_{p+1}`).** -/
theorem layerreg1_replace_canonC {LG LG' : LayeredGarden 2} {a b : Fin 2 × Path} {Q Q' : RegCpl}
    (hcan : IsCanonC (p + 1) LG) (hwf : Q.wf = true) (hE : Embeds LG.garden Q a b)
    (hcoh : CohOn LG (Q.linksAt a b)) (hA : OutAgree LG LG' a b)
    (hsig : LG'.garden.sig = LG.garden.sig) (hE' : Embeds LG'.garden Q' a b)
    (hP' : LayerPattern LG' p Q' a b) : IsCanonC (p + 1) LG' := by
  obtain ⟨⟨hplain, hs⟩, hcrit⟩ := hcan
  have hplain' := plain_transfer hA hplain hE'
  have hP := layerPattern_of_canon hcrit hplain hwf hE hcoh
  exact ⟨⟨hplain', hsig.trans hs⟩, (layerreg1_replace hA hplain hplain' hE hE' hP hP').1 hcrit⟩

end WaveTurbulence.Links

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg1

/-!
# The drop budget of an embedded regular couple (packet C4, for TARGET Prop `layerreg2`)

For a layered garden in a canonical class and a regular couple embedded at `(a, b)` with parent layers
`q = parAt a`, `q' = parAt b` and incoherency index `g` (`incohCount`), the total drop
`∑_{𝔫 ∈ 𝒩} (𝔏_{𝔫^pr} - 𝔏_𝔫)` over its branching nodes is at most `|q - q'| + 9 p g` (`cpl_budget`),
where `p` bounds all layers. The proof follows TARGET's proof of `layerreg2`: a coherent type-1 root
pair costs `|q - q'|`, a coherent type-2 level costs `|q - q'|` (its lone pair is in layer `min(q, q')`,
by the cut argument of `layerreg1`), and every incoherent link costs at most `9p`.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **The incoherency index** of a list of links (T Def `defcoh`): the number of links with different
layers. -/
def incohCount (LG : LayeredGarden w) (L : List ((Fin w × Path) × (Fin w × Path))) : ℕ :=
  (L.filter fun l => layerAt LG l.1 ≠ layerAt LG l.2).length

/-- `|x - y|` on `ℕ`. -/
def ldist (x y : ℕ) : ℕ := (x - y) + (y - x)

variable (LG : LayeredGarden w) (p : ℕ)

theorem incohCount_append (L₁ L₂ : List ((Fin w × Path) × (Fin w × Path))) :
    incohCount LG (L₁ ++ L₂) = incohCount LG L₁ + incohCount LG L₂ := by
  simp [incohCount, List.filter_append]

theorem incohCount_cons (l : (Fin w × Path) × (Fin w × Path)) (L : List ((Fin w × Path) × (Fin w × Path))) :
    incohCount LG (l :: L) = (if layerAt LG l.1 = layerAt LG l.2 then 0 else 1) + incohCount LG L := by
  by_cases h : layerAt LG l.1 = layerAt LG l.2
  · simp [incohCount, h]
  · simp [incohCount, h]; omega

/-- The drop `𝔏_{𝔫^pr} - 𝔏_𝔫` at an address. -/
def dropAt (z : Fin w × Path) : ℕ := parAt LG p z - layerAt LG z

/-- The total drop over a set of addresses. -/
def budget (S : Finset (Fin w × Path)) : ℕ := ∑ z ∈ S, dropAt LG p z

theorem budget_union_le (S T : Finset (Fin w × Path)) :
    budget LG p (S ∪ T) ≤ budget LG p S + budget LG p T := by
  unfold budget
  have := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := dropAt LG p)
  omega

theorem budget_pair_le (x y : Fin w × Path) (S : Finset (Fin w × Path)) :
    budget LG p ({x} ∪ ({y} ∪ S)) ≤ dropAt LG p x + dropAt LG p y + budget LG p S := by
  have h1 := budget_union_le LG p {x} ({y} ∪ S)
  have h2 := budget_union_le LG p {y} S
  simp only [budget, Finset.sum_singleton] at h1 h2 ⊢
  omega

theorem budget_empty : budget LG p ∅ = 0 := by simp [budget]

theorem parAt_le (hp : ∀ a, LG.layer a ≤ p) (z : Fin w × Path) : parAt LG p z ≤ p := by
  unfold parAt
  split_ifs with h
  · unfold LayeredGarden.parentLayer
    split_ifs
    · exact le_rfl
    · exact hp _
  · exact Nat.zero_le _

theorem layerAt_le (hp : ∀ a, LG.layer a ≤ p) (z : Fin w × Path) : layerAt LG z ≤ p := by
  unfold layerAt
  split_ifs
  · exact hp _
  · exact Nat.zero_le _

/-- The parent layer of a node strictly below `a` is at most the layer of `a`. -/
theorem parAt_le_of_sunder {a z : Fin w × Path} (ha : a.2 ∈ (LG.garden.tree a.1).nodes)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (h : Under a z) (hne : z ≠ a) :
    parAt LG p z ≤ layerAt LG a := by
  obtain ⟨e1, q, hq⟩ := h
  have hq0 : q ≠ [] := by
    rintro rfl
    exact hne (Prod.ext e1.symm (by simpa using hq.symm))
  obtain ⟨q', i, rfl⟩ := List.eq_nil_or_concat q |>.resolve_left hq0
  have ez : z = addrExt (addrExt a q') [i] := by
    rw [addrExt_append]
    exact Prod.ext e1.symm (by rw [← hq, List.concat_eq_append]; rfl)
  rw [ez] at hz ⊢
  rw [parAt_child LG p i hz]
  have hpn : (addrExt a q').2 ∈ (LG.garden.tree (addrExt a q').1).nodes := by
    have := TTree.dropLast_mem_nodes _ hz
    simpa [addrExt] using this
  exact layerAt_le_of_under LG ha hpn (under_ext _ _)

/-- Parent layers do not increase downwards. -/
theorem parAt_le_parAt {a z : Fin w × Path} (hp : ∀ x, LG.layer x ≤ p)
    (ha : a.2 ∈ (LG.garden.tree a.1).nodes)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (h : Under a z) : parAt LG p z ≤ parAt LG p a := by
  by_cases hne : z = a
  · rw [hne]
  · exact (parAt_le_of_sunder LG p ha hz h hne).trans (layerAt_le_parAt LG p hp ha)

/-! ### Incoherence of chains -/

/-- The number of incoherent chain links `(𝔫_a, 𝔫_b)` (at all nesting levels). -/
def headIncoh : RegChain → ℤˣ → (Fin w × Path) → ℕ
  | .nil, _, _ => 0
  | .pair m _ _ inner rest, ζ, a =>
    (if layerAt LG a = layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) then 0 else 1) +
      headIncoh inner (slotSign ζ m.c) (addrExt a [m.c]) +
      headIncoh rest (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))

/-- The incoherence of the couples of a chain. -/
def couplesIncoh : RegChain → ℤˣ → (Fin w × Path) → ℕ
  | .nil, _, _ => 0
  | .pair m Qr Qg inner rest, ζ, a =>
    incohCount LG (if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) +
    incohCount LG (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) +
    couplesIncoh inner (slotSign ζ m.c) (addrExt a [m.c]) +
    couplesIncoh rest (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))

theorem incohCount_chain : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path),
    incohCount LG (X.linksAt ζ a) = headIncoh LG X ζ a + couplesIncoh LG X ζ a
  | .nil, _, _ => by simp [incohCount, RegChain.linksAt, headIncoh, couplesIncoh]
  | .pair m Qr Qg inner rest, ζ, a => by
    rw [RegChain.linksAt, incohCount_cons, incohCount_append, incohCount_append, incohCount_append,
      incohCount_chain inner, incohCount_chain rest, headIncoh, couplesIncoh]
    dsimp only
    omega

theorem spine_coh_of_headIncoh : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path),
    headIncoh LG X ζ a = 0 → ∀ l ∈ spineLinks X a, layerAt LG l.1 = layerAt LG l.2
  | .nil, _, _, _, l, hl => by simp [spineLinks] at hl
  | .pair m Qr Qg inner rest, ζ, a, h, l, hl => by
    simp only [headIncoh] at h
    simp only [spineLinks, List.mem_cons] at hl
    rcases hl with rfl | hl
    · by_contra hne
      simp only [hne, ↓reduceIte] at h
      omega
    · exact spine_coh_of_headIncoh rest (slotSign (slotSign ζ m.c) m.lone) _ (by omega) l hl

/-! ### The budget -/

variable {LG p}

theorem oriented_links_budget {P : Prop} [Decidable P] (Q : RegCpl) (x y : Fin w × Path)
    (H : ∀ u v, Embeds LG.garden Q u v → budget LG p (pairEndpoints (Q.linksAt u v)) ≤
      ldist (parAt LG p u) (parAt LG p v) + 9 * p * incohCount LG (Q.linksAt u v))
    (hE : if P then Embeds LG.garden Q x y else Embeds LG.garden Q y x) :
    budget LG p (pairEndpoints (if P then Q.linksAt x y else Q.linksAt y x)) ≤
      ldist (parAt LG p x) (parAt LG p y) +
        9 * p * incohCount LG (if P then Q.linksAt x y else Q.linksAt y x) := by
  split_ifs at hE ⊢
  · exact H x y hE
  · have := H y x hE
    unfold ldist at this ⊢
    omega

variable (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain)
include hcan hplain

mutual
/-- **The drop budget of an embedded regular couple**: at most `|q - q'| + 9 p g`. -/
theorem cpl_budget : (Q : RegCpl) → (a b : Fin w × Path) → Q.wf = true →
    Embeds LG.garden Q a b →
    budget LG p (pairEndpoints (Q.linksAt a b)) ≤
      ldist (parAt LG p a) (parAt LG p b) + 9 * p * incohCount LG (Q.linksAt a b)
  | .triv, a, b, _, _ => by simp [RegCpl.linksAt, budget_empty]
  | .type1 c Q₁ Q₂ Q₃, a, b, hwf, hE => by
    simp only [RegCpl.wf, Bool.and_eq_true] at hwf
    obtain ⟨E1, E2, E3⟩ := hE.type1
    have B1 := cpl_budget Q₁ _ _ hwf.1.1 E1
    have B2 := cpl_budget Q₂ _ _ hwf.1.2 E2
    have B3 := cpl_budget Q₃ _ _ hwf.2 E3
    have pa0 := parAt_child LG p 0 E1.nodeA
    have pb0 := parAt_child LG p _ E1.nodeB
    have pb1 := parAt_child LG p 1 E2.nodeA
    have pa1 := parAt_child LG p 1 E2.nodeB
    have pa2 := parAt_child LG p 2 E3.nodeA
    have pb2 := parAt_child LG p _ E3.nodeB
    rw [pa0, pb0] at B1
    rw [pb1, pa1] at B2
    rw [pa2, pb2] at B3
    have hsum := budget_pair_le LG p a b (pairEndpoints (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.linksAt (addrExt b [1]) (addrExt a [1]) ++ Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])))
    rw [← pairEndpoints_cons] at hsum
    have hu1 := budget_union_le LG p (pairEndpoints (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.linksAt (addrExt b [1]) (addrExt a [1]))) (pairEndpoints (Q₃.linksAt (addrExt a [2])
        (addrExt b [c.partner 2])))
    have hu2 := budget_union_le LG p (pairEndpoints (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])))
      (pairEndpoints (Q₂.linksAt (addrExt b [1]) (addrExt a [1])))
    rw [← pairEndpoints_append] at hu1 hu2
    have hinc : incohCount LG ((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b) =
        (if layerAt LG a = layerAt LG b then 0 else 1) +
          incohCount LG (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])) +
          incohCount LG (Q₂.linksAt (addrExt b [1]) (addrExt a [1])) +
          incohCount LG (Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])) := by
      rw [RegCpl.linksAt, incohCount_cons, incohCount_append, incohCount_append]
      dsimp only
      omega
    have la := layerAt_le_parAt LG p hcan.1 hE.nodeA
    have lb := layerAt_le_parAt LG p hcan.1 hE.nodeB
    have pA := parAt_le LG p hcan.1 a
    have pB := parAt_le LG p hcan.1 b
    rw [hinc, RegCpl.linksAt]
    unfold dropAt at hsum
    simp only [mul_add] at ⊢
    by_cases hab : layerAt LG a = layerAt LG b
    · have hpu : PairedUnder ((RegCpl.type1 c Q₁ Q₂ Q₃).pairsAt a b) a b := by
        intro q hq
        have r1 := cpl_endpoints_under (RegCpl.type1 c Q₁ Q₂ Q₃) a b q.1 (Finset.mem_union_right _
          ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))
        have r2 := cpl_endpoints_under (RegCpl.type1 c Q₁ Q₂ Q₃) a b q.2 (Finset.mem_union_right _
          ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))
        exact ⟨fun _ => r2, fun _ => r1⟩
      have hc := crit_apply hcan hplain hE hE.nodeA hE.nodeB (Or.inl (under_refl a))
        (Or.inr (under_refl b)) hE.indep hpu
      have key := min_eq_of_crit hab la lb hc
      simp only [hab, ↓reduceIte, mul_zero, zero_add] at ⊢
      rw [← hab] at B1 B2 B3 hsum lb
      unfold ldist at B1 B2 B3 ⊢
      simp only [Nat.sub_self, add_zero] at B1 B2 B3
      rcases le_total (parAt LG p a) (parAt LG p b) with h | h
      · rw [min_eq_left h] at key; omega
      · rw [min_eq_right h] at key; omega
    · simp only [hab, ↓reduceIte, mul_one] at ⊢
      have d1 : ldist (layerAt LG a) (layerAt LG b) ≤ p := by
        have := layerAt_le LG p hcan.1 a; have := layerAt_le LG p hcan.1 b; unfold ldist; omega
      have d2 : ldist (layerAt LG b) (layerAt LG a) ≤ p := by unfold ldist at d1 ⊢; omega
      unfold ldist at B1 B2 B3 d1 d2 ⊢
      omega
  | .type2 Xp Xm Qlp, a, b, hwf, hE => by
    have hwf' := hwf
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf'
    obtain ⟨⟨⟨⟨wp, wm⟩, wl⟩, wlt⟩, -⟩ := hwf'
    obtain ⟨Cp, Cm, El⟩ := hE.type2
    have BP := chain_budget Xp 1 a _ wp Cp
    have BM := chain_budget Xm (-1) b _ wm Cm
    have IP := incohCount_chain LG Xp 1 a
    have IM := incohCount_chain LG Xm (-1) b
    have hp := hcan.1
    have la := layerAt_le_parAt LG p hp hE.nodeA
    have lb := layerAt_le_parAt LG p hp hE.nodeB
    have pA := parAt_le LG p hp a
    have pB := parAt_le LG p hp b
    have nu := El.nodeA
    have nv := El.nodeB
    have lu := layerAt_le_parAt LG p hp nu
    have lv := layerAt_le_parAt LG p hp nv
    have pu := parAt_le_parAt LG p hp hE.nodeA nu (under_ext a _)
    have pv := parAt_le_parAt LG p hp hE.nodeB nv (under_ext b _)
    have pU := parAt_le LG p hp (addrExt a Xp.lonePath)
    have pV := parAt_le LG p hp (addrExt b Xm.lonePath)
    have hsum : budget LG p (pairEndpoints ((RegCpl.type2 Xp Xm Qlp).linksAt a b)) ≤
        budget LG p (pairEndpoints (Xp.linksAt 1 a)) + budget LG p (pairEndpoints (Xm.linksAt (-1) b)) +
          budget LG p (pairEndpoints (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))) := by
      rw [RegCpl.linksAt, pairEndpoints_append, pairEndpoints_append]
      have h1 := budget_union_le LG p (pairEndpoints (Xp.linksAt 1 a) ∪ pairEndpoints (Xm.linksAt (-1) b))
        (pairEndpoints (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)))
      have h2 := budget_union_le LG p (pairEndpoints (Xp.linksAt 1 a)) (pairEndpoints (Xm.linksAt (-1) b))
      omega
    have hinc : incohCount LG ((RegCpl.type2 Xp Xm Qlp).linksAt a b) = incohCount LG (Xp.linksAt 1 a) +
        incohCount LG (Xm.linksAt (-1) b) +
        incohCount LG (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)) := by
      rw [RegCpl.linksAt, incohCount_append, incohCount_append]
    -- the cut argument, when the level is locally coherent
    have cut : headIncoh LG Xp 1 a = 0 → headIncoh LG Xm (-1) b = 0 →
        layerAt LG (addrExt a Xp.lonePath) = layerAt LG (addrExt b Xm.lonePath) →
        layerAt LG (addrExt a Xp.lonePath) = min (parAt LG p a) (parAt LG p b) := by
      intro h0 h1 huv
      have uA : layerAt LG (addrExt a Xp.lonePath) ≤ parAt LG p a :=
        (layerAt_le_of_under LG hE.nodeA nu (under_ext a _)).trans la
      have vB : layerAt LG (addrExt b Xm.lonePath) ≤ parAt LG p b :=
        (layerAt_le_of_under LG hE.nodeB nv (under_ext b _)).trans lb
      by_contra hne
      have hlt : layerAt LG (addrExt a Xp.lonePath) < min (parAt LG p a) (parAt LG p b) :=
        lt_of_le_of_ne (le_min uA (huv ▸ vB)) hne
      obtain ⟨sP, hsP, hsP1, hsP2⟩ := spine_cut Xp 1 a _ Cp (spine_coh_of_headIncoh LG Xp 1 a h0) _ rfl
        (lt_of_lt_of_le hlt (min_le_left _ _))
      obtain ⟨sM, hsM, hsM1, hsM2⟩ := spine_cut Xm (-1) b _ Cm (spine_coh_of_headIncoh LG Xm (-1) b h1)
        _ rfl (huv ▸ lt_of_lt_of_le hlt (min_le_right _ _))
      have uP := spinePos_under Xp a sP hsP
      have uM := spinePos_under Xm b sM hsM
      have hc := crit_apply hcan hplain hE (spinePos_node Cp hsP) (spinePos_node Cm hsM)
        (Or.inl uP.1) (Or.inr uM.1) (indep_of_under hE.indep uP.1 uM.1)
        (type2_pairedUnder Xp Xm Qlp hE.indep hsP hsM)
      rw [hsP1, hsM1, ← huv, max_self] at hc
      exact absurd hc (not_le.2 (lt_min (hsP2) (huv ▸ hsM2)))
    rw [hinc, IP, IM]
    have pab : ldist (parAt LG p a) (parAt LG p b) + 2 * min (parAt LG p a) (parAt LG p b) =
        parAt LG p a + parAt LG p b := by
      unfold ldist; rcases le_total (parAt LG p a) (parAt LG p b) with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; omega
    cases Qlp with
    | type2 _ _ _ => simp [RegCpl.isType2] at wlt
    | triv =>
      have hL : budget LG p (pairEndpoints (RegCpl.triv.linksAt (addrExt a Xp.lonePath)
          (addrExt b Xm.lonePath))) = 0 := by simp [RegCpl.linksAt, budget_empty]
      have gL : incohCount LG (RegCpl.triv.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)) = 0 := by
        simp [RegCpl.linksAt, incohCount]
      have huv : layerAt LG (addrExt a Xp.lonePath) = layerAt LG (addrExt b Xm.lonePath) :=
        El.pair_layer LG (q := (addrExt a Xp.lonePath, addrExt b Xm.lonePath)) (by simp [RegCpl.pairsAt])
      rw [gL]
      simp only [mul_add, add_zero] at ⊢
      by_cases hz : headIncoh LG Xp 1 a = 0 ∧ headIncoh LG Xm (-1) b = 0
      · have key := cut hz.1 hz.2 huv
        rw [hz.1] at BP ⊢
        rw [hz.2] at BM ⊢
        simp only [mul_zero, add_zero] at BP BM ⊢
        omega
      · have hpos : p ≤ p * headIncoh LG Xp 1 a + p * headIncoh LG Xm (-1) b := by
          rcases Nat.eq_zero_or_pos (headIncoh LG Xp 1 a) with h0 | h0
          · have h1 : 0 < headIncoh LG Xm (-1) b := Nat.pos_of_ne_zero fun h1 => hz ⟨h0, h1⟩
            have := Nat.le_mul_of_pos_right p h1; omega
          · have := Nat.le_mul_of_pos_right p h0; omega
        simp only [Nat.mul_assoc] at BP BM ⊢
        omega
    | type1 c' A B C =>
      have wl' := wl
      simp only [RegCpl.wf, Bool.and_eq_true] at wl'
      obtain ⟨EA, EB, EC⟩ := El.type1
      have BA := cpl_budget A _ _ wl'.1.1 EA
      have BB := cpl_budget B _ _ wl'.1.2 EB
      have BC := cpl_budget C _ _ wl'.2 EC
      rw [parAt_child LG p 0 EA.nodeA, parAt_child LG p _ EA.nodeB] at BA
      rw [parAt_child LG p 1 EB.nodeA, parAt_child LG p 1 EB.nodeB] at BB
      rw [parAt_child LG p 2 EC.nodeA, parAt_child LG p _ EC.nodeB] at BC
      set u := addrExt a Xp.lonePath with hu
      set v := addrExt b Xm.lonePath with hv
      have hLsum := budget_pair_le LG p u v (pairEndpoints (A.linksAt (addrExt u [0]) (addrExt v [c'.partner 0]) ++
        B.linksAt (addrExt v [1]) (addrExt u [1]) ++ C.linksAt (addrExt u [2]) (addrExt v [c'.partner 2])))
      rw [← pairEndpoints_cons, ← RegCpl.linksAt] at hLsum
      have hu1 := budget_union_le LG p (pairEndpoints (A.linksAt (addrExt u [0]) (addrExt v [c'.partner 0]) ++
        B.linksAt (addrExt v [1]) (addrExt u [1]))) (pairEndpoints (C.linksAt (addrExt u [2])
          (addrExt v [c'.partner 2])))
      have hu2 := budget_union_le LG p (pairEndpoints (A.linksAt (addrExt u [0]) (addrExt v [c'.partner 0])))
        (pairEndpoints (B.linksAt (addrExt v [1]) (addrExt u [1])))
      rw [← pairEndpoints_append] at hu1 hu2
      have gL : incohCount LG ((RegCpl.type1 c' A B C).linksAt u v) =
          (if layerAt LG u = layerAt LG v then 0 else 1) +
            incohCount LG (A.linksAt (addrExt u [0]) (addrExt v [c'.partner 0])) +
            incohCount LG (B.linksAt (addrExt v [1]) (addrExt u [1])) +
            incohCount LG (C.linksAt (addrExt u [2]) (addrExt v [c'.partner 2])) := by
        rw [RegCpl.linksAt, incohCount_cons, incohCount_append, incohCount_append]
        dsimp only
        omega
      rw [gL]
      unfold dropAt at hLsum
      have d1 : ldist (layerAt LG u) (layerAt LG v) ≤ p := by
        have := layerAt_le LG p hp u; have := layerAt_le LG p hp v; unfold ldist; omega
      have d2 : ldist (layerAt LG v) (layerAt LG u) ≤ p := by unfold ldist at d1 ⊢; omega
      simp only [mul_add] at ⊢
      by_cases hz : headIncoh LG Xp 1 a = 0 ∧ headIncoh LG Xm (-1) b = 0 ∧ layerAt LG u = layerAt LG v
      · have key := cut hz.1 hz.2.1 hz.2.2
        rw [hz.1] at BP ⊢
        rw [hz.2.1] at BM ⊢
        rw [← hz.2.2] at BA BB BC lv
        simp only [hz.2.2, ↓reduceIte, mul_zero, add_zero, zero_add] at BP BM ⊢
        unfold ldist at BA BB BC
        simp only [Nat.sub_self, add_zero] at BA BB BC
        omega
      · by_cases huv : layerAt LG u = layerAt LG v
        · have hpos : p ≤ p * headIncoh LG Xp 1 a + p * headIncoh LG Xm (-1) b := by
            rcases Nat.eq_zero_or_pos (headIncoh LG Xp 1 a) with h0 | h0
            · have h1 : 0 < headIncoh LG Xm (-1) b :=
                Nat.pos_of_ne_zero fun h1 => hz ⟨h0, h1, huv⟩
              have := Nat.le_mul_of_pos_right p h1; omega
            · have := Nat.le_mul_of_pos_right p h0; omega
          simp only [huv, ↓reduceIte, mul_zero, zero_add] at ⊢
          rw [← huv] at BA BB BC
          unfold ldist at BA BB BC
          simp only [Nat.sub_self, add_zero] at BA BB BC
          simp only [Nat.mul_assoc] at BP BM BA BB BC ⊢
          omega
        · simp only [huv, ↓reduceIte, mul_one] at ⊢
          unfold ldist at BA BB BC d1 d2
          simp only [Nat.mul_assoc] at BP BM BA BB BC ⊢
          omega

/-- **The drop budget of an embedded chain**: the chain nodes telescope to `q - 𝔏_{lone^pr}`, every
incoherent chain link costs `2p` and its couples are budgeted by `cpl_budget`. -/
theorem chain_budget : (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) → (h : TTree) → X.wf = true →
    ChainEmb LG.garden X ζ a h →
    budget LG p (pairEndpoints (X.linksAt ζ a)) ≤ (parAt LG p a - parAt LG p (addrExt a X.lonePath)) +
      2 * p * headIncoh LG X ζ a + 9 * p * couplesIncoh LG X ζ a
  | .nil, _, _, _, _, _ => by simp [RegChain.linksAt, budget_empty]
  | .pair m Qr Qg inner rest, ζ, a, h, hwf, hC => by
    have _ := hplain
    simp only [RegChain.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨wr, wg⟩, wi⟩, ws⟩ := hwf
    obtain ⟨ER, EG, EI, ES⟩ := hC.parts
    have BR := oriented_links_budget Qr _ _ (fun u v hE => cpl_budget Qr u v wr hE) ER
    have BG := oriented_links_budget Qg _ _ (fun u v hE => cpl_budget Qg u v wg hE) EG
    have BI := chain_budget inner _ _ _ wi EI
    have BS := chain_budget rest _ _ _ ws ES
    have hp := hcan.1
    have tr := hC.tree
    have nT : ∀ i, (addrExt a [i]).2 ∈ (LG.garden.tree (addrExt a [i]).1).nodes :=
      fun i => node_ext hC.node tr (top_mem m Qr Qg inner rest ζ h i)
    have nB : ∀ k, (addrExt a ([m.c] ++ inner.lonePath ++ [k])).2 ∈
        (LG.garden.tree (addrExt a ([m.c] ++ inner.lonePath ++ [k])).1).nodes :=
      fun k => node_ext hC.node tr (bottom_mem m Qr Qg inner rest ζ h k)
    have nlone := nodeOfChainEmb hC
    have nnb : (addrExt a ([m.c] ++ inner.lonePath)).2 ∈
        (LG.garden.tree (addrExt a ([m.c] ++ inner.lonePath)).1).nodes := by
      have := nodeOfChainEmb EI; rwa [addrExt_append] at this
    have pT : ∀ i, parAt LG p (addrExt a [i]) = layerAt LG a := fun i => parAt_child LG p i (nT i)
    have pBt : ∀ k, parAt LG p (addrExt a ([m.c] ++ inner.lonePath ++ [k])) =
        layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) := fun k => parAt_bottom _ k (nB k)
    rw [pT, pBt] at BR BG
    rw [pT, addrExt_append] at BI
    rw [pBt, ← chain_lonePath_eq m Qr Qg inner rest a] at BS
    have la := layerAt_le_parAt LG p hp hC.node
    have lnb := layerAt_le_parAt LG p hp nnb
    have h1 : parAt LG p (addrExt a ([m.c] ++ inner.lonePath)) ≤ layerAt LG a :=
      parAt_le_of_sunder LG p hC.node nnb (under_ext _ _) (addrExt_cons_ne a m.c inner.lonePath)
    have h2 : parAt LG p (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) ≤
        layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) := by
      apply parAt_le_of_sunder LG p nnb nlone
      · exact ⟨rfl, ⟨[m.lone] ++ rest.lonePath, by simp [addrExt, RegChain.lonePath]⟩⟩
      · intro he
        have := congrArg (fun z : Fin w × Path => z.2.length) he
        simp [addrExt, RegChain.lonePath] at this
    have hsum : budget LG p (pairEndpoints ((RegChain.pair m Qr Qg inner rest).linksAt ζ a)) ≤
        dropAt LG p a + dropAt LG p (addrExt a ([m.c] ++ inner.lonePath)) +
          budget LG p (pairEndpoints (if slotSign ζ m.red.1 = 1 then
            Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))) +
          budget LG p (pairEndpoints (if slotSign ζ m.green.1 = 1 then
            Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))) +
          budget LG p (pairEndpoints (inner.linksAt (slotSign ζ m.c) (addrExt a [m.c]))) +
          budget LG p (pairEndpoints (rest.linksAt (slotSign (slotSign ζ m.c) m.lone)
            (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))) := by
      rw [RegChain.linksAt, pairEndpoints_cons]
      refine (budget_pair_le LG p _ _ _).trans ?_
      rw [pairEndpoints_append, pairEndpoints_append, pairEndpoints_append]
      have u1 := budget_union_le LG p (pairEndpoints (if slotSign ζ m.red.1 = 1 then
            Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∪
          pairEndpoints (if slotSign ζ m.green.1 = 1 then
            Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∪
          pairEndpoints (inner.linksAt (slotSign ζ m.c) (addrExt a [m.c])))
        (pairEndpoints (rest.linksAt (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))))
      have u2 := budget_union_le LG p (pairEndpoints (if slotSign ζ m.red.1 = 1 then
            Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∪
          pairEndpoints (if slotSign ζ m.green.1 = 1 then
            Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])))
        (pairEndpoints (inner.linksAt (slotSign ζ m.c) (addrExt a [m.c])))
      have u3 := budget_union_le LG p (pairEndpoints (if slotSign ζ m.red.1 = 1 then
            Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])))
          (pairEndpoints (if slotSign ζ m.green.1 = 1 then
            Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])))
      omega
    unfold dropAt at hsum
    rw [headIncoh, couplesIncoh]
    simp only [mul_add] at ⊢
    by_cases hab : layerAt LG a = layerAt LG (addrExt a ([m.c] ++ inner.lonePath))
    · simp only [hab, ↓reduceIte, mul_zero, zero_add] at ⊢
      rw [← hab] at BR BG
      unfold ldist at BR BG
      simp only [Nat.sub_self, add_zero] at BR BG
      rw [← hab] at h2 lnb hsum BS
      simp only [Nat.mul_assoc] at BR BG BI BS ⊢
      omega
    · simp only [hab, ↓reduceIte, mul_one] at ⊢
      have d1 : ldist (layerAt LG a) (layerAt LG (addrExt a ([m.c] ++ inner.lonePath))) ≤ p := by
        have := layerAt_le LG p hp a
        have := layerAt_le LG p hp (addrExt a ([m.c] ++ inner.lonePath))
        unfold ldist; omega
      unfold ldist at BR BG d1
      simp only [Nat.mul_assoc] at BR BG BI BS ⊢
      omega
end

end WaveTurbulence.Links

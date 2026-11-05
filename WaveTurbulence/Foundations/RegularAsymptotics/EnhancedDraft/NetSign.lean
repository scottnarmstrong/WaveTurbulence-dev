/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Encoded2

/-!
# Net signs (DH21 §4.4.5 (2), (defzetaq), (defzetat))

DH21 L900: with `ζ*(𝒬) = ∏_{𝔫 ∈ 𝒩*} (iζ_𝔫)` (defzetaq) and `ζ*(𝒯) = ∏_{𝔫 ∈ 𝒩} (-1)^{𝚌_𝔫}`
(defzetat), "these signs are preserved under equivalence, and also under the bijection in
Proposition 4.23 (so `ζ*(𝒬) = ζ*(𝒯)` if `𝒯` is associated to `𝒬`)".

* `Shape.netSign`: the product of `(-1)^{𝚌}` over the tuples, recursively; invariant under
  `Shape.Equiv` (`Shape.Equiv.netSign_eq`);
* `EncTree.netSign` (defzetat) equals the net sign of its shape (`EncTree.netSign_eq_shape`);
* for a couple carrier `G` decoded by a dominant code `𝒬`, `ζ(𝒢) = ∏_{𝔫 ∈ 𝒩*} (iζ_𝔫)` (B1
  `Garden.zeta`) is the net sign of the shape of `(𝒬, ∅)` (`zeta_eq_netSign`), computed link by
  link: a type-1 root link contributes `(i)(-i) = 1`, a chain link `(𝔫_{2j-1}, 𝔫_{2j})` contributes
  `(iζ)(iζ') = (-1)^{𝚌_j}`;
* hence `ζ*(𝒬) = ζ*(𝒯(𝒬))` (`zeta_eq_netSign_cplEnc`) and equivalent dominant couples have the same
  net sign (`zeta_eq_of_equiv`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg EncTree

/-- `(-1)^𝚌` for the first code digit `𝚌 = c + 1`. -/
def codeSign (c : Fin 3) : ℤ := if c = 1 then 1 else -1

mutual
/-- The net sign of a shape. -/
def Shape.netSign : Shape → ℤ
  | .triv => 1
  | .type1 a b c => a.netSign * b.netSign * c.netSign
  | .type2 L Y => L.netSign * Y.netSign

/-- The net sign of a list of tuples. -/
def Tuples.netSign : Tuples → ℤ
  | .nil => 1
  | .cons _ c X₁ X₂ rest => codeSign c * X₁.netSign * X₂.netSign * rest.netSign
end

theorem Tuples.prod_cons {M : Type*} [CommMonoid M] (I : Bool) (c : Fin 3) (X₁ X₂ : Shape)
    (rest : Tuples) (f : Bool × Fin 3 × Shape × Shape → M) :
    ∏ i, f ((Tuples.cons I c X₁ X₂ rest).get i) = f (I, c, X₁, X₂) * ∏ i, f (rest.get i) := by
  show ∏ i : Fin (rest.length + 1), _ = _
  rw [Fin.prod_univ_succ]
  rfl

theorem Tuples.netSign_eq_prod : (L : Tuples) →
    L.netSign = ∏ i, (codeSign (L.get i).2.1 * (L.get i).2.2.1.netSign * (L.get i).2.2.2.netSign)
  | .nil => by show (1 : ℤ) = ∏ i : Fin 0, _; simp
  | .cons I c X₁ X₂ rest => by
    rw [Tuples.prod_cons (f := fun t => codeSign t.2.1 * t.2.2.1.netSign * t.2.2.2.netSign),
      ← Tuples.netSign_eq_prod rest]
    simp only [Tuples.netSign]

theorem Tuples.netSign_append : (L L' : Tuples) → (L.append L').netSign = L.netSign * L'.netSign
  | .nil, L' => by simp [Tuples.append, Tuples.netSign]
  | .cons I c X₁ X₂ rest, L' => by
    simp only [Tuples.append, Tuples.netSign, Tuples.netSign_append rest L']; ring

/-- **Net signs are preserved under equivalence** (DH21 L900). -/
theorem Shape.Equiv.netSign_eq {s t : Shape} (h : Shape.Equiv s t) : s.netSign = t.netSign := by
  induction h with
  | triv => rfl
  | type1 _ _ _ ih₁ ih₂ ih₃ => simp [Shape.netSign, ih₁, ih₂, ih₃]
  | @type2 L L' Y Y' e _ hc _ _ _ ih₁ ih₂ ihY =>
    simp only [Shape.netSign, Tuples.netSign_eq_prod, ihY]
    congr 1
    rw [← Equiv.prod_comp e (fun j => codeSign (L'.get j).2.1 * (L'.get j).2.2.1.netSign *
      (L'.get j).2.2.2.netSign)]
    exact Finset.prod_congr rfl fun i _ => by rw [hc i, ih₁ i, ih₂ i]

/-! ### Encoded trees -/

/-- `(-1)^𝚌` for a node code. -/
def ECode.sign : ECode → ℤ
  | .c0 => 1
  | .c1 => -1
  | .c2 => 1
  | .c3 => -1

/-- **`ζ*(𝒯) = ∏_{𝔫 ∈ 𝒩} (-1)^{𝚌_𝔫}`** (DH21 (defzetat)). -/
def EncTree.netSign : EncTree → ℤ
  | .leaf => 1
  | .node c a b d => c.sign * a.netSign * b.netSign * d.netSign

theorem toShape_netSign (p : Tuples × Shape) : (toShape p).netSign = p.1.netSign * p.2.netSign := by
  obtain ⟨L, s⟩ := p
  cases L with
  | nil => simp [toShape, Tuples.netSign]
  | cons I c X₁ X₂ rest => rfl

theorem EncTree.netSign_shapeAux : (T : EncTree) →
    T.netSign = T.shapeAux.1.netSign * T.shapeAux.2.netSign
  | .leaf => rfl
  | .node .c0 a b d => by
    simp only [EncTree.netSign, shapeAux, Tuples.netSign, Shape.netSign, toShape_netSign,
      ← EncTree.netSign_shapeAux a, ← EncTree.netSign_shapeAux b, ← EncTree.netSign_shapeAux d,
      ECode.sign]
    ring
  | .node .c1 t a b => by
    simp only [EncTree.netSign, shapeAux, Tuples.netSign, toShape_netSign,
      ← EncTree.netSign_shapeAux a, ← EncTree.netSign_shapeAux b, EncTree.netSign_shapeAux t,
      ECode.sign, codeSign]
    simp; ring
  | .node .c2 a t b => by
    simp only [EncTree.netSign, shapeAux, Tuples.netSign, toShape_netSign,
      ← EncTree.netSign_shapeAux a, ← EncTree.netSign_shapeAux b, EncTree.netSign_shapeAux t,
      ECode.sign, codeSign]
    simp; ring
  | .node .c3 a b t => by
    simp only [EncTree.netSign, shapeAux, Tuples.netSign, toShape_netSign,
      ← EncTree.netSign_shapeAux a, ← EncTree.netSign_shapeAux b, EncTree.netSign_shapeAux t,
      ECode.sign, codeSign]
    simp; ring

/-- The net sign of an encoded tree is that of its shape. -/
theorem EncTree.netSign_eq_shape (T : EncTree) : T.netSign = T.shape.netSign := by
  rw [shape, toShape_netSign, EncTree.netSign_shapeAux]

/-- **Equivalent encoded trees have the same net sign.** -/
theorem EncTree.netSign_eq_of_equiv {T T' : EncTree} (h : T ≈ T') : T.netSign = T'.netSign := by
  rw [EncTree.netSign_eq_shape, EncTree.netSign_eq_shape]
  exact Shape.Equiv.netSign_eq h

/-! ### Couples: `ζ*(𝒬)` link by link -/

/-- The factor `(iζ_𝔫)(iζ_{𝔫'})` of a link. -/
noncomputable def linkFactor {w : ℕ} (σ : Fin w → ℤˣ) (l : (Fin w × Path) × (Fin w × Path)) : ℂ :=
  (Complex.I * ((nodeSign σ l.1 : ℤ) : ℂ)) * (Complex.I * ((nodeSign σ l.2 : ℤ) : ℂ))

theorem red_sign (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.red.2 = -slotSign ζ m.red.1 := by
  obtain ⟨c, b⟩ := m
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases b <;> decide

theorem green_sign (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.green.2 = -slotSign ζ m.green.1 := by
  obtain ⟨c, b⟩ := m
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases b <;> decide

theorem nodeSign_ext {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path) (p : Path) :
    nodeSign σ (addrExt a p) = pathSign (nodeSign σ a) p := nodeSign_addrExt σ a p

theorem chain_link_factor {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path) (ζ : ℤˣ)
    (ha : nodeSign σ a = ζ) (c : Fin 3) :
    linkFactor σ (a, addrExt a [c]) = (codeSign c : ℂ) := by
  have h2 : nodeSign σ (addrExt a [c]) = slotSign ζ c := by
    rw [nodeSign_ext, ha, pathSign_singleton]
  unfold linkFactor codeSign
  rw [h2, ha]
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;>
    simp [slotSign]

/-- A placed couple whose `+` tree is at `a`. -/
theorem placed_signs {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path) (ζ : ℤˣ) (ha : nodeSign σ a = ζ)
    (m : MiniTreeCode) :
    nodeSign σ (addrExt a [m.red.1]) = slotSign ζ m.red.1 ∧
    nodeSign σ (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2])) = -slotSign ζ m.red.1 ∧
    nodeSign σ (addrExt a [m.green.1]) = slotSign ζ m.green.1 ∧
    nodeSign σ (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2])) =
      -slotSign ζ m.green.1 := by
  simp only [nodeSign_ext, ha, pathSign_singleton, RegChain.lonePath, List.append_nil,
    Comb.pathSign_append]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [red_sign, green_sign]

mutual
/-- The product of the link factors of a dominant couple code placed with signs `(+, -)`. -/
theorem linksAt_prod {w : ℕ} (σ : Fin w → ℤˣ) : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → nodeSign σ a = 1 → nodeSign σ b = -1 →
    ((Q.linksAt a b).map (linkFactor σ)).prod = ((cplShape0 Q).netSign : ℂ)
  | .triv, _, _, _, _, _ => by simp [RegCpl.linksAt, cplShape0, Shape.netSign]
  | .type1 c Q₁ Q₂ Q₃, h, a, b, sa, sb => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    have s0 : ∀ i, nodeSign σ (addrExt a [i]) = slotSign 1 i := fun i => by
      rw [nodeSign_ext, sa, pathSign_singleton]
    have s1 : ∀ i, nodeSign σ (addrExt b [i]) = slotSign (-1) i := fun i => by
      rw [nodeSign_ext, sb, pathSign_singleton]
    have hp0 : c.partner 0 ≠ 1 := by fin_cases c <;> decide
    have hp2 : c.partner 2 ≠ 1 := by fin_cases c <;> decide
    have e₁ := linksAt_prod σ Q₁ h.1.1 (addrExt a [0]) (addrExt b [c.partner 0])
      (by rw [s0]; rfl) (by rw [s1]; simp [slotSign, hp0])
    have e₂ := linksAt_prod σ Q₂ h.1.2 (addrExt b [1]) (addrExt a [1])
      (by rw [s1]; simp [slotSign]) (by rw [s0]; simp [slotSign])
    have e₃ := linksAt_prod σ Q₃ h.2 (addrExt a [2]) (addrExt b [c.partner 2])
      (by rw [s0]; rfl) (by rw [s1]; simp [slotSign, hp2])
    have er : linkFactor σ (a, b) = 1 := by
      unfold linkFactor; rw [sa, sb]; simp
    simp only [RegCpl.linksAt, List.map_cons, List.map_append, List.prod_cons, List.prod_append,
      e₁, e₂, e₃, er, cplShape0, Shape.netSign, Int.cast_mul]
    ring
  | .type2 Xp Xm Qlp, h, a, b, sa, sb => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    have ep := chain_linksAt_prod σ Xp h.1.1 1 a sa
    have em := chain_linksAt_prod σ Xm h.1.2 (-1) b sb
    have el := linksAt_prod σ Qlp h.2 (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)
      (by rw [nodeSign_ext, sa, lonePath_sign]) (by rw [nodeSign_ext, sb, lonePath_sign])
    simp only [RegCpl.linksAt, List.map_append, List.prod_append, ep, em, el, cplShape0,
      Shape.netSign, Tuples.netSign_append, Int.cast_mul]

/-- The product of the link factors of a dominant chain code rooted at `a` of sign `ζ`. -/
theorem chain_linksAt_prod {w : ℕ} (σ : Fin w → ℤˣ) : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) → nodeSign σ a = ζ →
    ((X.linksAt ζ a).map (linkFactor σ)).prod = ((chainTuples0 X).netSign : ℂ)
  | .nil, _, _, _, _ => by simp [RegChain.linksAt, chainTuples0, Tuples.netSign]
  | .pair m Qr Qg inner rest, h, ζ, a, ha => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    obtain ⟨r1, r2, g1, g2⟩ := placed_signs σ a ζ ha m
    have eR : ((if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).map (linkFactor σ)).prod = ((cplShape0 Qr).netSign : ℂ) := by
      split_ifs with hz
      · exact linksAt_prod σ Qr hr _ _ (by rw [r1, hz]) (by rw [r2, hz])
      · have hz' := slotSign_eq_neg_one hz
        exact linksAt_prod σ Qr hr _ _ (by rw [r2, hz', neg_neg]) (by rw [r1, hz'])
    have eG : ((if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).map (linkFactor σ)).prod = ((cplShape0 Qg).netSign : ℂ) := by
      split_ifs with hz
      · exact linksAt_prod σ Qg hg _ _ (by rw [g1, hz]) (by rw [g2, hz])
      · have hz' := slotSign_eq_neg_one hz
        exact linksAt_prod σ Qg hg _ _ (by rw [g2, hz', neg_neg]) (by rw [g1, hz'])
    have eS := chain_linksAt_prod σ rest hs (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone]))
      (by simp only [nodeSign_ext, ha, RegChain.lonePath, List.append_nil, Comb.pathSign_append,
        pathSign_singleton])
    have eH : linkFactor σ (a, addrExt a ([m.c] ++ RegChain.nil.lonePath)) = (codeSign m.c : ℂ) := by
      simpa [RegChain.lonePath] using chain_link_factor σ a ζ ha m.c
    simp only [RegChain.linksAt, List.map_cons, List.map_append, List.prod_cons, List.prod_append,
      eH, eR, eG, eS, RegChain.linksAt, List.map_nil, List.prod_nil, chainTuples0, Tuples.netSign,
      Int.cast_mul, mul_one]
    ring
end

/-! ### Carriers -/

open Finset in
/-- A product over the branching nodes of a couple carrier, link by link. -/
theorem prod_branch_links {M : Type*} [CommMonoid M] {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (f : GBranch G.tree → M) :
    ∏ b, f b = ∏ j : Fin Q.links.length,
      f (chosenBranch hQ j) * f (linkPartner hQ (chosenBranch hQ j)) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not univ
    (fun b : GBranch G.tree => b.1 ∈ chosenSet Q.links)]
  have h2 : ∏ b ∈ univ.filter (fun b : GBranch G.tree => ¬ b.1 ∈ chosenSet Q.links), f b =
      ∏ b ∈ univ.filter (fun b : GBranch G.tree => b.1 ∈ chosenSet Q.links),
        f (linkPartner hQ b) := by
    refine Finset.prod_nbij' (linkPartner hQ) (linkPartner hQ) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      have hb' : b.1 ∉ chosenSet Q.links := by simpa using hb
      rcases chosen_xor hQ b with h | h
      · exact absurd h.1 hb'
      · simpa using h.2
    · intro b hb
      have hb' : b.1 ∈ chosenSet Q.links := by simpa using hb
      rcases chosen_xor hQ b with h | h
      · simpa using h.2
      · exact absurd hb' h.1
    · intro b _; exact linkPartner_linkPartner hQ b
    · intro b _; exact linkPartner_linkPartner hQ b
    · intro b _; rw [linkPartner_linkPartner]
  rw [h2, ← Finset.prod_mul_distrib]
  symm
  refine Finset.prod_bij (fun j _ => chosenBranch hQ j) ?_ ?_ ?_ ?_
  · intro j _
    simp only [mem_filter, mem_univ, true_and]
    exact List.mem_toFinset.2 (List.mem_map_of_mem (List.get_mem _ _))
  · intro j₁ _ j₂ _ h
    have h' : chosenNode Q j₁ = chosenNode Q j₂ := congrArg Subtype.val h
    clear h
    exact Fin.ext (by rw [← idxOf_chosenNode Q j₁, ← idxOf_chosenNode Q j₂, h'])
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hm : b.1 ∈ Q.links.map Prod.fst := List.mem_toFinset.1 hb
    have hlt : (Q.links.map Prod.fst).idxOf b.1 < Q.links.length := by
      simpa using List.idxOf_lt_length_of_mem hm
    refine ⟨⟨_, hlt⟩, mem_univ _, Subtype.ext ?_⟩
    have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
    rw [List.getElem_map] at this
    show (Q.links.get ⟨_, hlt⟩).1 = b.1
    rw [List.get_eq_getElem]
    exact this
  · intro j _
    rfl

/-- **`ζ*(𝒬) = ∏_{𝔫 ∈ 𝒩*} (iζ_𝔫)` of a dominant couple is the net sign of its shape** (DH21
(defzetaq), L900). -/
theorem zeta_eq_netSign {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (hdom : Q.dominant = true) : G.zeta = ((cplShape0 Q).netSign : ℂ) := by
  unfold Garden.zeta
  rw [prod_branch_links hQ]
  have hlink : ∀ j : Fin Q.links.length,
      Complex.I * (((G.sign (chosenBranch hQ j).toNode : ℤˣ) : ℤ) : ℂ) *
        (Complex.I * (((G.sign (linkPartner hQ (chosenBranch hQ j)).toNode : ℤˣ) : ℤ) : ℂ)) =
      linkFactor G.sig (Q.links.get j) := by
    intro j
    have hl : Q.links.get j ∈ Q.links := List.get_mem _ _
    have h2 := linkPartner_of_fst hQ hl (chosenBranch hQ j) rfl
    unfold linkFactor
    show _ * (Complex.I * (((nodeSign G.sig (linkPartner hQ (chosenBranch hQ j)).1 : ℤˣ) : ℤ) : ℂ)) = _
    rw [h2]
    rfl
  rw [Finset.prod_congr rfl fun j _ => hlink j]
  have hfun : ∏ j : Fin Q.links.length, linkFactor G.sig (Q.links.get j) =
      (Q.links.map (linkFactor G.sig)).prod := by
    rw [← Fin.prod_univ_fun_getElem Q.links (linkFactor G.sig)]
    rfl
  rw [hfun]
  refine linksAt_prod G.sig Q hdom _ _ ?_ ?_
  · show pathSign (G.sig 0) [] = 1
    rw [hG.2]; rfl
  · show pathSign (G.sig 1) [] = -1
    rw [hG.2]; rfl

/-- **`ζ*(𝒬) = ζ*(𝒯(𝒬))`** (DH21 L900): the net sign of a dominant couple equals the net sign of its
encoded tree. -/
theorem zeta_eq_netSign_cplEnc {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (hgood : Good Q) : G.zeta = ((cplEnc Q).netSign : ℂ) := by
  rw [zeta_eq_netSign hQ hG hgood.2, EncTree.netSign_eq_shape, shape_cplEnc Q hgood.1]

/-- **Equivalent dominant couples have the same net sign** (DH21 L900). -/
theorem zeta_eq_of_equiv {G G' : Garden 2} {q q' : DomCpl} (hQ : q.1.Decodes G) (hG : IsCouple G)
    (hQ' : q'.1.Decodes G') (hG' : IsCouple G') (h : q ≈ q') : G.zeta = G'.zeta := by
  rw [zeta_eq_netSign hQ hG q.2.2, zeta_eq_netSign hQ' hG' q'.2.2, Shape.Equiv.netSign_eq h]

end WaveTurbulence.Links

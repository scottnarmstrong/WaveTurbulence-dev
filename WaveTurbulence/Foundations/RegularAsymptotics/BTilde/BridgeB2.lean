/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.Bridge
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.BridgeTree
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.BtRecB

/-!
# The B̃ bridge with B2's links and wt-torus's signs

The statements of `Bridge` restated with B2's own `Q.links` and `chosenSet Q.links` (B2 draft §5),
wt-torus's sign `Cancel.zetaA` and the family `BtJR` of `btRec_BtJR`, in the form consumed by
wt-torus's `Cancel.maincancel` and `Cancel.regcplcal` (DH21 Props 7.4, 7.5):
* `maincoef_BtJR`: the expansion data `MCExp … zetaA (chosenSet Q.links) (BtJR Q root root)`;
* `cplB_eq_BtJR`, `phaseIntegral_kDomain_eq_BtJR`: the garden-defined `B̃_Q` is `BtJR Q root root`;
* `maincoef_garden_B2`: DH21 Prop 5.1 for regular couples through gardens;
* `LinkRelG`: the link relation with the garden's own signs, on B2's links `Q.links` (couples) and
  `X.treeLinks ζ` (trees, addresses `Fin 1 × Path`): `cplB_eq_BtJR_G`, `treeAstar_eq_Atilde_G`.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

mutual
/-- ClassJR's links are B2's. -/
theorem linksAt_toJR {w : ℕ} : ∀ (Q : RegCpl) (a b : Fin w × TTree.Path),
    (toJR Q).linksAt a b = Q.linksAt a b
  | .triv, _, _ => rfl
  | .type1 _ Q₁ Q₂ Q₃, _, _ => by
    simp only [toJR, ClassJR.RegCpl.linksAt, RegCpl.linksAt, linksAt_toJR Q₁, linksAt_toJR Q₂,
      linksAt_toJR Q₃]
    rfl
  | .type2 Xp Xm Qlp, _, _ => by
    simp only [toJR, ClassJR.RegCpl.linksAt, RegCpl.linksAt, linksAt_toJRc Xp, linksAt_toJRc Xm,
      linksAt_toJR Qlp, lonePath_toJRc]
    rfl

theorem linksAt_toJRc {w : ℕ} : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × TTree.Path),
    (toJRc X).linksAt ζ a = X.linksAt ζ a
  | .nil, _, _ => rfl
  | .pair _ Qr Qg inner rest, _, _ => by
    simp only [toJRc, ClassJR.RegChain.linksAt, RegChain.linksAt, linksAt_toJR Qr, linksAt_toJR Qg,
      linksAt_toJRc inner, linksAt_toJRc rest, lonePath_toJRc]
    rfl
end

theorem links_toJR (Q : RegCpl) : (toJR Q).links = Q.links := linksAt_toJR Q _ _

theorem chosenSet_toJR (Q : RegCpl) : ClassJR.chosenSet (toJR Q).links = chosenSet Q.links := by
  rw [links_toJR]
  rfl

theorem zetaA_eq_nodeSgn : Cancel.zetaA = ClassJR.nodeSgn := funext zetaA_eq

theorem BtJR_root (Q : RegCpl) :
    BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), []) = (toJR Q).Btilde := rfl

/-- **DH21 Proposition 5.1 for `BtJR`**, in the form of the hypotheses of wt-torus's
`Cancel.maincancel` and `Cancel.regcplcal`. -/
theorem maincoef_BtJR {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : ClassJR.A1 ≤ A) (Q : RegCpl) (hQ : Q.wf = true) :
    ClassJR.MCExp θ a b A (ClassJR.C0 θ a b ^ (2 * Q.size + 1)) Cancel.zetaA (chosenSet Q.links)
      (BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), [])) := by
  have h := ClassJR.RegCpl.maincoef hθ0 hθ1 ha hb hab1 hab hA (toJR Q) (by rw [wf_toJR]; exact hQ)
  rw [size_toJR, chosenSet_toJR, ← zetaA_eq_nodeSgn] at h
  exact h

/-- `maincoef_BtJR` with the weights of DH23: `θ = 1 - η/8`, `a = η/4`, `b = 1 - η/2`. -/
theorem maincoef_BtJR_DH23 {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A) (Q : RegCpl)
    (hQ : Q.wf = true) :
    ClassJR.MCExp (1 - η / 8) (η / 4) (1 - η / 2) A
      (ClassJR.C0 (1 - η / 8) (η / 4) (1 - η / 2) ^ (2 * Q.size + 1)) Cancel.zetaA
      (chosenSet Q.links) (BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), [])) :=
  maincoef_BtJR (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hA Q hQ

/-- **The garden-defined `B̃_Q` is `BtJR Q root root`** (B2's links). -/
theorem cplB_eq_BtJR {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) {α : ClassJR.Addr → ℝ}
    (hα : ∀ l ∈ Q.links, LinkRel α l) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cplB G t s α = BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), []) α t s :=
  cplB_eq_Btilde hQ (by rw [links_toJR]; exact hα) ht hs

/-- **Wave B's phase integral of a decoded couple is `BtJR Q root root`** (B2's links). -/
theorem phaseIntegral_kDomain_eq_BtJR {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    (h0 : ∀ a, LG.layer a = 0) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (k : GNode LG.garden.tree → Mom d)
    (hα : ∀ l ∈ Q.links, LinkRel (alphaOmega L γ δ LG.garden k) l)
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (s₁ s₂ : ℝ) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun b => if b.1.1 = 0 then t else s) s₁) s₂ k =
      BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), []) (alphaOmega L γ δ LG.garden k) t s :=
  phaseIntegral_kDomain_eq_Btilde L γ δ LG h0 hQ k (by rw [links_toJR]; exact hα) ht hs s₁ s₂

/-- **DH21 Proposition 5.1 for regular couples through gardens**, with B2's links. `hstruct` is the
named obligation `existsUnique_regCpl_decodes` (REG-STRUCT, statement verbatim). -/
theorem maincoef_garden_B2
    (hstruct : ∀ G : Garden 2, IsRegularCouple G → ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G)
    {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b) (hab1 : a + b < 1)
    (hab : a + b ≤ θ) (hA : ClassJR.A1 ≤ A) (G : Garden 2) (hG : IsRegularCouple G) :
    ∃! Q : RegCpl, (Q.wf = true ∧ Q.Decodes G) ∧
      (∀ α : ClassJR.Addr → ℝ, (∀ l ∈ Q.links, LinkRel α l) → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
        cplB G t s α = BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), []) α t s) ∧
      ClassJR.MCExp θ a b A (ClassJR.C0 θ a b ^ (2 * Q.size + 1)) Cancel.zetaA (chosenSet Q.links)
        (BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), [])) := by
  obtain ⟨Q, hQ, huniq⟩ := hstruct G hG
  exact ⟨Q, ⟨hQ, fun α hα t s ht hs => cplB_eq_BtJR hQ.2 hα ht hs,
    maincoef_BtJR hθ0 hθ1 ha hb hab1 hab hA Q hQ.1⟩, fun Q' hQ' => huniq Q' hQ'.1⟩

/-! ### The link relation with the garden's signs -/

/-- **The link relation** `ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫` with the signs of the garden `G`. -/
def LinkRelG {w : ℕ} (G : Garden w) (α : Fin w × TTree.Path → ℝ)
    (l : (Fin w × TTree.Path) × (Fin w × TTree.Path)) : Prop :=
  (((nodeSign G.sig l.2 : ℤˣ) : ℤ) : ℝ) * α l.2 = -((((nodeSign G.sig l.1 : ℤˣ) : ℤ) : ℝ) * α l.1)

theorem linkRelG_iff_couple {G : Garden 2} (hG : G.sig = ![1, -1]) (α : ClassJR.Addr → ℝ)
    (l : ClassJR.Addr × ClassJR.Addr) : LinkRelG G α l ↔ LinkRel α l := by
  simp only [LinkRelG, LinkRel, hG, nodeSign_couple_eq]

/-- **The garden-defined `B̃_Q` is `BtJR Q root root`**, with the garden's signs on B2's links. -/
theorem cplB_eq_BtJR_G {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) {α : ClassJR.Addr → ℝ}
    (hα : ∀ l ∈ Q.links, LinkRelG G α l) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cplB G t s α = BtJR Q ((0 : Fin 2), []) ((1 : Fin 2), []) α t s :=
  cplB_eq_BtJR hQ (fun l hl => (linkRelG_iff_couple hQ.1.2 α l).1 (hα l hl)) ht hs

mutual
/-- Links do not depend on the tree indices of the roots. -/
theorem linksAt_reroot {w w' : ℕ} (g : Fin w → Fin w') : ∀ (Q : RegCpl) (a b : Fin w × TTree.Path),
    Q.linksAt ((g a.1, a.2) : Fin w' × TTree.Path) (g b.1, b.2) =
      (Q.linksAt a b).map fun l => ((g l.1.1, l.1.2), (g l.2.1, l.2.2))
  | .triv, _, _ => rfl
  | .type1 _ Q₁ Q₂ Q₃, _, _ => by
    simp only [RegCpl.linksAt, List.map_cons, List.map_append, ← linksAt_reroot g Q₁,
      ← linksAt_reroot g Q₂, ← linksAt_reroot g Q₃]
    rfl
  | .type2 Xp Xm Qlp, _, _ => by
    simp only [RegCpl.linksAt, List.map_append, ← linksAt_reroot_c g Xp, ← linksAt_reroot_c g Xm,
      ← linksAt_reroot g Qlp]
    rfl

theorem linksAt_reroot_c {w w' : ℕ} (g : Fin w → Fin w') : ∀ (X : RegChain) (ζ : ℤˣ)
    (a : Fin w × TTree.Path), X.linksAt ζ ((g a.1, a.2) : Fin w' × TTree.Path) =
      (X.linksAt ζ a).map fun l => ((g l.1.1, l.1.2), (g l.2.1, l.2.2))
  | .nil, _, _ => rfl
  | .pair _ Qr Qg inner rest, _, _ => by
    simp only [RegChain.linksAt, List.map_cons, List.map_append]
    split_ifs <;>
      simp only [← linksAt_reroot g Qr, ← linksAt_reroot g Qg, ← linksAt_reroot_c g inner,
        ← linksAt_reroot_c g rest] <;> rfl
end

/-- The chain links in the couple addresses are B2's tree links, moved to the root `rootT ζ`. -/
theorem linksAt_rootT (X : RegChain) (ζ : ℤˣ) :
    (toJRc X).linksAt ζ (rootT ζ) = (X.treeLinks ζ).map fun l =>
      (((rootT ζ).1, l.1.2), ((rootT ζ).1, l.2.2)) := by
  rw [linksAt_toJRc, RegChain.treeLinks,
    ← linksAt_reroot_c (fun _ : Fin 1 => (rootT ζ).1) X ζ ((0 : Fin 1), [])]
  rfl

theorem linkRelG_iff_tree (G : Garden 1) (α : Fin 1 × TTree.Path → ℝ)
    (l : (Fin 1 × TTree.Path) × (Fin 1 × TTree.Path)) :
    LinkRelG G α l ↔
      LinkRel (liftT α) (((rootT (G.sig 0)).1, l.1.2), ((rootT (G.sig 0)).1, l.2.2)) := by
  have e : ∀ p : TTree.Path, ClassJR.nodeSgn ((rootT (G.sig 0)).1, p) =
      ((nodeSign G.sig ((0 : Fin 1), p) : ℤˣ) : ℤ) := fun p => by
    have := nodeSgn_rootT_ext (G.sig 0) p
    simpa [ClassJR.addrExt, rootT, nodeSign] using this
  obtain ⟨⟨j₁, p₁⟩, ⟨j₂, p₂⟩⟩ := l
  obtain rfl := fin_one_eq_zero' j₁
  obtain rfl := fin_one_eq_zero' j₂
  simp only [LinkRelG, LinkRel, e, liftT]

/-- **The garden-defined `𝒜*_𝒯` is the code-defined `Ã_𝒯`**, with the garden's signs on B2's tree
links. -/
theorem treeAstar_eq_Atilde_G {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {α : Fin 1 × TTree.Path → ℝ} (hα : ∀ l ∈ X.treeLinks (G.sig 0), LinkRelG G α l)
    {t s : ℝ} (ht : 0 ≤ t) (hst : s < t) :
    treeAstar G t s α = chainAtilde X (G.sig 0) (liftT α) t s := by
  refine treeAstar_eq_Atilde hX (fun l hl => ?_) ht hst
  rw [linksAt_rootT, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  exact (linkRelG_iff_tree G α l').1 (hα l' hl')

end WaveTurbulence.MainCoef

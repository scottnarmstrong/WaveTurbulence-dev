/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.TVine.Core.Bridge
/-! # H-TV (1): T-vines are invariant under relabelings that keep the bond counts (packet L6-HTV)

PLAN-L6 §3e, item H-TV (1). If `φ` is injective on `S`, `S' = φ '' S`, `M'.bondsBetween (φ u) (φ v) =
M.bondsBetween u v` for `u v ∈ S`, and `M'.IsBlock S' (φ a) (φ b)`, then `M.IsTVine S a b → M'.IsTVine S' (φ a) (φ b)`
(`isTVine_map`). The pinned `Molecule.IsTVine` (D11, `TVine/Defs.lean`) depends on `(M, S)` only through the block
predicate and the undirected multigraph of `S` (L1's `TVine.Core.isTVine_iff`, B0); the bond counts determine that
multigraph, and the closure, the (Y2) steps and the doubled triangle `T` map along `φ` (`relabel`).

Variants: the hypothesis on bond counts in the form `M'.groupBonds S' = (M.groupBonds S).map (Sym2.map φ)` (the form
proved by main's transports, `isTVine_map_of_groupBonds`), and the same-atom-type form
`isTVine_iff_of_groupBonds_eq`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.TV
open Finset TVine TVine.Core

section relabel
variable {V V' : Type*} [DecidableEq V] [DecidableEq V'] (φ : V → V') (ψ : V' → V)

/-- The image of the multigraph `G` along `φ`: vertices `φ '' verts`; a pair of image vertices has the multiplicity of
its `ψ`-image (`ψ` a left inverse of `φ` on the vertices, `relabel_mult_map`), every other pair multiplicity `0`. -/
def relabel (G : UMultigraph V) : UMultigraph V' where
  verts := G.verts.image φ
  mult e := if e ∈ (G.verts.image φ).sym2 then G.mult (Sym2.map ψ e) else 0
  supp e he x hx := by
    by_cases h : e ∈ (G.verts.image φ).sym2
    · exact Finset.mem_sym2_iff.mp h x hx
    · simp [h] at he

theorem relabel_verts (G : UMultigraph V) : (relabel φ ψ G).verts = G.verts.image φ := rfl

theorem relabel_mult (G : UMultigraph V) (e : Sym2 V') :
    (relabel φ ψ G).mult e = if e ∈ (G.verts.image φ).sym2 then G.mult (Sym2.map ψ e) else 0 := rfl

variable {φ ψ} {S : Finset V}

theorem inj_of_leftInv (hψ : ∀ x ∈ S, ψ (φ x) = x) {x y : V} (hx : x ∈ S) (hy : y ∈ S) (h : φ x = φ y) :
    x = y := by
  rw [← hψ x hx, ← hψ y hy, h]

theorem map_map_of_leftInv (hψ : ∀ x ∈ S, ψ (φ x) = x) {e : Sym2 V} (he : ∀ x ∈ e, x ∈ S) :
    Sym2.map ψ (Sym2.map φ e) = e := by
  induction e using Sym2.ind with
  | h u v =>
    rw [Sym2.map_mk, Sym2.map_mk, hψ u (he u (Sym2.mem_mk_left u v)), hψ v (he v (Sym2.mem_mk_right u v))]

theorem map_mem_sym2 {e : Sym2 V} (he : ∀ x ∈ e, x ∈ S) : Sym2.map φ e ∈ (S.image φ).sym2 := by
  refine Finset.mem_sym2_iff.mpr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hy
  exact mem_image_of_mem φ (he x hx)

theorem map_inj_of_leftInv (hψ : ∀ x ∈ S, ψ (φ x) = x) {e₁ e₂ : Sym2 V} (h₁ : ∀ x ∈ e₁, x ∈ S)
    (h₂ : ∀ x ∈ e₂, x ∈ S) : Sym2.map φ e₁ = Sym2.map φ e₂ ↔ e₁ = e₂ :=
  ⟨fun h => by rw [← map_map_of_leftInv hψ h₁, h, map_map_of_leftInv hψ h₂], fun h => h ▸ rfl⟩

theorem mem_map_iff_of_leftInv (hψ : ∀ x ∈ S, ψ (φ x) = x) {a : V} (ha : a ∈ S) {e : Sym2 V}
    (he : ∀ x ∈ e, x ∈ S) : φ a ∈ Sym2.map φ e ↔ a ∈ e := by
  refine ⟨fun h => ?_, fun h => Sym2.mem_map.mpr ⟨a, h, rfl⟩⟩
  obtain ⟨x, hx, hxa⟩ := Sym2.mem_map.mp h
  rwa [inj_of_leftInv hψ (he x hx) ha hxa] at hx

theorem pair_mem {u v : V} (hu : u ∈ S) (hv : v ∈ S) : ∀ x ∈ s(u, v), x ∈ S := by
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact hu
  · exact hv

/-- The multiplicity of the image of a pair of `S` (`ψ` a left inverse of `φ` on `S ⊇ verts`). -/
theorem relabel_mult_map (hψ : ∀ x ∈ S, ψ (φ x) = x) {G : UMultigraph V} (hG : G.verts ⊆ S) {e : Sym2 V}
    (he : ∀ x ∈ e, x ∈ S) : (relabel φ ψ G).mult (Sym2.map φ e) = G.mult e := by
  rw [relabel_mult]
  by_cases h : ∀ x ∈ e, x ∈ G.verts
  · rw [ite_eq_left (map_mem_sym2 h), map_map_of_leftInv hψ he]
  · push Not at h
    obtain ⟨x, hx, hxG⟩ := h
    rw [ite_eq_right]
    · by_contra hne
      exact hxG (G.supp e (Ne.symm hne) x hx)
    · intro hm
      obtain ⟨y, hy, hyx⟩ := mem_image.mp (Finset.mem_sym2_iff.mp hm (φ x) (Sym2.mem_map.mpr ⟨x, hx, rfl⟩))
      exact hxG (inj_of_leftInv hψ (hG hy) (he x hx) hyx ▸ hy)

theorem relabel_mult_of_not_mem {G : UMultigraph V} {e : Sym2 V'} (h : e ∉ (G.verts.image φ).sym2) :
    (relabel φ ψ G).mult e = 0 :=
  ite_eq_right h

/-- Every pair of `V'` is the image of a pair of vertices, or not a pair of image vertices. -/
theorem relabel_cases (G : UMultigraph V) (e' : Sym2 V') :
    (∃ e : Sym2 V, (∀ x ∈ e, x ∈ G.verts) ∧ Sym2.map φ e = e') ∨ e' ∉ (G.verts.image φ).sym2 := by
  by_cases h : e' ∈ (G.verts.image φ).sym2
  · left
    induction e' using Sym2.ind with
    | h u' v' =>
      obtain ⟨u, hu, rfl⟩ := mem_image.mp (Finset.mem_sym2_iff.mp h u' (Sym2.mem_mk_left _ _))
      obtain ⟨v, hv, rfl⟩ := mem_image.mp (Finset.mem_sym2_iff.mp h v' (Sym2.mem_mk_right _ _))
      exact ⟨s(u, v), pair_mem hu hv, rfl⟩
  · exact Or.inr h

theorem relabel_mult_of_not_mem_sub {G H : UMultigraph V} (hHG : H.verts ⊆ G.verts) {e : Sym2 V'}
    (h : e ∉ (G.verts.image φ).sym2) : (relabel φ ψ H).mult e = 0 :=
  relabel_mult_of_not_mem fun hm => h (Finset.mem_sym2_iff.mpr fun x hx =>
    image_subset_image hHG (Finset.mem_sym2_iff.mp hm x hx))

theorem erase_image (hψ : ∀ x ∈ S, ψ (φ x) = x) {T : Finset V} (hT : T ⊆ S) {a b : V} (ha : a ∈ S)
    (hb : b ∈ S) : ((T.erase a).erase b).image φ = ((T.image φ).erase (φ a)).erase (φ b) := by
  ext y
  simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨x, ⟨hxb, hxa, hx⟩, rfl⟩
    exact ⟨fun h => hxb (inj_of_leftInv hψ (hT hx) hb h), fun h => hxa (inj_of_leftInv hψ (hT hx) ha h), x, hx,
      rfl⟩
  · rintro ⟨hyb, hya, x, hx, rfl⟩
    exact ⟨x, ⟨fun h => hyb (h ▸ rfl), fun h => hya (h ▸ rfl), hx⟩, rfl⟩

theorem count_map_of_leftInv (hψ : ∀ x ∈ S, ψ (φ x) = x) {m : Multiset (Sym2 V)}
    (hm : ∀ f ∈ m, ∀ x ∈ f, x ∈ S) {e : Sym2 V} (he : ∀ x ∈ e, x ∈ S) :
    (m.map (Sym2.map φ)).count (Sym2.map φ e) = m.count e := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun f hf => map_inj_of_leftInv hψ he (hm f hf)

theorem count_map_of_not_mem {m : Multiset (Sym2 V)} (hm : ∀ f ∈ m, ∀ x ∈ f, x ∈ S) {e' : Sym2 V'}
    (he : e' ∉ (S.image φ).sym2) : (m.map (Sym2.map φ)).count e' = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp h
  exact he (map_mem_sym2 (hm f hf))

/-! ## The (Y2) step, its reflexive-transitive closure and the doubled triangle -/

theorem verts_subset_of_y2Step {G H : UMultigraph V} (h : Y2Step G H) : H.verts ⊆ G.verts := by
  obtain ⟨a, b, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := h
  rw [hv]
  exact (erase_subset _ _).trans (erase_subset _ _)

theorem verts_subset_of_rtg {G H : UMultigraph V} (h : Relation.ReflTransGen Y2Step G H) : H.verts ⊆ G.verts := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hst ih => exact (verts_subset_of_y2Step hst).trans ih

theorem y2Step_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G H : UMultigraph V} (hG : G.verts ⊆ S) (h : Y2Step G H) :
    Y2Step (relabel φ ψ G) (relabel φ ψ H) := by
  have hHG := verts_subset_of_y2Step h
  obtain ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, h1, h1', ha0, hb0, hv, hm⟩ := h
  have hmem : ∀ {u v : V}, G.mult s(u, v) ≠ 0 → u ∈ G.verts ∧ v ∈ G.verts := fun hne =>
    ⟨G.supp _ hne _ (Sym2.mem_mk_left _ _), G.supp _ hne _ (Sym2.mem_mk_right _ _)⟩
  obtain ⟨ha, hb⟩ := hmem (u := a) (v := b) (by omega)
  obtain ⟨-, hc⟩ := hmem (u := a) (v := c) (by omega)
  obtain ⟨-, hd⟩ := hmem (u := b) (v := d) (by omega)
  have ne : ∀ {x y : V}, x ∈ G.verts → y ∈ G.verts → x ≠ y → φ x ≠ φ y := fun hx hy hxy h =>
    hxy (inj_of_leftInv hψ (hG hx) (hG hy) h)
  have key : ∀ {u v : V}, u ∈ G.verts → v ∈ G.verts → (relabel φ ψ G).mult s(φ u, φ v) = G.mult s(u, v) :=
    fun hu hv => relabel_mult_map hψ hG (pair_mem (hG hu) (hG hv))
  refine ⟨φ a, φ b, φ c, φ d, ne ha hb hab, ne hc hd hcd, ne hc ha hca, ne hc hb hcb, ne hd ha hda,
    ne hd hb hdb, (key ha hb).trans h3, (key ha hc).trans h1, (key hb hd).trans h1', ?_, ?_, ?_, ?_⟩
  · intro x hxb hxc
    by_cases hx : x ∈ G.verts.image φ
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      rw [key ha hy]
      exact ha0 y (fun h => hxb (h ▸ rfl)) (fun h => hxc (h ▸ rfl))
    · exact relabel_mult_of_not_mem fun hm => hx (Finset.mem_sym2_iff.mp hm x (Sym2.mem_mk_right _ _))
  · intro x hxa hxd
    by_cases hx : x ∈ G.verts.image φ
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      rw [key hb hy]
      exact hb0 y (fun h => hxa (h ▸ rfl)) (fun h => hxd (h ▸ rfl))
    · exact relabel_mult_of_not_mem fun hm => hx (Finset.mem_sym2_iff.mp hm x (Sym2.mem_mk_right _ _))
  · rw [relabel_verts, hv, relabel_verts]
    exact erase_image hψ hG (hG ha) (hG hb)
  · intro e'
    rcases relabel_cases (φ := φ) G e' with ⟨e, he, rfl⟩ | hne
    · have heS : ∀ x ∈ e, x ∈ S := fun x hx => hG (he x hx)
      have hA := mem_map_iff_of_leftInv hψ (hG ha) heS
      have hB := mem_map_iff_of_leftInv hψ (hG hb) heS
      have hC : Sym2.map φ e = s(φ c, φ d) ↔ e = s(c, d) :=
        map_inj_of_leftInv hψ heS (pair_mem (hG hc) (hG hd))
      rw [relabel_mult_map hψ (hHG.trans hG) heS, hm e, relabel_mult_map hψ hG heS]
      simp only [hA, hB, hC]
    · have hcd' : e' ≠ s(φ c, φ d) := by
        intro h
        apply hne
        rw [h]
        exact map_mem_sym2 (φ := φ) (pair_mem hc hd)
      rw [relabel_mult_of_not_mem_sub hHG hne, relabel_mult_of_not_mem hne, ite_eq_right hcd']
      simp

theorem rtg_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G H : UMultigraph V} (hG : G.verts ⊆ S)
    (h : Relation.ReflTransGen Y2Step G H) : Relation.ReflTransGen Y2Step (relabel φ ψ G) (relabel φ ψ H) := by
  induction h with
  | refl => exact .refl
  | tail hgh hst ih => exact ih.tail (y2Step_relabel hψ ((verts_subset_of_rtg hgh).trans hG) hst)

theorem isDoubledTriangle_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G : UMultigraph V} (hG : G.verts ⊆ S)
    (h : IsDoubledTriangle G) : IsDoubledTriangle (relabel φ ψ G) := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, hm⟩ := h
  have hav : a ∈ G.verts := by rw [hv]; simp
  have hbv : b ∈ G.verts := by rw [hv]; simp
  have hcv : c ∈ G.verts := by rw [hv]; simp
  have ha : a ∈ S := hG hav
  have hb : b ∈ S := hG hbv
  have hc : c ∈ S := hG hcv
  have ne : ∀ {x y : V}, x ∈ S → y ∈ S → x ≠ y → φ x ≠ φ y := fun hx hy hxy h =>
    hxy (inj_of_leftInv hψ hx hy h)
  refine ⟨φ a, φ b, φ c, ne ha hb hab, ne ha hc hac, ne hb hc hbc, ?_, ?_⟩
  · rw [relabel_verts, hv, image_insert, image_insert, image_singleton]
  · intro e'
    rcases relabel_cases (φ := φ) G e' with ⟨e, he, rfl⟩ | hne
    · have heS : ∀ x ∈ e, x ∈ S := fun x hx => hG (he x hx)
      have h1 : Sym2.map φ e = s(φ a, φ b) ↔ e = s(a, b) := map_inj_of_leftInv hψ heS (pair_mem ha hb)
      have h2 : Sym2.map φ e = s(φ b, φ c) ↔ e = s(b, c) := map_inj_of_leftInv hψ heS (pair_mem hb hc)
      have h3 : Sym2.map φ e = s(φ a, φ c) ↔ e = s(a, c) := map_inj_of_leftInv hψ heS (pair_mem ha hc)
      rw [relabel_mult_map hψ hG heS, hm e]
      simp only [h1, h2, h3]
    · have hGv : ∀ {x y : V}, x ∈ G.verts → y ∈ G.verts → e' ≠ s(φ x, φ y) := by
        intro x y hx hy h
        apply hne
        rw [h]
        exact map_mem_sym2 (φ := φ) (pair_mem hx hy)
      rw [relabel_mult_of_not_mem hne, ite_eq_right]
      rintro (h | h | h)
      exacts [hGv hav hbv h, hGv hbv hcv h, hGv hav hcv h]

/-! ## Neighbours, loops and the closure -/

theorem nbrs_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G : UMultigraph V} (hG : G.verts ⊆ S) {v : V}
    (hv : v ∈ G.verts) : nbrs (relabel φ ψ G) (φ v) = (nbrs G v).map φ := by
  have inj : Set.InjOn φ G.verts := fun x hx y hy h => inj_of_leftInv hψ (hG hx) (hG hy) h
  have key : ∀ w ∈ G.verts, (relabel φ ψ G).mult s(φ v, φ w) = G.mult s(v, w) := fun w hw =>
    relabel_mult_map hψ hG (pair_mem (hG hv) (hG hw))
  have hsum : (∑ w ∈ G.verts, Multiset.replicate (G.mult s(v, w)) w).map φ =
      ∑ w ∈ G.verts, Multiset.replicate (G.mult s(v, w)) (φ w) := by
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]
    exact Finset.sum_congr rfl fun w _ => Multiset.map_replicate _ _ _
  rw [nbrs, nbrs, relabel_verts, Finset.sum_image inj, Multiset.map_add, Multiset.map_replicate, key v hv, hsum]
  congr 1
  exact Finset.sum_congr rfl fun w hw => by rw [key w hw]

theorem mem_verts_of_mem_nbrs {G : UMultigraph V} {v : V} (hv : v ∈ G.verts) {x : V} (hx : x ∈ nbrs G v) :
    x ∈ G.verts := by
  rw [nbrs, Multiset.mem_add] at hx
  rcases hx with hx | hx
  · obtain ⟨w, hw, hxw⟩ := Multiset.mem_sum.mp hx
    rw [Multiset.eq_of_mem_replicate hxw]
    exact hw
  · rw [Multiset.eq_of_mem_replicate hx]
    exact hv

theorem loopless_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G : UMultigraph V} (hG : G.verts ⊆ S) (h : G.Loopless) :
    (relabel φ ψ G).Loopless := by
  intro x'
  rcases relabel_cases (φ := φ) G s(x', x') with ⟨e, he, he'⟩ | hne
  · induction e using Sym2.ind with
    | h u v =>
      have hu : u ∈ G.verts := he u (Sym2.mem_mk_left u v)
      have hv : v ∈ G.verts := he v (Sym2.mem_mk_right u v)
      have huv : u = v := by
        have h' : s(φ u, φ v) = s(x', x') := he'
        rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact inj_of_leftInv hψ (hG hu) (hG hv) (h1.trans h2.symm)
        · exact inj_of_leftInv hψ (hG hu) (hG hv) (h1.trans h2.symm)
      subst huv
      rw [← he', relabel_mult_map hψ hG (pair_mem (hG hu) (hG hu))]
      exact h u
  · exact relabel_mult_of_not_mem hne

theorem isClosureU_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G : UMultigraph V} (hG : G.verts ⊆ S) {j₁ j₂ : V}
    (h₁ : j₁ ∈ G.verts) (h₂ : j₂ ∈ G.verts) {C : UMultigraph V} (h : IsClosureU G j₁ j₂ C) :
    IsClosureU (relabel φ ψ G) (φ j₁) (φ j₂) (relabel φ ψ C) := by
  obtain ⟨hσ, hCv, hloop, added, hadd, hCm⟩ := h
  have hCG : C.verts ⊆ G.verts := by rw [hCv]; exact (erase_subset _ _).trans (erase_subset _ _)
  have hσ' : (relabel φ ψ G).mult s(φ j₁, φ j₂) = G.mult s(j₁, j₂) :=
    relabel_mult_map hψ hG (pair_mem (hG h₁) (hG h₂))
  have hn₁ := nbrs_relabel hψ hG h₁
  have hn₂ := nbrs_relabel hψ hG h₂
  have hψG : ∀ x ∈ G.verts, ψ (φ x) = x := fun x hx => hψ x (hG hx)
  have haddG : ∀ f ∈ added, ∀ x ∈ f, x ∈ G.verts := by
    have hm : ∀ {v x : V}, v ∈ G.verts → x ∈ nbrs G v → x ∈ G.verts := fun hv hx => mem_verts_of_mem_nbrs hv hx
    rcases hadd with ⟨-, a, b, c, d, hb₁, hb₂, rfl⟩ | ⟨-, x, y, hb₁, hb₂, rfl⟩
    · have ha : a ∈ G.verts := hm h₁ (by rw [hb₁]; simp)
      have hb : b ∈ G.verts := hm h₁ (by rw [hb₁]; simp)
      have hc : c ∈ G.verts := hm h₂ (by rw [hb₂]; simp)
      have hd : d ∈ G.verts := hm h₂ (by rw [hb₂]; simp)
      intro f hf
      rcases Multiset.mem_cons.mp hf with rfl | hf
      · exact pair_mem ha hb
      · rw [Multiset.mem_singleton.mp hf]; exact pair_mem hc hd
    · have hx : x ∈ G.verts := hm h₁ (by rw [hb₁]; simp)
      have hy : y ∈ G.verts := hm h₂ (by rw [hb₂]; simp)
      intro f hf
      rw [Multiset.mem_singleton.mp hf]; exact pair_mem hx hy
  refine ⟨hσ'.symm ▸ hσ, ?_, loopless_relabel hψ (hCG.trans hG) hloop, added.map (Sym2.map φ), ?_, ?_⟩
  · rw [relabel_verts, hCv, relabel_verts]
    exact erase_image hψ hG (hG h₁) (hG h₂)
  · rcases hadd with ⟨h0, a, b, c, d, hb₁, hb₂, rfl⟩ | ⟨h1, x, y, hb₁, hb₂, rfl⟩
    · refine Or.inl ⟨hσ'.trans h0, φ a, φ b, φ c, φ d, ?_, ?_, ?_⟩
      · rw [hn₁, hb₁]; simp
      · rw [hn₂, hb₂]; simp
      · simp
    · refine Or.inr ⟨hσ'.trans h1, φ x, φ y, ?_, ?_, ?_⟩
      · rw [hn₁, hb₁]; simp
      · rw [hn₂, hb₂]; simp
      · simp
  · intro e'
    rcases relabel_cases (φ := φ) G e' with ⟨e, he, rfl⟩ | hne
    · have heS : ∀ x ∈ e, x ∈ S := fun x hx => hG (he x hx)
      have hA := mem_map_iff_of_leftInv hψ (hG h₁) heS
      have hB := mem_map_iff_of_leftInv hψ (hG h₂) heS
      rw [relabel_mult_map hψ (hCG.trans hG) heS, hCm e, relabel_mult_map hψ hG heS,
        count_map_of_leftInv hψG haddG he]
      simp only [hA, hB]
    · rw [relabel_mult_of_not_mem_sub hCG hne, relabel_mult_of_not_mem hne, count_map_of_not_mem haddG hne]
      simp

/-- **The U-level invariance**: the T-vine property of a multigraph passes to its relabeling, given the block
property of the relabeling. -/
theorem isTVineU_relabel (hψ : ∀ x ∈ S, ψ (φ x) = x) {G : UMultigraph V} (hG : G.verts ⊆ S) {j₁ j₂ : V}
    (hBU : IsBlockU (relabel φ ψ G) (φ j₁) (φ j₂)) (h : IsTVineU G j₁ j₂) :
    IsTVineU (relabel φ ψ G) (φ j₁) (φ j₂) := by
  obtain ⟨hB, hm, C, hC, C', hr, hT⟩ := h
  have hCG : C.verts ⊆ G.verts := by rw [hC.2.1]; exact (erase_subset _ _).trans (erase_subset _ _)
  refine ⟨hBU, ?_, relabel φ ψ C, isClosureU_relabel hψ hG hB.1 hB.2.1 hC, relabel φ ψ C',
    rtg_relabel hψ (hCG.trans hG) hr, isDoubledTriangle_relabel hψ (((verts_subset_of_rtg hr).trans hCG).trans hG) hT⟩
  intro u' hu' v' hv' huv
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hu'
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hv'
  have hk : (relabel φ ψ G).mult s(φ u, φ v) = G.mult s(u, v) := relabel_mult_map hψ hG (pair_mem (hG hu) (hG hv))
  rw [hk]
  exact hm u hu v hv fun h => huv (h ▸ rfl)

end relabel

/-! ## Molecules -/

section molecule
variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [DecidableEq V'] [Fintype D']
  [DecidableEq D']

theorem mem_of_mem_groupBonds {M : Molecule V D} {S : Finset V} {f : Sym2 V} (hf : f ∈ M.groupBonds S) :
    ∀ x ∈ f, x ∈ S := fun x hx =>
  (groupGraph M S).supp f (by rw [groupGraph_mult]; exact Multiset.count_ne_zero.mpr hf) x hx

/-- The multigraph of the group `φ '' S` of `M'` is the relabeling of that of `S`, when `φ` keeps the bond counts. -/
theorem groupGraph_eq_relabel {M : Molecule V D} {M' : Molecule V' D'} {S : Finset V} {φ : V → V'}
    {ψ : V' → V} (hψ : ∀ x ∈ S, ψ (φ x) = x)
    (hbb : ∀ u ∈ S, ∀ v ∈ S, M'.bondsBetween (φ u) (φ v) = M.bondsBetween u v) :
    groupGraph M' (S.image φ) = relabel φ ψ (groupGraph M S) := by
  refine TVine.Core.ext rfl fun e' => ?_
  rcases relabel_cases (φ := φ) (groupGraph M S) e' with ⟨e, he, rfl⟩ | hne
  · induction e using Sym2.ind with
    | h u v =>
      have hu : u ∈ S := he u (Sym2.mem_mk_left u v)
      have hv : v ∈ S := he v (Sym2.mem_mk_right u v)
      rw [relabel_mult_map hψ subset_rfl he]
      change (groupGraph M' (S.image φ)).mult s(φ u, φ v) = (groupGraph M S).mult s(u, v)
      rw [← bondsBetween_eq M' (mem_image_of_mem φ hu) (mem_image_of_mem φ hv), ← bondsBetween_eq M hu hv,
        hbb u hu v hv]
  · rw [relabel_mult_of_not_mem hne]
    by_contra h0
    exact hne (Finset.mem_sym2_iff.mpr fun x hx => (groupGraph M' (S.image φ)).supp e' h0 x hx)

/-- **General invariance of T-vines** (PLAN-L6 §3e, H-TV (1)). If `φ` is injective on `S`, `S' = φ '' S`, `φ` keeps
the bond counts between atoms of `S`, and `S'` is a block of `M'` with joints `φ a, φ b`, then a T-vine `S` of `M`
with joints `a, b` maps to a T-vine `S'` of `M'` with joints `φ a, φ b`. -/
theorem isTVine_map {M : Molecule V D} {M' : Molecule V' D'} {S : Finset V} {S' : Finset V'} {φ : V → V'}
    {a b : V} (hφ : Set.InjOn φ S) (hS' : S' = S.image φ)
    (hbb : ∀ u ∈ S, ∀ v ∈ S, M'.bondsBetween (φ u) (φ v) = M.bondsBetween u v)
    (hB : M'.IsBlock S' (φ a) (φ b)) (hT : M.IsTVine S a b) : M'.IsTVine S' (φ a) (φ b) := by
  subst hS'
  have : Nonempty V := ⟨a⟩
  have hψ : ∀ x ∈ S, Function.invFunOn φ (S : Set V) (φ x) = x := fun x hx => hφ.leftInvOn_invFunOn hx
  rw [isTVine_iff] at hT ⊢
  refine ⟨hB, ?_⟩
  have hBU := isBlockU_of_isBlock M' hB
  rw [groupGraph_eq_relabel hψ hbb] at hBU ⊢
  exact isTVineU_relabel hψ subset_rfl hBU hT.2

/-- Bond counts are kept when the bond multiset of the group is the image of the old one. -/
theorem bondsBetween_of_groupBonds_map {M : Molecule V D} {M' : Molecule V' D'} {S : Finset V} {S' : Finset V'}
    {φ : V → V'} (hφ : Set.InjOn φ S) (hS' : S' = S.image φ)
    (hg : M'.groupBonds S' = (M.groupBonds S).map (Sym2.map φ)) :
    ∀ u ∈ S, ∀ v ∈ S, M'.bondsBetween (φ u) (φ v) = M.bondsBetween u v := by
  intro u hu v hv
  subst hS'
  have : Nonempty V := ⟨u⟩
  have hψ : ∀ x ∈ S, Function.invFunOn φ (S : Set V) (φ x) = x := fun x hx => hφ.leftInvOn_invFunOn hx
  rw [bondsBetween_eq M' (mem_image_of_mem φ hu) (mem_image_of_mem φ hv), bondsBetween_eq M hu hv, groupGraph_mult,
    groupGraph_mult, hg]
  exact count_map_of_leftInv hψ (fun f hf => mem_of_mem_groupBonds hf) (pair_mem hu hv)

/-- `isTVine_map` with the bond counts given as the image of the bond multiset (the form of main's transports). -/
theorem isTVine_map_of_groupBonds {M : Molecule V D} {M' : Molecule V' D'} {S : Finset V} {S' : Finset V'}
    {φ : V → V'} {a b : V} (hφ : Set.InjOn φ S) (hS' : S' = S.image φ)
    (hg : M'.groupBonds S' = (M.groupBonds S).map (Sym2.map φ))
    (hB : M'.IsBlock S' (φ a) (φ b)) (hT : M.IsTVine S a b) : M'.IsTVine S' (φ a) (φ b) :=
  isTVine_map hφ hS' (bondsBetween_of_groupBonds_map hφ hS' hg) hB hT

/-- Two molecules on the same atoms with the same bond multiset on `S` and the same block property have the same
T-vines on `S`. -/
theorem isTVine_iff_of_groupBonds_eq {M : Molecule V D} {N : Molecule V D'} {S : Finset V} {a b : V}
    (hg : N.groupBonds S = M.groupBonds S) (hblk : N.IsBlock S a b ↔ M.IsBlock S a b) :
    N.IsTVine S a b ↔ M.IsTVine S a b := by
  have hG : groupGraph N S = groupGraph M S :=
    TVine.Core.ext rfl fun e => by rw [groupGraph_mult, groupGraph_mult, hg]
  rw [isTVine_iff, isTVine_iff, hblk, hG]

end molecule

end WaveTurbulence.GammaLow.FinalCount.H.TV

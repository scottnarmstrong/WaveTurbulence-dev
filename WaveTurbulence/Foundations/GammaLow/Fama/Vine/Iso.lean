/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Local
import Mathlib.Tactic
/-! # T-vines are invariant under isomorphisms of induced subgraphs (packet L5a, item D)

Proof of `TVineIsoInvariant` (`Vine/IsoStmt.lean`): along main's `RedSplice.InducedIso I : M[B] ≅ M'[B']` the block
structure is transported by `I.isBlock` (main); the bond multiplicities inside `B` by `I.groupBonds_map`; the closure,
the (Y2) moves and the doubled triangle by the push-forward `umap I.π` of multigraphs, which is faithful because `I.π`
is injective on `B` and every multigraph involved lives on a subset of `B`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open Finset

section UMap
variable {V V' : Type*} [DecidableEq V] [DecidableEq V']

theorem sym2_map_injOn {π : V → V'} {s : Finset V} (h : Set.InjOn π s) {e₁ e₂ : Sym2 V}
    (h₁ : e₁ ∈ s.sym2) (h₂ : e₂ ∈ s.sym2) (he : Sym2.map π e₁ = Sym2.map π e₂) : e₁ = e₂ := by
  induction e₁ using Sym2.ind with
  | h a b =>
    induction e₂ using Sym2.ind with
    | h c d =>
      rw [Finset.mk_mem_sym2_iff] at h₁ h₂
      simp only [Sym2.map_mk, Sym2.eq_iff] at he ⊢
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h h₁.1 h₂.1 h1, h h₁.2 h₂.2 h2⟩
      · exact Or.inr ⟨h h₁.1 h₂.2 h1, h h₁.2 h₂.1 h2⟩

theorem mem_map_iff_injOn {π : V → V'} {s : Finset V} (h : Set.InjOn π s) {e : Sym2 V} (he : e ∈ s.sym2)
    {a : V} (ha : a ∈ s) : π a ∈ Sym2.map π e ↔ a ∈ e := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hya⟩
    rw [h ha (Finset.mem_sym2_iff.mp he y hy) hya.symm]
    exact hy
  · intro hae
    exact ⟨a, hae, rfl⟩

theorem image_erase_injOn {π : V → V'} {s : Finset V} (h : Set.InjOn π s) {x : V} (hx : x ∈ s) :
    (s.erase x).image π = (s.image π).erase (π x) := by
  ext y
  simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨z, ⟨hzx, hz⟩, rfl⟩
    exact ⟨fun he => hzx (h hz hx he), z, hz, rfl⟩
  · rintro ⟨hy, z, hz, rfl⟩
    exact ⟨z, ⟨fun he => hy (he ▸ rfl), hz⟩, rfl⟩

open Classical in
/-- The multiplicity function of the push-forward `umap π G`. -/
noncomputable def umapMult (π : V → V') (G : TVine.UMultigraph V) (e' : Sym2 V') : ℕ :=
  if h : ∃ e ∈ G.verts.sym2, Sym2.map π e = e' then G.mult h.choose else 0

theorem umapMult_supp (π : V → V') (G : TVine.UMultigraph V) (e' : Sym2 V') (hne : umapMult π G e' ≠ 0) :
    ∀ x ∈ e', x ∈ G.verts.image π := by
  intro x hx
  unfold umapMult at hne
  by_cases h : ∃ e ∈ G.verts.sym2, Sym2.map π e = e'
  · obtain ⟨he, hmap⟩ := h.choose_spec
    rw [← hmap, Sym2.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact mem_image_of_mem π (Finset.mem_sym2_iff.mp he y hy)
  · rw [dif_neg h] at hne
    exact absurd rfl hne

/-- The push-forward of a multigraph along a map (faithful where the map is injective on the vertices). -/
noncomputable def umap (π : V → V') (G : TVine.UMultigraph V) : TVine.UMultigraph V' where
  verts := G.verts.image π
  mult := umapMult π G
  supp := umapMult_supp π G

variable {π : V → V'} {G : TVine.UMultigraph V}

theorem mult_eq_zero_of_not_mem_sym2 {e : Sym2 V} (he : e ∉ G.verts.sym2) : G.mult e = 0 := by
  by_contra hne
  exact he (Finset.mem_sym2_iff.mpr fun x hx => G.supp e hne x hx)

theorem umap_mult_map (h : Set.InjOn π G.verts) {e : Sym2 V} (he : e ∈ G.verts.sym2) :
    (umap π G).mult (Sym2.map π e) = G.mult e := by
  have hex : ∃ e₀ ∈ G.verts.sym2, Sym2.map π e₀ = Sym2.map π e := ⟨e, he, rfl⟩
  change umapMult π G (Sym2.map π e) = _
  unfold umapMult
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  rw [sym2_map_injOn h h1 he h2]

theorem umap_mult_eq_zero {e' : Sym2 V'} (hne : ∀ e ∈ G.verts.sym2, Sym2.map π e ≠ e') :
    (umap π G).mult e' = 0 := by
  change umapMult π G e' = _
  unfold umapMult
  rw [dif_neg]
  rintro ⟨e, he, hmap⟩
  exact hne e he hmap

theorem umap_mult_map_of_subset {H : TVine.UMultigraph V} (h : Set.InjOn π G.verts) (hsub : H.verts ⊆ G.verts)
    {e : Sym2 V} (he : e ∈ G.verts.sym2) (heH : e ∉ H.verts.sym2) : (umap π H).mult (Sym2.map π e) = 0 :=
  umap_mult_eq_zero fun e₀ he₀ hmap =>
    heH (sym2_map_injOn h (Finset.sym2_mono hsub he₀) he hmap ▸ he₀)

theorem y2Step_verts_subset {G H : TVine.UMultigraph V} (h : TVine.Y2Step G H) : H.verts ⊆ G.verts := by
  obtain ⟨a, b, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := h
  rw [hv]
  exact (erase_subset _ _).trans (erase_subset _ _)

theorem rtg_verts_subset {G H : TVine.UMultigraph V} (h : Relation.ReflTransGen TVine.Y2Step G H) :
    H.verts ⊆ G.verts := by
  induction h with
  | refl => exact subset_refl _
  | tail _ hs ih => exact (y2Step_verts_subset hs).trans ih

theorem mem_verts_of_mult_ne_zero {G : TVine.UMultigraph V} {x y : V} (h : G.mult s(x, y) ≠ 0) :
    x ∈ G.verts ∧ y ∈ G.verts :=
  ⟨G.supp _ h x (Sym2.mem_mk_left x y), G.supp _ h y (Sym2.mem_mk_right x y)⟩

/-- The vertices adjacent in the image come from the image of the vertices. -/
theorem umap_mult_pair_zero (h : Set.InjOn π G.verts) {u : V} (hu : u ∈ G.verts) {x' : V'}
    (hz : ∀ x ∈ G.verts, π x = x' → G.mult s(u, x) = 0) : (umap π G).mult s(π u, x') = 0 := by
  by_cases hx : ∃ x ∈ G.verts, π x = x'
  · obtain ⟨x, hxv, rfl⟩ := hx
    have hmem : s(u, x) ∈ G.verts.sym2 := Finset.mk_mem_sym2_iff.mpr ⟨hu, hxv⟩
    rw [show s(π u, π x) = Sym2.map π s(u, x) from (Sym2.map_mk π u x).symm, umap_mult_map h hmem]
    exact hz x hxv rfl
  · apply umap_mult_eq_zero
    intro e he hmap
    apply hx
    have : x' ∈ Sym2.map π e := hmap ▸ Sym2.mem_mk_right _ _
    obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp this
    exact ⟨y, Finset.mem_sym2_iff.mp he y hy, hyx⟩

theorem y2Step_umap {H : TVine.UMultigraph V} (hinj : Set.InjOn π G.verts) (h : TVine.Y2Step G H) :
    TVine.Y2Step (umap π G) (umap π H) := by
  classical
  have hsub := y2Step_verts_subset h
  obtain ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hac, hbd, ha0, hb0, hv, hm⟩ := h
  have hab' := mem_verts_of_mult_ne_zero (G := G) (x := a) (y := b) (by rw [h3]; norm_num)
  have hac' := mem_verts_of_mult_ne_zero (G := G) (x := a) (y := c) (by rw [hac]; norm_num)
  have hbd' := mem_verts_of_mult_ne_zero (G := G) (x := b) (y := d) (by rw [hbd]; norm_num)
  have hne : ∀ {x y : V}, x ∈ G.verts → y ∈ G.verts → x ≠ y → π x ≠ π y :=
    fun hx hy hxy he => hxy (hinj hx hy he)
  have hmap2 : ∀ {x y : V}, x ∈ G.verts → y ∈ G.verts → (umap π G).mult s(π x, π y) = G.mult s(x, y) := by
    intro x y hx hy
    rw [show s(π x, π y) = Sym2.map π s(x, y) from (Sym2.map_mk π x y).symm]
    exact umap_mult_map hinj (Finset.mk_mem_sym2_iff.mpr ⟨hx, hy⟩)
  refine ⟨π a, π b, π c, π d, hne hab'.1 hab'.2 hab, hne hac'.2 hbd'.2 hcd, hne hac'.2 hab'.1 hca,
    hne hac'.2 hab'.2 hcb, hne hbd'.2 hab'.1 hda, hne hbd'.2 hab'.2 hdb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap2 hab'.1 hab'.2, h3]
  · rw [hmap2 hac'.1 hac'.2, hac]
  · rw [hmap2 hbd'.1 hbd'.2, hbd]
  · intro x' hxb hxc
    exact umap_mult_pair_zero hinj hab'.1 fun x _ hx => ha0 x (fun he => hxb (he ▸ hx.symm))
      (fun he => hxc (he ▸ hx.symm))
  · intro x' hxa hxd
    exact umap_mult_pair_zero hinj hab'.2 fun x _ hx => hb0 x (fun he => hxa (he ▸ hx.symm))
      (fun he => hxd (he ▸ hx.symm))
  · change H.verts.image π = ((G.verts.image π).erase (π a)).erase (π b)
    rw [hv, image_erase_injOn (hinj.mono (erase_subset _ _)) (mem_erase.mpr ⟨fun he => hab he.symm, hab'.2⟩),
      image_erase_injOn hinj hab'.1]
  · intro e'
    have hcd2 : s(c, d) ∈ G.verts.sym2 := Finset.mk_mem_sym2_iff.mpr ⟨hac'.2, hbd'.2⟩
    by_cases hex : ∃ e ∈ G.verts.sym2, Sym2.map π e = e'
    · obtain ⟨e, he, rfl⟩ := hex
      have hia : π a ∈ Sym2.map π e ↔ a ∈ e := mem_map_iff_injOn hinj he hab'.1
      have hib : π b ∈ Sym2.map π e ↔ b ∈ e := mem_map_iff_injOn hinj he hab'.2
      have hicd : Sym2.map π e = s(π c, π d) ↔ e = s(c, d) := by
        rw [show s(π c, π d) = Sym2.map π s(c, d) from (Sym2.map_mk π c d).symm]
        exact ⟨fun h => sym2_map_injOn hinj he hcd2 h, fun h => h ▸ rfl⟩
      rw [umap_mult_map hinj he]
      by_cases hin : a ∈ e ∨ b ∈ e
      · rw [if_pos (by rwa [hia, hib])]
        apply umap_mult_map_of_subset hinj hsub he
        intro heH
        rw [hv] at heH
        rcases hin with hin | hin
        · exact (mem_erase.mp (mem_erase.mp (Finset.mem_sym2_iff.mp heH a hin)).2).1 rfl
        · exact (mem_erase.mp (Finset.mem_sym2_iff.mp heH b hin)).1 rfl
      · rw [if_neg (by rwa [hia, hib])]
        have heH : e ∈ H.verts.sym2 := by
          rw [hv]
          refine Finset.mem_sym2_iff.mpr fun x hx => ?_
          refine mem_erase.mpr ⟨fun hxb => hin (Or.inr (hxb ▸ hx)), mem_erase.mpr
            ⟨fun hxa => hin (Or.inl (hxa ▸ hx)), Finset.mem_sym2_iff.mp he x hx⟩⟩
        rw [umap_mult_map (hinj.mono hsub) heH, hm e, if_neg hin]
        simp only [hicd]
    · have hz : (umap π H).mult e' = 0 :=
        umap_mult_eq_zero fun e₀ he₀ hmap => hex ⟨e₀, Finset.sym2_mono hsub he₀, hmap⟩
      have hz' : (umap π G).mult e' = 0 := umap_mult_eq_zero fun e₀ he₀ hmap => hex ⟨e₀, he₀, hmap⟩
      have hcd' : e' ≠ s(π c, π d) := fun he => hex ⟨s(c, d), hcd2, by rw [he, Sym2.map_mk]⟩
      rw [hz, hz', if_neg hcd']
      simp

theorem rtg_umap {H : TVine.UMultigraph V} (hinj : Set.InjOn π G.verts)
    (h : Relation.ReflTransGen TVine.Y2Step G H) : Relation.ReflTransGen TVine.Y2Step (umap π G) (umap π H) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail K L hGK hKL ih =>
    exact Relation.ReflTransGen.tail ih (y2Step_umap (hinj.mono (rtg_verts_subset hGK)) hKL)

theorem doubledTriangle_umap (hinj : Set.InjOn π G.verts) (h : TVine.IsDoubledTriangle G) :
    TVine.IsDoubledTriangle (umap π G) := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hv, hm⟩ := h
  have hx : x ∈ G.verts := by rw [hv]; simp
  have hy : y ∈ G.verts := by rw [hv]; simp
  have hz : z ∈ G.verts := by rw [hv]; simp
  have hne : ∀ {u w : V}, u ∈ G.verts → w ∈ G.verts → u ≠ w → π u ≠ π w :=
    fun hu hw huw he => huw (hinj hu hw he)
  refine ⟨π x, π y, π z, hne hx hy hxy, hne hx hz hxz, hne hy hz hyz, ?_, fun e' => ?_⟩
  · change G.verts.image π = _
    rw [hv]; simp [Finset.image_insert]
  · have hpair : ∀ {u w : V}, u ∈ G.verts → w ∈ G.verts → s(π u, π w) = Sym2.map π s(u, w) :=
      fun _ _ => (Sym2.map_mk π _ _).symm
    have hmem : ∀ {u w : V}, u ∈ G.verts → w ∈ G.verts → s(u, w) ∈ G.verts.sym2 :=
      fun hu hw => Finset.mk_mem_sym2_iff.mpr ⟨hu, hw⟩
    by_cases hex : ∃ e ∈ G.verts.sym2, Sym2.map π e = e'
    · obtain ⟨e, he, rfl⟩ := hex
      rw [umap_mult_map hinj he, hm e, hpair hx hy, hpair hy hz, hpair hx hz]
      have k : ∀ {u w : V}, u ∈ G.verts → w ∈ G.verts → (Sym2.map π e = Sym2.map π s(u, w) ↔ e = s(u, w)) :=
        fun hu hw => ⟨fun h => sym2_map_injOn hinj he (hmem hu hw) h, fun h => h ▸ rfl⟩
      simp only [k hx hy, k hy hz, k hx hz]
    · rw [umap_mult_eq_zero fun e₀ he₀ hmap => hex ⟨e₀, he₀, hmap⟩]
      have h1 : e' ≠ s(π x, π y) := fun he => hex ⟨_, hmem hx hy, by rw [he, Sym2.map_mk]⟩
      have h2 : e' ≠ s(π y, π z) := fun he => hex ⟨_, hmem hy hz, by rw [he, Sym2.map_mk]⟩
      have h3 : e' ≠ s(π x, π z) := fun he => hex ⟨_, hmem hx hz, by rw [he, Sym2.map_mk]⟩
      simp [h1, h2, h3]

end UMap

section IsoMol
variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [DecidableEq V'] [Fintype D']
  [DecidableEq D']
variable {M : Molecule V D} {M' : Molecule V' D'} {B : Finset V} {B' : Finset V'}

theorem count_map_injOn {π : V → V'} {s : Finset V} (h : Set.InjOn π s) {m : Multiset (Sym2 V)}
    (hm : ∀ e ∈ m, e ∈ s.sym2) {e : Sym2 V} (he : e ∈ s.sym2) :
    (m.map (Sym2.map π)).count (Sym2.map π e) = m.count e := by
  classical
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun x hx =>
    ⟨fun h' => sym2_map_injOn h he (hm x hx) h', fun h' => h' ▸ rfl⟩

theorem groupBonds_mem_sym2 (M : Molecule V D) (S : Finset V) : ∀ e ∈ M.groupBonds S, e ∈ S.sym2 :=
  fun e he => Finset.mem_sym2_iff.mpr (RedSplice.InducedIso.mem_of_mem_groupBonds he)

namespace IsoMol
variable (I : RedSplice.InducedIso M M' B B')

theorem bondsBetween_eq {u v : V} (hu : u ∈ B) (hv : v ∈ B) :
    M'.bondsBetween (I.π u) (I.π v) = M.bondsBetween u v := by
  rw [bondsBetween_eq_count M' (I.pi_mem hu) (I.pi_mem hv), bondsBetween_eq_count M hu hv, I.groupBonds_map,
    show s(I.π u, I.π v) = Sym2.map I.π s(u, v) from (Sym2.map_mk _ _ _).symm]
  exact count_map_injOn I.inj (groupBonds_mem_sym2 M B) (Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩)

theorem groupNbrs_map {v : V} (hv : v ∈ B) : M'.groupNbrs B' (I.π v) = (M.groupNbrs B v).map I.π := by
  classical
  unfold Molecule.groupNbrs
  rw [Multiset.map_map]
  apply Multiset.map_eq_map_of_bij_of_nodup (f := fun x => M'.atom (M'.mate x))
    (g := I.π ∘ fun x => M.atom (M.mate x)) (Finset.nodup _) (Finset.nodup _)
    (fun y hy => (I.e.symm ⟨y, (Finset.mem_filter.mp hy).2⟩).1)
  · intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hy
    have hx := I.atom_comm (I.e.symm ⟨y, h2⟩)
    rw [Equiv.apply_symm_apply] at hx
    have hxB := (I.e.symm ⟨y, h2⟩).2.1
    have hat : M.atom (I.e.symm ⟨y, h2⟩).1 = v :=
      I.inj hxB hv (by rw [← hx]; exact (Mole.mem_dartsAt M' _ y).mp h1)
    exact Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M v _).mpr hat, (I.e.symm ⟨y, h2⟩).2⟩
  · intro y1 hy1 y2 hy2 h
    exact congrArg Subtype.val (I.e.symm.injective (Subtype.ext h))
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    refine ⟨(I.e ⟨x, h2⟩).1, Finset.mem_filter.mpr ⟨?_, (I.e ⟨x, h2⟩).2⟩, by simp⟩
    rw [Mole.mem_dartsAt, I.atom_comm ⟨x, h2⟩, (Mole.mem_dartsAt M v x).mp h1]
  · intro y hy
    obtain ⟨-, h2⟩ := Finset.mem_filter.mp hy
    set x := I.e.symm ⟨y, h2⟩ with hxdef
    have hmx : M.InGroup B (M.mate x.1) := ⟨x.2.2, by simpa [M.mate_mate] using x.2.1⟩
    have hmc := I.mate_comm x
    have hac := I.atom_comm ⟨M.mate x.1, hmx⟩
    have hy' : (I.e x).1 = y := by rw [hxdef, Equiv.apply_symm_apply]
    simp only [Function.comp]
    rw [← hy', ← hmc, hac]

theorem image_verts (a b : V) (ha : a ∈ B) (hb : b ∈ B) :
    ((B.erase a).erase b).image I.π = (B'.erase (I.π a)).erase (I.π b) := by
  by_cases hab : a = b
  · subst hab
    rw [Finset.erase_idem, Finset.erase_idem, image_erase_injOn I.inj ha, I.img]
  · rw [image_erase_injOn (I.inj.mono (erase_subset _ _)) (mem_erase.mpr ⟨fun h => hab h.symm, hb⟩),
      image_erase_injOn I.inj ha, I.img]

theorem isClosure {a b : V} (ha : a ∈ B) (hb : b ∈ B) {G : TVine.UMultigraph V}
    (hG : M.IsClosure B a b G) : M'.IsClosure B' (I.π a) (I.π b) (umap I.π G) := by
  classical
  obtain ⟨hσ, hv, hl, added, hcase, hm⟩ := hG
  have hGB : G.verts ⊆ B := by rw [hv]; exact (erase_subset _ _).trans (erase_subset _ _)
  have hinj : Set.InjOn I.π G.verts := I.inj.mono hGB
  have hsig : M'.sigma (I.π a) (I.π b) = M.sigma a b := bondsBetween_eq I ha hb
  -- every bond counted by `G` lives on the vertices of `G`
  have hmemF : ∀ e ∈ (M.groupBonds B).filter (fun f => a ∉ f ∧ b ∉ f), e ∈ G.verts.sym2 := by
    intro e he
    by_contra hne
    have := hm e
    rw [mult_eq_zero_of_not_mem_sym2 hne] at this
    have hpos := Multiset.count_pos.mpr he
    omega
  have hmemA : ∀ e ∈ added, e ∈ G.verts.sym2 := by
    intro e he
    by_contra hne
    have := hm e
    rw [mult_eq_zero_of_not_mem_sym2 hne] at this
    have hpos := Multiset.count_pos.mpr he
    omega
  have hfilt : (M'.groupBonds B').filter (fun f => I.π a ∉ f ∧ I.π b ∉ f) =
      ((M.groupBonds B).filter (fun f => a ∉ f ∧ b ∉ f)).map (Sym2.map I.π) := by
    rw [I.groupBonds_map, Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro x hx
    have hxB := groupBonds_mem_sym2 M B x hx
    simp only [Function.comp, mem_map_iff_injOn I.inj hxB ha, mem_map_iff_injOn I.inj hxB hb]
  refine ⟨by rwa [hsig], ?_, ?_, added.map (Sym2.map I.π), ?_, ?_⟩
  · change G.verts.image I.π = _
    rw [hv, image_verts I a b ha hb]
  · intro x'
    change umapMult I.π G s(x', x') = 0
    unfold umapMult
    split_ifs with h
    · obtain ⟨he, hmap⟩ := h.choose_spec
      revert he hmap
      generalize h.choose = e
      intro he hmap
      induction e using Sym2.ind with
      | h u w =>
        rw [Sym2.map_mk] at hmap
        rw [Finset.mk_mem_sym2_iff] at he
        have huw : u = w := by
          rcases Sym2.eq_iff.mp hmap with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hinj he.1 he.2 (h1.trans h2.symm)
          · exact hinj he.1 he.2 (h1.trans h2.symm)
        subst huw
        exact hl u
    · rfl
  · rcases hcase with ⟨h0, p, q, r, t, h1, h2, h3⟩ | ⟨h0, x, y, h1, h2, h3⟩
    · refine Or.inl ⟨by rw [hsig, h0], I.π p, I.π q, I.π r, I.π t, ?_, ?_, ?_⟩
      · rw [groupNbrs_map I ha, h1]; simp
      · rw [groupNbrs_map I hb, h2]; simp
      · rw [h3]; simp
    · refine Or.inr ⟨by rw [hsig, h0], I.π x, I.π y, ?_, ?_, ?_⟩
      · rw [groupNbrs_map I ha, h1]; simp
      · rw [groupNbrs_map I hb, h2]; simp
      · rw [h3]; simp
  · intro e'
    rw [hfilt, ← Multiset.count_add, ← Multiset.map_add]
    set m := (M.groupBonds B).filter (fun f => a ∉ f ∧ b ∉ f) + added with hmdef
    have hmG : ∀ e ∈ m, e ∈ G.verts.sym2 := by
      intro e he
      rcases Multiset.mem_add.mp he with he | he
      · exact hmemF e he
      · exact hmemA e he
    by_cases hex : ∃ e ∈ G.verts.sym2, Sym2.map I.π e = e'
    · obtain ⟨e, he, rfl⟩ := hex
      rw [umap_mult_map hinj he, count_map_injOn hinj hmG he, hm e, hmdef, Multiset.count_add]
    · rw [umap_mult_eq_zero fun e₀ he₀ hmap => hex ⟨e₀, he₀, hmap⟩]
      symm
      rw [Multiset.count_eq_zero]
      intro hmem
      obtain ⟨e₀, he₀, hmap⟩ := Multiset.mem_map.mp hmem
      exact hex ⟨e₀, hmG e₀ he₀, hmap⟩

theorem isTVine {a b : V} (h : M.IsTVine B a b) : M'.IsTVine B' (I.π a) (I.π b) := by
  obtain ⟨hB, hm2, G, G', hc, hr, ht⟩ := h
  have ha := hB.2.1
  have hb := hB.2.2.1
  have hGB : G.verts ⊆ B := by rw [hc.2.1]; exact (erase_subset _ _).trans (erase_subset _ _)
  have hinj : Set.InjOn I.π G.verts := I.inj.mono hGB
  refine ⟨I.isBlock hB, ?_, umap I.π G, umap I.π G', isClosure I ha hb hc, rtg_umap hinj hr,
    doubledTriangle_umap (hinj.mono (rtg_verts_subset hr)) ht⟩
  intro u' hu' v' hv' huv
  obtain ⟨u, hu, rfl⟩ := (I.mem_B').mp hu'
  obtain ⟨v, hv, rfl⟩ := (I.mem_B').mp hv'
  rw [bondsBetween_eq I hu hv]
  exact hm2 u hu v hv (fun h => huv (h ▸ rfl))

end IsoMol

end IsoMol

/-- **T-vines are invariant under isomorphisms of induced subgraphs** (discharges the staged obligation). -/
theorem tvineIsoInvariant : TVineIsoInvariant := by
  intro V D V' D' _ _ _ _ _ _ M M' B B' I a b h
  exact IsoMol.isTVine I h

instance : Fact TVineIsoInvariant := ⟨tvineIsoInvariant⟩

end WaveTurbulence.GammaLow.Fama

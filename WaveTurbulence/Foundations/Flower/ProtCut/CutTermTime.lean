/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairDecEquiv
public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueLayer
public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitCouple

/-! # D2c PROT-CUT: the terminal pin, at one decoration (o73 Prop 13.1, time level)

A protected tree with code `X = appendChain Xp (pair m Qr Qg inner nil)` has its terminal node `𝔫_b` at
`Xp.lonePath ++ bPath m inner` and the partner `𝔫_a` at `Xp.lonePath`. `CutTermData` collects the four pieces:
the prefix (code `Xp`), the interior (code `inner`) and the two side couples (`Qr`, `Qg`), with the layers of the
protected tree.

`protTime_cutTerm`: with `𝔫_b` designated at `s` (upper clock `T`), the free-time integral is
`∫_{u ∈ cutU} (boundary phases at u, s) · prefix(T, u) · interior(u, s) · Qr(u, s) · Qg(u, s) du`, where `cutU` is
`max(s, 𝔏_a, 0) < u < min(T, 𝔏_a + 1)`. Internally the closing pair is a garden `GZ` (main's `glueData_tree`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The closing pair `pair m Qr Qg inner nil`. -/
abbrev cpair (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) : RegChain := .pair m Qr Qg inner .nil

theorem cpair_lonePath (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) :
    (cpair m Qr Qg inner).lonePath = lonePos m inner := by
  simp [RegChain.lonePath, lonePos, bPath]

/-- **The pieces of a terminal-pinned protected tree** (o73 Prop 13.1). -/
structure CutTermData (LG : LayeredGarden 1) (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner : RegChain) (LGp LGi : LayeredGarden 1) (LGr LGg : LayeredGarden 2) : Prop where
  dec : (appendChain Xp (cpair m Qr Qg inner)).DecodesTree LG.garden
  wfZ : (cpair m Qr Qg inner).wf = true
  decP : Xp.DecodesTree LGp.garden
  sigP : LGp.garden.sig 0 = LG.garden.sig 0
  decI : inner.DecodesTree LGi.garden
  sigI : LGi.garden.sig 0 = slotSign (LG.garden.sig 0) m.c
  decR : Qr.Decodes LGr.garden
  decG : Qg.Decodes LGg.garden
  layP : ∀ z : GNode LGp.garden.tree, LGp.layer z = layerAt LG ((0 : Fin 1), z.1.2)
  layI : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt LG ((0 : Fin 1), Xp.lonePath ++ m.c :: z.1.2)
  layR : ∀ z : GNode LGr.garden.tree,
    LGr.layer z = layerAt LG ((0 : Fin 1), Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2))
  layG : ∀ z : GNode LGg.garden.tree,
    LGg.layer z = layerAt LG ((0 : Fin 1), Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2))

/-- The terminal pin: `𝔫_b` designated at `s`. -/
def termFix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (s : ℝ) {T : Fin 1 → TTree}
    (b : GBranch T) : Option ℝ :=
  if b.1.2 = Xp.lonePath ++ bPath m inner then some s else none

/-- The range of the partner time `u`. -/
def cutU (LG : LayeredGarden 1) (Xp : RegChain) (T s : ℝ) : Set ℝ :=
  {u | (layerAt LG ((0 : Fin 1), Xp.lonePath) : ℝ) < u ∧ u < layerAt LG ((0 : Fin 1), Xp.lonePath) + 1 ∧
    0 < u ∧ u < T ∧ s < u}

theorem measurableSet_cutU (LG : LayeredGarden 1) (Xp : RegChain) (T s : ℝ) :
    MeasurableSet (cutU LG Xp T s) := by
  unfold cutU
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter
        ((measurableSet_lt measurable_id measurable_const).inter
          (measurableSet_lt measurable_const measurable_id))))

theorem bPath_ne_nil (m : MiniTreeCode) (inner : RegChain) : bPath m inner ≠ [] := by simp [bPath]

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include D hZ hsZ

/-- The gluing of the prefix and the closing pair. -/
theorem gd : GlueData LG.garden LGp.garden GZ Xp := glueData_tree D.dec D.decP D.sigP hZ hsZ

/-- The closing pair as a layered garden (layers of the protected tree). -/
abbrev LGZ : LayeredGarden 1 :=
  ⟨GZ, fun y => LG.layer ((D.gd hZ hsZ).ι₂ y), (botLayered_tree D.dec D.decP D.sigP hZ hsZ).isLayering⟩

theorem LGZ_garden : (D.LGZ hZ hsZ).garden = GZ := rfl

theorem LGZ_layer (y : GNode GZ.tree) : (D.LGZ hZ hsZ).layer y = LG.layer ((D.gd hZ hsZ).ι₂ y) := rfl

/-- The closing pair and its three pieces. -/
theorem hp : PairData m Qr Qg inner GZ LGi.garden LGr.garden LGg.garden :=
  ⟨hZ, D.decI, by rw [D.sigI]; exact congrArg (slotSign · m.c) hsZ.symm, D.decR, D.decG⟩

/-- The partner `𝔫_a` in the protected tree. -/
def aB : GBranch LG.garden.tree := (D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).rootB)

/-- The terminal node `𝔫_b` in the protected tree. -/
def bG : GBranch LG.garden.tree := (D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).bB)

theorem aB_path : (D.aB hZ hsZ).1 = ((0 : Fin 1), Xp.lonePath) := by
  show botAddr Xp.lonePath ((0 : Fin 1), ([] : Path)) = _
  simp [botAddr]

theorem bG_path : (D.bG hZ hsZ).1 = ((0 : Fin 1), Xp.lonePath ++ bPath m inner) := by
  show botAddr Xp.lonePath ((0 : Fin 1), bPath m inner) = _
  simp [botAddr]

theorem ofSum_inr_path (y : GBranch GZ.tree) :
    ((D.gd hZ hsZ).ofSum (.inr y)).1 = ((0 : Fin 1), Xp.lonePath ++ y.1.2) := by
  obtain ⟨⟨j, p⟩, _⟩ := y
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show botAddr Xp.lonePath ((0 : Fin 1), p) = _
  simp [botAddr]

theorem ofSum_inl_path (x : GBranch LGp.garden.tree) :
    ((D.gd hZ hsZ).ofSum (.inl x)).1 = ((0 : Fin 1), x.1.2) := rfl

theorem termFix_aB (s : ℝ) : termFix Xp m inner s (D.aB hZ hsZ) = none := by
  unfold termFix
  rw [D.aB_path hZ hsZ]
  simp [bPath_ne_nil]

theorem termFix_bG (s : ℝ) : termFix Xp m inner s (D.bG hZ hsZ) = some s := by
  unfold termFix
  rw [D.bG_path hZ hsZ]
  simp

theorem top_not_prefix (x : GBranch LGp.garden.tree) : ¬ Xp.lonePath <+: x.1.2 := by
  have hm := x.2
  rw [show x.1.1 = 0 from Subsingleton.elim _ _] at hm
  exact (((D.gd hZ hsZ).top_branch_iff _).mp hm).2

theorem termFix_inl (s : ℝ) (x : GBranch LGp.garden.tree) :
    termFix Xp m inner s ((D.gd hZ hsZ).ofSum (.inl x)) = none := by
  unfold termFix
  rw [D.ofSum_inl_path hZ hsZ]
  simp only
  rw [if_neg]
  intro he
  exact D.top_not_prefix hZ hsZ x (he ▸ List.prefix_append _ _)

/-! ### Lone parents -/

theorem isLone_iff (ℓ : GLeaf LG.garden.tree) :
    LG.garden.IsLone ℓ ↔ ℓ.1.2 = Xp.lonePath ++ lonePos m inner := by
  unfold Garden.IsLone
  rw [D.dec.2.1 ℓ, appendChain_lonePath, cpair_lonePath]
  split_ifs with h <;> simp [h]

theorem isLoneParent_iff (b : GBranch LG.garden.tree) :
    LG.garden.IsLoneParent b ↔ b = D.bG hZ hsZ := by
  constructor
  · rintro ⟨ℓ, hℓ, -, i, hi⟩
    rw [D.isLone_iff hZ hsZ] at hℓ
    rw [hℓ, lonePos, ← List.append_assoc] at hi
    have := (List.append_inj' hi rfl).1
    apply Subtype.ext
    rw [D.bG_path hZ hsZ]
    exact Prod.ext (Subsingleton.elim _ _) this.symm
  · rintro rfl
    have hmem : Xp.lonePath ++ lonePos m inner ∈ (LG.garden.tree 0).leaves := by
      have e : Xp.lonePath ++ lonePos m inner = (appendChain Xp (cpair m Qr Qg inner)).lonePath := by
        rw [appendChain_lonePath, cpair_lonePath]
      rw [e, D.dec.1]
      exact lonePath_mem_leaves _ _
    refine ⟨⟨((0 : Fin 1), Xp.lonePath ++ lonePos m inner), hmem⟩, (D.isLone_iff hZ hsZ _).mpr rfl,
      Subsingleton.elim _ _, m.lone, ?_⟩
    rw [D.bG_path hZ hsZ]
    simp [lonePos]

theorem isLoneParent_Z (y : GBranch GZ.tree) : GZ.IsLoneParent y ↔ y = (D.hp hZ hsZ).bB := by
  constructor
  · intro hy
    exact (D.hp hZ hsZ).isLoneParent_G y hy
  · rintro rfl
    have hmem : lonePos m inner ∈ (GZ.tree 0).leaves := by
      rw [hZ.1, ← cpair_lonePath]
      exact lonePath_mem_leaves _ _
    refine ⟨⟨((0 : Fin 1), lonePos m inner), hmem⟩, ?_, Subsingleton.elim _ _, m.lone, rfl⟩
    unfold Garden.IsLone
    exact (hZ.2.1 _).trans (by rw [cpair_lonePath]; simp)

theorem hlone (b : GBranch LG.garden.tree) :
    LG.garden.IsLoneParent b ↔ ∃ y, b = (D.gd hZ hsZ).ofSum (.inr y) ∧ GZ.IsLoneParent y := by
  rw [D.isLoneParent_iff hZ hsZ]
  constructor
  · rintro rfl
    exact ⟨(D.hp hZ hsZ).bB, rfl, (D.isLoneParent_Z hZ hsZ _).mpr rfl⟩
  · rintro ⟨y, rfl, hy⟩
    rw [(D.isLoneParent_Z hZ hsZ y).mp hy]
    rfl

theorem hlone₁ (x : GBranch LGp.garden.tree) :
    LGp.garden.IsLoneParent x ↔
      ((D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).rootB)).IsChildOf ((D.gd hZ hsZ).ofSum (.inl x)) := by
  have key : LGp.garden.IsLoneParent x ↔ ∃ i : Fin 3, x.1.2 ++ [i] = Xp.lonePath := by
    constructor
    · rintro ⟨ℓ, hℓ, -, i, hi⟩
      have hpath : ℓ.1.2 = Xp.lonePath := by
        by_contra hne
        unfold Garden.IsLone at hℓ
        rw [D.decP.2.1 ℓ, ite_eq_right hne] at hℓ
        exact absurd hℓ (by simp)
      exact ⟨i, hi.symm.trans hpath⟩
    · rintro ⟨i, hi⟩
      have hmem : Xp.lonePath ∈ (LGp.garden.tree x.1.1).leaves := by
        rw [Subsingleton.elim x.1.1 0, D.decP.1]
        exact lonePath_mem_leaves _ _
      refine ⟨⟨(x.1.1, Xp.lonePath), hmem⟩, ?_, rfl, i, hi.symm⟩
      unfold Garden.IsLone
      exact (D.decP.2.1 _).trans (by simp)
  rw [key]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨Subsingleton.elim _ _, i, ?_⟩
    rw [D.ofSum_inr_path hZ hsZ, D.ofSum_inl_path hZ hsZ]
    simp [PairData.rootB, hi]
  · rintro ⟨-, i, hi⟩
    rw [D.ofSum_inr_path hZ hsZ, D.ofSum_inl_path hZ hsZ] at hi
    simp only [PairData.rootB, List.append_nil] at hi
    exact ⟨i, hi.symm⟩

/-! ### The glue step -/

/-- The designations inside the closing pair, after `𝔫_a` is designated at `u`. -/
def fixZ (s u : ℝ) (y : GBranch GZ.tree) : Option ℝ :=
  Function.update (termFix Xp m inner s) (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr y))

theorem fixZ_rootB (s u : ℝ) : D.fixZ hZ hsZ s u (D.hp hZ hsZ).rootB = some u := by
  unfold fixZ
  exact Function.update_self _ _ _

theorem ofSum_inr_ne_aB (y : GBranch GZ.tree) (hy : y ≠ (D.hp hZ hsZ).rootB) :
    (D.gd hZ hsZ).ofSum (.inr y) ≠ D.aB hZ hsZ := by
  intro he
  have := (D.gd hZ hsZ).ofSum_injective he
  simp only [Sum.inr.injEq] at this
  exact hy this

theorem fixZ_other (s u : ℝ) (y : GBranch GZ.tree) (hy : y ≠ (D.hp hZ hsZ).rootB) :
    D.fixZ hZ hsZ s u y = termFix Xp m inner s ((D.gd hZ hsZ).ofSum (.inr y)) := by
  unfold fixZ
  exact Function.update_of_ne (D.ofSum_inr_ne_aB hZ hsZ y hy) _ _

theorem bB_ne_rootB : (D.hp hZ hsZ).bB ≠ (D.hp hZ hsZ).rootB := by
  intro he
  have := congrArg (fun b : GBranch GZ.tree => b.1.2) he
  simp [PairData.bB, PairData.rootB, bPath] at this

theorem fixZ_bB (s u : ℝ) : D.fixZ hZ hsZ s u (D.hp hZ hsZ).bB = some s := by
  rw [D.fixZ_other hZ hsZ s u _ (D.bB_ne_rootB hZ hsZ)]
  exact D.termFix_bG hZ hsZ s

theorem fixZ_free (s u : ℝ) (y : GBranch GZ.tree) (hy : y ≠ (D.hp hZ hsZ).rootB)
    (hb : y.1.2 ≠ bPath m inner) : D.fixZ hZ hsZ s u y = none := by
  rw [D.fixZ_other hZ hsZ s u y hy]
  unfold termFix
  rw [D.ofSum_inr_path hZ hsZ]
  simp only
  rw [if_neg]
  intro he
  exact hb (List.append_cancel_left he)

/-- **The glue step**: with `𝔫_a` designated at `u`, the prefix splits off. -/
theorem protTime_glueT (L γ δ : ℝ) {d : ℕ} (T s s' u : ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (Function.update (termFix Xp m inner s) (D.aB hZ hsZ) (some u)) K =
      protTime L γ δ LGp (fun _ => T) u (fun _ => none) (K ∘ (D.gd hZ hsZ).ι₁) *
        protTime L γ δ (D.LGZ hZ hsZ) (fun _ => T) s' (D.fixZ hZ hsZ s u) (K ∘ (D.gd hZ hsZ).ι₂) := by
  set fix := Function.update (termFix Xp m inner s) (D.aB hZ hsZ) (some u)
  have hD := fun τ hτ => protDom_glue_pinned (LG₂ := D.LGZ hZ hsZ) (D.gd hZ hsZ) (fun _ => T) s' fix
    (D.hp hZ hsZ).rootB rfl u (Function.update_self _ _ _)
    (fun x => by rw [D.layP, ← layerAt_node]; rfl) (fun y => rfl) (D.hlone hZ hsZ) (D.hlone₁ hZ hsZ) τ hτ
  rw [protTime_glue L γ δ (LG₂ := D.LGZ hZ hsZ) (D.gd hZ hsZ) (fun _ => T) s' fix (fun _ => T) u
    (fun _ => T) s' K hD]
  congr 2
  funext x
  show Function.update (termFix Xp m inner s) (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inl x)) = none
  rw [Function.update_of_ne, D.termFix_inl hZ hsZ]
  intro he
  have := (D.gd hZ hsZ).ofSum_injective he
  simp at this

/-! ### The pair step -/

theorem fixZ_βi (s u : ℝ) (x : GBranch LGi.garden.tree) :
    D.fixZ hZ hsZ s u ((D.hp hZ hsZ).βi x) = none := by
  apply D.fixZ_free hZ hsZ s u
  · intro he
    have := congrArg (fun b : GBranch GZ.tree => b.1.2) he
    simp [PairData.βi, PairData.rootB] at this
  · intro he
    have h2 : m.c :: x.1.2 = m.c :: inner.lonePath := he
    have hx := x.2
    rw [show x.1.1 = 0 from Subsingleton.elim _ _, (D.hp hZ hsZ).treeI] at hx
    exact PairData.not_lonePath_prefix_of_branching hx ((List.cons.inj h2).2 ▸ List.prefix_refl _)

theorem rBase_ne_nil (ζ : ℤˣ) (j : Fin 2) : rBase m inner ζ j ≠ [] := by
  rcases rBase_cases m inner ζ j with h | h <;> simp [h]

theorem gBase_ne_nil (ζ : ℤˣ) (j : Fin 2) : gBase m inner ζ j ≠ [] := by
  rcases gBase_cases m inner ζ j with h | h <;> simp [h]

theorem fixZ_βr (s u : ℝ) (y : GBranch LGr.garden.tree) :
    D.fixZ hZ hsZ s u ((D.hp hZ hsZ).βr y) = none := by
  apply D.fixZ_free hZ hsZ s u
  · intro he
    have h2 : rBase m inner (GZ.sig 0) y.1.1 ++ y.1.2 = [] := congrArg (fun b : GBranch GZ.tree => b.1.2) he
    exact D.rBase_ne_nil hZ hsZ _ _ (List.append_eq_nil_iff.mp h2).1
  · intro he
    have h2 : rBase m inner (GZ.sig 0) y.1.1 ++ y.1.2 = bPath m inner := he
    have hreg := regionOf_rBase m inner (GZ.sig 0) y.1.1 y.1.2
    rw [h2, regionOf_bPath] at hreg
    exact absurd hreg (by simp)

theorem fixZ_βg (s u : ℝ) (y : GBranch LGg.garden.tree) :
    D.fixZ hZ hsZ s u ((D.hp hZ hsZ).βg y) = none := by
  apply D.fixZ_free hZ hsZ s u
  · intro he
    have h2 : gBase m inner (GZ.sig 0) y.1.1 ++ y.1.2 = [] := congrArg (fun b : GBranch GZ.tree => b.1.2) he
    exact D.gBase_ne_nil hZ hsZ _ _ (List.append_eq_nil_iff.mp h2).1
  · intro he
    have h2 : gBase m inner (GZ.sig 0) y.1.1 ++ y.1.2 = bPath m inner := he
    have hreg := regionOf_gBase m inner (GZ.sig 0) y.1.1 y.1.2
    rw [h2, regionOf_bPath] at hreg
    exact absurd hreg (by simp)

theorem layer_ι₂ (p : Path) (y : GNode GZ.tree) (hy : y.1.2 = p) :
    (D.LGZ hZ hsZ).layer y = layerAt LG ((0 : Fin 1), Xp.lonePath ++ p) := by
  rw [D.LGZ_layer, ← layerAt_node]
  congr 1
  obtain ⟨⟨j, q⟩, _⟩ := y
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp only at hy
  subst hy
  show botAddr Xp.lonePath ((0 : Fin 1), q) = _
  simp [botAddr]

theorem hli (z : GNode LGi.garden.tree) :
    LGi.layer z = (D.LGZ hZ hsZ).layer ((D.hp hZ hsZ).ιi z) := by
  rw [D.layI, D.layer_ι₂ hZ hsZ (m.c :: z.1.2) _ rfl]

theorem hlr (z : GNode LGr.garden.tree) :
    LGr.layer z = (D.LGZ hZ hsZ).layer ((D.hp hZ hsZ).ιr z) := by
  rw [D.layR, D.layer_ι₂ hZ hsZ (rBase m inner (GZ.sig 0) z.1.1 ++ z.1.2) _ rfl, hsZ]

theorem hlg (z : GNode LGg.garden.tree) :
    LGg.layer z = (D.LGZ hZ hsZ).layer ((D.hp hZ hsZ).ιg z) := by
  rw [D.layG, D.layer_ι₂ hZ hsZ (gBase m inner (GZ.sig 0) z.1.1 ++ z.1.2) _ rfl, hsZ]

/-- **The pair step**, for `s ≤ u ≤ T`. -/
theorem protTime_pairT (L γ δ : ℝ) {d : ℕ} (T s s' u : ℝ) (hsu : s ≤ u) (huT : u ≤ T)
    (K : GNode GZ.tree → Mom d) :
    protTime L γ δ (D.LGZ hZ hsZ) (fun _ => T) s' (D.fixZ hZ hsZ s u) K =
      Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode GZ K (D.hp hZ hsZ).rootB * u : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode GZ K (D.hp hZ hsZ).bB * s : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => u) s (fun _ => none) (K ∘ (D.hp hZ hsZ).ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (GZ.sig 0) u s y.1.1) 0 (fun _ => none)
              (K ∘ (D.hp hZ hsZ).ιr) *
            protTime L γ δ LGg (fun y => cupG m inner (GZ.sig 0) u s y.1.1) 0 (fun _ => none)
              (K ∘ (D.hp hZ hsZ).ιg))) := by
  have e := PairData.protTime_pair (LG := D.LGZ hZ hsZ) (D.hp hZ hsZ) L γ δ T s' u s (D.fixZ hZ hsZ s u) (D.fixZ_rootB hZ hsZ s u)
    (D.fixZ_bB hZ hsZ s u) (D.hli hZ hsZ) (D.hlr hZ hsZ) (D.hlg hZ hsZ) huT (hsu.trans huT)
    (fun x σ hx => by rw [D.fixZ_βi hZ hsZ] at hx; simp at hx)
    (fun y σ hy => by rw [D.fixZ_βr hZ hsZ] at hy; simp at hy)
    (fun y σ hy => by rw [D.fixZ_βg hZ hsZ] at hy; simp at hy) K
  have fi : (fun x => D.fixZ hZ hsZ s u ((D.hp hZ hsZ).βi x)) = fun _ => none :=
    funext (D.fixZ_βi hZ hsZ s u)
  have fr : (fun y => D.fixZ hZ hsZ s u ((D.hp hZ hsZ).βr y)) = fun _ => none :=
    funext (D.fixZ_βr hZ hsZ s u)
  have fg : (fun y => D.fixZ hZ hsZ s u ((D.hp hZ hsZ).βg y)) = fun _ => none :=
    funext (D.fixZ_βg hZ hsZ s u)
  rw [fi, fr, fg] at e
  exact e

/-- **Vanishing below the terminal time**: with a nonempty interior and `u ≤ s`, the closing pair vanishes. -/
theorem protTime_pairT_zero (L γ δ : ℝ) {d : ℕ} (T s s' u : ℝ) (hsu : u ≤ s)
    (hin : inner.lonePath ≠ []) (K : GNode GZ.tree → Mom d) :
    protTime L γ δ (D.LGZ hZ hsZ) (fun _ => T) s' (D.fixZ hZ hsZ s u) K = 0 := by
  unfold protTime
  refine (integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)).trans (integral_zero _ _)
  simp only [Pi.zero_apply]
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  set τ := (D.LGZ hZ hsZ).garden.extendFix (D.fixZ hZ hsZ s u) σ
  have hτ : ∀ b v, D.fixZ hZ hsZ s u b = some v → τ b = v := fun b v hv => extendFix_some _ _ _ hv
  have hI := (PairData.protDom_pair_mp (LG := D.LGZ hZ hsZ) (D.hp hZ hsZ) T s' u s (D.fixZ hZ hsZ s u) (D.fixZ_rootB hZ hsZ s u)
    (D.fixZ_bB hZ hsZ s u) (D.hli hZ hsZ) (D.hlr hZ hsZ) (D.hlg hZ hsZ)
    (fun x σ hx => by rw [D.fixZ_βi hZ hsZ] at hx; simp at hx)
    (fun y σ hy => by rw [D.fixZ_βr hZ hsZ] at hy; simp at hy)
    (fun y σ hy => by rw [D.fixZ_βg hZ hsZ] at hy; simp at hy) τ hτ hmem).1
  -- the lone parent of the interior
  obtain ⟨q, k, hq⟩ := (List.eq_nil_or_concat inner.lonePath).resolve_left hin
  have hmem' : q ∈ (LGi.garden.tree 0).branching := by
    rw [D.decI.1]
    refine TTree.branching_of_append_mem _ (i := k) ?_
    rw [← List.concat_eq_append, ← hq]
    exact lonePath_mem_plug inner _ _
  let x₀ : GBranch LGi.garden.tree := ⟨((0 : Fin 1), q), hmem'⟩
  have hx₀ : LGi.garden.IsLoneParent x₀ :=
    ((D.hp hZ hsZ).isLoneParent_I x₀).mpr ⟨k, by simpa using hq⟩
  have h1 := hI.2 x₀ hx₀ (D.fixZ_βi hZ hsZ s u x₀)
  have h2 := ((hI.1 x₀).1 (D.fixZ_βi hZ hsZ s u x₀)).2.2.2
  simp only at h1 h2
  linarith

/-! ### The partner pin -/

theorem aB_child_ne (b' : GBranch LG.garden.tree) (hb : b'.IsChildOf (D.aB hZ hsZ)) (s : ℝ) (σ : ℝ)
    (hσ : termFix Xp m inner s b' = some σ) : inner.lonePath = [] ∧ σ = s := by
  unfold termFix at hσ
  split_ifs at hσ with hp
  obtain ⟨-, i, hi⟩ := hb
  have hi' : b'.1.2 = Xp.lonePath ++ [i] := by rw [hi, D.aB_path hZ hsZ]
  rw [hp] at hi'
  have h4 := List.append_cancel_left hi'
  have hl : inner.lonePath.length = 0 := by
    have := congrArg List.length h4
    simp only [bPath, List.length_append, List.length_singleton, List.length_cons, List.length_nil] at this
    omega
  exact ⟨List.eq_nil_of_length_eq_zero hl, (Option.some.inj hσ).symm⟩

theorem aB_parent_free (b : GBranch LG.garden.tree) (hb : (D.aB hZ hsZ).IsChildOf b) (s : ℝ) :
    termFix Xp m inner s b = none := by
  unfold termFix
  rw [if_neg]
  intro hp
  obtain ⟨-, i, hi⟩ := hb
  have hi' : Xp.lonePath = b.1.2 ++ [i] := by rw [← hi, D.aB_path hZ hsZ]
  rw [hp] at hi'
  have := congrArg List.length hi'
  simp only [bPath, List.length_append, List.length_singleton, List.length_cons, List.length_nil] at this
  omega

theorem aB_not_lone : ¬ LG.garden.IsLoneParent (D.aB hZ hsZ) := by
  rw [D.isLoneParent_iff hZ hsZ]
  intro he
  have := congrArg (fun b : GBranch LG.garden.tree => b.1.2) he
  simp only [D.aB_path hZ hsZ, D.bG_path hZ hsZ] at this
  have := congrArg List.length this
  simp [bPath] at this

theorem layer_aB : LG.layer (D.aB hZ hsZ).toNode = layerAt LG ((0 : Fin 1), Xp.lonePath) := by
  rw [← layerAt_node]
  exact congrArg (layerAt LG) (D.aB_path hZ hsZ)

theorem cutU_sub (T s s' : ℝ) :
    cutU LG Xp T s ⊆ pinSet LG (fun _ => T) s' (termFix Xp m inner s) (D.aB hZ hsZ) := by
  rintro u ⟨h1, h2, h3, h4, h5⟩
  refine ⟨by rw [D.layer_aB]; exact h1, by rw [D.layer_aB]; exact h2, h3, h4, fun b' hb' σ hσ => ?_,
    fun b hb σ hσ => ?_, fun hl => absurd hl (D.aB_not_lone hZ hsZ)⟩
  · rw [(D.aB_child_ne hZ hsZ b' hb' s σ hσ).2]; exact h5
  · rw [D.aB_parent_free hZ hsZ b hb s] at hσ; simp at hσ

theorem pinSet_lt (T s s' u : ℝ) (hu : u ∈ pinSet LG (fun _ => T) s' (termFix Xp m inner s) (D.aB hZ hsZ))
    (hnil : inner.lonePath = []) : s < u := by
  have hchild : (D.bG hZ hsZ).IsChildOf (D.aB hZ hsZ) := by
    refine ⟨Subsingleton.elim _ _, m.c, ?_⟩
    rw [D.bG_path hZ hsZ, D.aB_path hZ hsZ]
    simp [bPath, hnil]
  exact hu.2.2.2.2.1 _ hchild s (D.termFix_bG hZ hsZ s)

/-- **The terminal pin at one decoration** (o73 Prop 13.1, time level). -/
theorem protTime_cutTerm (L γ δ : ℝ) {d : ℕ} (T s s' : ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (termFix Xp m inner s) K =
      ∫ u in cutU LG Xp T s,
        Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode GZ (K ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).rootB * u : ℝ) * Complex.I) *
          Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode GZ (K ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).bB * s : ℝ) * Complex.I) *
        (protTime L γ δ LGp (fun _ => T) u (fun _ => none) (K ∘ (D.gd hZ hsZ).ι₁) *
          (protTime L γ δ LGi (fun _ => u) s (fun _ => none) (K ∘ (D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιi) *
            (protTime L γ δ LGr (fun y => cupR m inner (GZ.sig 0) u s y.1.1) 0 (fun _ => none)
                (K ∘ (D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιr) *
              protTime L γ δ LGg (fun y => cupG m inner (GZ.sig 0) u s y.1.1) 0 (fun _ => none)
                (K ∘ (D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιg)))) := by
  rw [protTime_pin L γ δ LG (fun _ => T) s' (termFix Xp m inner s) K (D.aB hZ hsZ) (D.termFix_aB hZ hsZ s),
    ← integral_indicator (measurableSet_cutU LG Xp T s)]
  congr 1
  funext u
  by_cases hU : u ∈ cutU LG Xp T s
  · rw [Set.indicator_of_mem (D.cutU_sub hZ hsZ T s s' hU), Set.indicator_of_mem hU]
    beta_reduce
    rw [D.protTime_glueT hZ hsZ L γ δ T s s' u K,
      D.protTime_pairT hZ hsZ L γ δ T s s' u hU.2.2.2.2.le hU.2.2.2.1.le]
    simp only [Function.comp_assoc]
    ring
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun _ => T) s' (termFix Xp m inner s) (D.aB hZ hsZ)
    · rw [Set.indicator_of_mem hP]
      beta_reduce
      have hus : u ≤ s := by
        by_contra hlt
        exact hU ⟨by rw [← D.layer_aB]; exact hP.1, by rw [← D.layer_aB]; exact hP.2.1, hP.2.2.1,
          hP.2.2.2.1, lt_of_not_ge hlt⟩
      have hin : inner.lonePath ≠ [] := fun hnil =>
        absurd (D.pinSet_lt hZ hsZ T s s' u hP hnil) (not_lt.mpr hus)
      rw [D.protTime_glueT hZ hsZ L γ δ T s s' u K,
        D.protTime_pairT_zero hZ hsZ L γ δ T s s' u hus hin, mul_zero]
    · rw [Set.indicator_of_notMem hP]

end CutTermData

end WaveTurbulence.Flower.ProtCut

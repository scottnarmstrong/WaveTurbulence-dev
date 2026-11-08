/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T2mExist

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (a) for couples, time level (`ε = +`)

A couple `LG` decoded by `type2 (pair m Qr Qg inner rest) Xm Qlp` (a nonempty `+` chain). Its root `ρ = n⁺_1 = (0, [])`
is linked to `n⁺_b` at `(0, bPath m inner)`. `Root2Data`: the closing pair `Z = pair m Qr Qg inner nil` (a paired tree
`LGZ`, sign `+`, top) is glued on the couple `closeCouple rest Xm Qlp` (`LGB`, bottom: o104's `K_rest`, "the couple
formed by the suffix chain, its side couples, `Q_lp` and the other chain `X⁻`"), at the lone position of `Z`
(main's `glueData_couple`).

* `protDom_glue_free2`: the time domain of the glue when a top node `p` (here `n⁺_b`) is designated at `u` and the
  bottom couple is free: its tree `0` (below `p`) then has the clock `u`, its tree `1` keeps its clock (`bClock`).
* **`Root2Data.protTime_root2`**: with `ρ` designated at `σ ≤ U 0` (`trFix 0 σ`),
  `protTime = ∫_{u ∈ root2U} Z(both linked nodes at σ, u) · K_rest(clocks (u, U 1))`,
  `root2U = {𝔏_b < u < 𝔏_b + 1, 0 < u, u < U 0, u < σ}` (o104 (a): `u ∈ (𝔏_{ρ'}, min(σ, 𝔏_{ρ'}+1))`; a couple has no
  port). The closing pair with both linked nodes designated is `PairOnly.protTime_both` ((P2)). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The clocks of the bottom couple: `u` for its tree `0` (below `n_b`), `U 1` for its tree `1`. -/
def bClock (U : Fin 2 → ℝ) (u : ℝ) (t : Fin 2) : ℝ := if t = 0 then u else U t

theorem measurable_bClock (U : Fin 2 → ℝ) (t : Fin 2) : Measurable fun u => bClock U u t := by
  unfold bClock; split_ifs
  · exact measurable_id
  · exact measurable_const

/-- **The free-junction glue of a couple.** -/
theorem protDom_glue_free2 {LG LG₂ : LayeredGarden 2} {LG₁ : LayeredGarden 1} {X : RegChain}
    (h : GlueData LG.garden LG₁.garden LG₂.garden X) (U : Fin 2 → ℝ) (s s₁ : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ)
    (p : GBranch LG₁.garden.tree) (u : ℝ) (hfp : fix (h.ofSum (.inl p)) = some u)
    (hfree : ∀ y, fix (h.ofSum (.inr y)) = none) (hu : u ≤ U 0)
    (hl₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.layer x.toNode = LG.layer (h.ofSum (.inl x)).toNode)
    (hl₂ : ∀ y : GBranch LG₂.garden.tree, LG₂.layer y.toNode = LG.layer (h.ofSum (.inr y)).toNode)
    (hlone : ∀ b, LG.garden.IsLoneParent b ↔ ∃ y, b = h.ofSum (.inr y) ∧ LG₂.garden.IsLoneParent y)
    (hlone₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.garden.IsLoneParent x → x = p)
    (hpar : ∀ (x : GBranch LG₁.garden.tree) (y : GBranch LG₂.garden.tree),
      (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl x)) → x = p)
    (hpar' : ∀ y : GBranch LG₂.garden.tree, y.1 = ((0 : Fin 2), []) →
      (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl p)))
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b v, fix b = some v → τ b = v) :
    τ ∈ protDom LG (fun b => U b.1.1) s fix ↔
      (fun x => τ (h.ofSum (.inl x))) ∈ protDom LG₁ (fun _ => U 0) s₁ (fun x => fix (h.ofSum (.inl x))) ∧
        (fun y => τ (h.ofSum (.inr y))) ∈ protDom LG₂ (fun y => bClock U u y.1.1) s
          (fun y => fix (h.ofSum (.inr y))) := by
  have hτp : τ (h.ofSum (.inl p)) = u := hτ _ _ hfp
  have hfst : ∀ y : GBranch LG₂.garden.tree, (h.ofSum (.inr y)).1.1 = y.1.1 := fun y => botAddr_fst _ _
  constructor
  · rintro ⟨hD, hL⟩
    have hlt : ∀ y, (fun y => fix (h.ofSum (.inr y))) y = none → τ (h.ofSum (.inr y)) < bClock U u y.1.1 := by
      refine lt_up_of_chain (fun y => fix (h.ofSum (.inr y))) (fun y => τ (h.ofSum (.inr y))) (bClock U u)
        (fun y y' hc hor => (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hc) hor)
        (fun y hy hf => ?_) (fun y σ hf => by simp only [hfree y] at hf; simp at hf)
      by_cases h0 : y.1.1 = 0
      · have hy0 : y.1 = ((0 : Fin 2), []) := Prod.ext h0 hy
        have := (hD (h.ofSum (.inl p))).2 _ (hpar' y hy0) (Or.inl (hfree y))
        rw [hτp] at this
        unfold bClock; rw [if_pos h0]; exact this
      · have := ((hD (h.ofSum (.inr y))).1 hf).2.2.2
        unfold bClock; rw [if_neg h0]
        simp only [hfst] at this
        exact this
    refine ⟨⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx hf => ?_⟩,
      ⟨fun y => ⟨fun hy => ?_, fun y' hy' hor => ?_⟩, fun y hy hf => ?_⟩⟩
    · have := (hD (h.ofSum (.inl x))).1 hx
      simp only [hl₁]; exact this
    · exact (hD (h.ofSum (.inl x))).2 _ ((h.child_inl_inl x x').mpr hx') hor
    · have := hlone₁ x hx
      subst this
      simp only [hfp] at hf
      exact absurd hf (by simp)
    · obtain ⟨a1, a2, a3, -⟩ := (hD (h.ofSum (.inr y))).1 hy
      simp only [hl₂]
      exact ⟨a1, a2, a3, hlt y hy⟩
    · exact (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hy') hor
    · exact hL _ ((hlone _).mpr ⟨y, rfl, hy⟩) hf
  · rintro ⟨⟨hD₁, hL₁⟩, ⟨hD₂, hL₂⟩⟩
    refine ⟨(h.forall_branch _).mpr ⟨fun x => ⟨fun hx => ?_, fun b' hb' hor => ?_⟩,
      fun y => ⟨fun hy => ?_, fun b' hb' hor => ?_⟩⟩, fun b hb hf => ?_⟩
    · have := (hD₁ x).1 hx
      simp only [hl₁] at this; exact this
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb' hor
        exact (hD₁ x).2 x' ((h.child_inl_inl x x').mp hb') hor
      · rw [hc] at hb' hor
        have hy0 := GlueFix.child_inr_inl h x y' hb'
        have hx := hpar x y' hb'
        subst hx
        rw [hτp]
        have h4 : τ (h.ofSum (.inr y')) < bClock U u y'.1.1 := ((hD₂ y').1 (hfree y')).2.2.2
        unfold bClock at h4
        rw [if_pos (congrArg Prod.fst hy0 : y'.1.1 = 0)] at h4
        exact h4
    · obtain ⟨a1, a2, a3, a4⟩ := (hD₂ y).1 hy
      simp only [hl₂] at a1 a2
      refine ⟨a1, a2, a3, a4.trans_le ?_⟩
      show bClock U u y.1.1 ≤ U (h.ofSum (.inr y)).1.1
      rw [hfst]
      unfold bClock
      split_ifs with h0
      · rw [h0]; exact hu
      · exact le_rfl
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb'
        exact absurd hb' (h.not_child_inl_inr x' y)
      · rw [hc] at hb' hor
        exact (hD₂ y).2 y' ((h.child_inr_inr y y').mp hb') hor
    · obtain ⟨y, rfl, hy⟩ := (hlone b).mp hb
      exact hL₂ y hy hf

/-- The range of the partner time `u = τ_{n_b}` of the root of a couple's `+` chain. -/
def root2U (LG : LayeredGarden 2) (m : MiniTreeCode) (inner : RegChain) (T σ : ℝ) : Set ℝ :=
  {u | (layerAt LG ((0 : Fin 2), bPath m inner) : ℝ) < u ∧ u < layerAt LG ((0 : Fin 2), bPath m inner) + 1 ∧
    0 < u ∧ u < T ∧ u < σ}

theorem measurableSet_root2U (LG : LayeredGarden 2) (m : MiniTreeCode) (inner : RegChain) (T σ : ℝ) :
    MeasurableSet (root2U LG m inner T σ) := by
  unfold root2U
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter
        ((measurableSet_lt measurable_id measurable_const).inter
          (measurableSet_lt measurable_id measurable_const))))

theorem volume_root2U_ne_top (LG : LayeredGarden 2) (m : MiniTreeCode) (inner : RegChain) (T σ : ℝ) :
    volume (root2U LG m inner T σ) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Ioo (layerAt LG ((0 : Fin 2), bPath m inner) : ℝ)
    (layerAt LG ((0 : Fin 2), bPath m inner) + 1))) ?_ (measure_mono fun u hu => ⟨hu.1, hu.2.1⟩)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- **The pieces of a root-traced couple with a nonempty chain on tree `0`** (o104 Prop 7.4 (a)): the closing pair
`Z = pair m Qr Qg inner nil` (a paired tree `LGZ`) glued on a bottom couple `LGB`, with the layers of `LG`. The decoded
instance (`type2 (pair m Qr Qg inner rest) Xm Qlp`, bottom `closeCouple rest Xm Qlp`) is `Root2Data.of_decodes`; the
fields are what the cut uses (the gluing, plainness, the decoration split and glue). -/
structure Root2Data (LG : LayeredGarden 2) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain)
    (LGZ : LayeredGarden 1) (LGB : LayeredGarden 2) : Prop where
  gd : GlueData LG.garden LGZ.garden LGB.garden (cpair m Qr Qg inner)
  decZ : (cpair m Qr Qg inner).DecodesTree LGZ.garden
  plain : LG.garden.IsPlain
  plainB : LGB.garden.IsPlain
  hs : ∀ d : ℕ, gd.DecSplit (Fin d → ℤ)
  hg : ∀ d : ℕ, GlueData.DecGlue (G := LG.garden) (G₁ := LGZ.garden) (G₂ := LGB.garden) (X := cpair m Qr Qg inner)
    (Fin d → ℤ)
  layZ : ∀ z : GNode LGZ.garden.tree, LGZ.layer z = layerAt LG ((0 : Fin 2), z.1.2)
  layB : ∀ z : GNode LGB.garden.tree, LGB.layer z = layerAt LG (botAddr (cpair m Qr Qg inner).lonePath z.1)

/-- **The decoded instance**: a couple decoded by `type2 (pair m Qr Qg inner rest) Xm Qlp`. -/
theorem Root2Data.of_decodes {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest Xm : RegChain}
    {Qlp : RegCpl} {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2}
    (dec : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).Decodes LG.garden)
    (decZ : (cpair m Qr Qg inner).DecodesTree LGZ.garden) (sigZ : LGZ.garden.sig 0 = 1)
    (decB : (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden)
    (layZ : ∀ z : GNode LGZ.garden.tree, LGZ.layer z = layerAt LG ((0 : Fin 2), z.1.2))
    (layB : ∀ z : GNode LGB.garden.tree, LGB.layer z = layerAt LG (botAddr (cpair m Qr Qg inner).lonePath z.1)) :
    Root2Data LG m Qr Qg inner LGZ LGB :=
  have dec' : (RegCpl.type2 (appendChain (cpair m Qr Qg inner) rest) Xm Qlp).Decodes LG.garden := dec
  ⟨glueData_couple dec' decZ sigZ decB, decZ, dec.1.1, decB.1.1, fun _ => decSplit_couple dec' decZ sigZ decB,
    fun _ => decGlue_couple dec' decZ sigZ decB, layZ, layB⟩

namespace Root2Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D

theorem inl_val (x : GBranch LGZ.garden.tree) : (D.gd.ofSum (.inl x)).1 = ((0 : Fin 2), x.1.2) := rfl

theorem hlone (b : GBranch LG.garden.tree) :
    LG.garden.IsLoneParent b ↔ ∃ y, b = D.gd.ofSum (.inr y) ∧ LGB.garden.IsLoneParent y := by
  constructor
  · intro hb; exact absurd hb (not_loneParent_of_plain D.plain b)
  · rintro ⟨y, -, hy⟩; exact absurd hy (not_loneParent_of_plain D.plainB y)

theorem hl₁ (x : GBranch LGZ.garden.tree) : LGZ.layer x.toNode = LG.layer (D.gd.ofSum (.inl x)).toNode := by
  rw [D.layZ, ← layerAt_node]; rfl

theorem hl₂ (y : GBranch LGB.garden.tree) : LGB.layer y.toNode = LG.layer (D.gd.ofSum (.inr y)).toNode := by
  rw [D.layB, ← layerAt_node]; rfl

include P

/-- The partner `n_b` in the couple. -/
def bR : GBranch LG.garden.tree := D.gd.ofSum (.inl P.hp.bB)

/-- The root `n_1` in the couple. -/
def aR : GBranch LG.garden.tree := D.gd.ofSum (.inl P.hp.rootB)

theorem bR_val : (D.bR P).1 = ((0 : Fin 2), bPath m inner) := rfl

theorem aR_val : (D.aR P).1 = ((0 : Fin 2), []) := rfl

theorem trFix_bR (σ : ℝ) : trFix 0 σ (D.bR P) = none := by
  unfold trFix
  rw [D.bR_val P]
  simp [bPath_ne_nil]

theorem hlone₁ (x : GBranch LGZ.garden.tree) (hx : LGZ.garden.IsLoneParent x) : x = P.hp.bB :=
  P.hp.isLoneParent_G x hx

theorem hpar (x : GBranch LGZ.garden.tree) (y : GBranch LGB.garden.tree)
    (hc : (D.gd.ofSum (.inr y)).IsChildOf (D.gd.ofSum (.inl x))) : x = P.hp.bB := by
  have hy := GlueFix.child_inr_inl D.gd x y hc
  obtain ⟨-, i, hi⟩ := hc
  have hi' : (botAddr (cpair m Qr Qg inner).lonePath y.1).2 = x.1.2 ++ [i] := hi
  rw [hy, cpair_lonePath] at hi'
  simp only [botAddr, ite_true, List.append_nil, lonePos] at hi'
  have hx : x.1.2 = bPath m inner := (List.append_inj' hi' rfl).1.symm
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) hx)

theorem hpar' (y : GBranch LGB.garden.tree) (hy : y.1 = ((0 : Fin 2), [])) :
    (D.gd.ofSum (.inr y)).IsChildOf (D.gd.ofSum (.inl P.hp.bB)) := by
  refine ⟨?_, m.lone, ?_⟩
  · show (botAddr (cpair m Qr Qg inner).lonePath y.1).1 = (0 : Fin 2)
    rw [hy]; simp [botAddr]
  · show (botAddr (cpair m Qr Qg inner).lonePath y.1).2 = (0, bPath m inner).2 ++ [m.lone]
    rw [hy, cpair_lonePath]
    simp [botAddr, lonePos]

/-- The designations after `n_b` is designated at `u`. -/
theorem fix_inl (σ u : ℝ) (x : GBranch LGZ.garden.tree) :
    Function.update (trFix 0 σ) (D.bR P) (some u) (D.gd.ofSum (.inl x)) = pairFix m inner σ u x := by
  by_cases hb : x = P.hp.bB
  · subst hb
    rw [show D.gd.ofSum (.inl P.hp.bB) = D.bR P from rfl, Function.update_self, P.pairFix_bB]
  · rw [Function.update_of_ne (fun he => hb (by simpa [bR] using D.gd.ofSum_injective he))]
    unfold trFix pairFix
    rw [D.inl_val]
    simp only [true_and]
    by_cases h0 : x.1.2 = []
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, if_neg (show ¬ x.1.2 = bPath m inner from
        fun h => hb (Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)))]

theorem fix_inr (σ u : ℝ) (y : GBranch LGB.garden.tree) :
    Function.update (trFix 0 σ) (D.bR P) (some u) (D.gd.ofSum (.inr y)) = none := by
  rw [Function.update_of_ne (fun he => by simpa [bR] using D.gd.ofSum_injective he)]
  unfold trFix
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have h1' : (botAddr (cpair m Qr Qg inner).lonePath y.1).1 = 0 := h1
  have h2' : (botAddr (cpair m Qr Qg inner).lonePath y.1).2 = [] := h2
  obtain ⟨⟨t, q⟩, hq⟩ := y
  by_cases ht : t = 0
  · subst ht
    simp [botAddr, cpair_lonePath, lonePos] at h2'
  · simp [botAddr, ht] at h1'

/-- **The glue step**: with `n_b` designated at `u`, the closing pair and the rest couple split. -/
theorem protTime_glue2 (L γ δ : ℝ) {d : ℕ} (U : Fin 2 → ℝ) (s σ u : ℝ) (hu : u ≤ U 0)
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun b => U b.1.1) s (Function.update (trFix 0 σ) (D.bR P) (some u)) K =
      protTime L γ δ LGZ (fun _ => U 0) s (pairFix m inner σ u) (K ∘ D.gd.ι₁) *
        protTime L γ δ LGB (fun y => bClock U u y.1.1) s (fun _ => none) (K ∘ D.gd.ι₂) := by
  set fix := Function.update (trFix 0 σ) (D.bR P) (some u)
  have hD := fun τ hτ => protDom_glue_free2 D.gd U s s fix P.hp.bB u (Function.update_self _ _ _)
    (D.fix_inr P σ u) hu D.hl₁ D.hl₂ D.hlone (D.hlone₁ P) (D.hpar P) (D.hpar' P) τ hτ
  rw [protTime_glue L γ δ D.gd (fun b => U b.1.1) s fix (fun _ => U 0) s (fun y => bClock U u y.1.1) s K hD]
  congr 2
  · funext x; exact D.fix_inl P σ u x
  · funext y; exact D.fix_inr P σ u y

theorem layer_bR : LG.layer (D.bR P).toNode = layerAt LG ((0 : Fin 2), bPath m inner) := by
  rw [← layerAt_node]; rfl

theorem root2U_sub (U : Fin 2 → ℝ) (s σ : ℝ) :
    root2U LG m inner (U 0) σ ⊆ pinSet LG (fun b => U b.1.1) s (trFix 0 σ) (D.bR P) := by
  rintro u ⟨h1, h2, h3, h4, h5⟩
  refine ⟨by rw [D.layer_bR P]; exact h1, by rw [D.layer_bR P]; exact h2, h3, h4, fun b' hb' σ' hσ' => ?_,
    fun b hb σ' hσ' => ?_, fun hl => absurd hl (not_loneParent_of_plain D.plain _)⟩
  · exfalso
    unfold trFix at hσ'
    split_ifs at hσ' with hp
    obtain ⟨-, i, hi⟩ := hb'
    rw [hp.2] at hi
    have := congrArg List.length hi
    simp at this
  · unfold trFix at hσ'
    split_ifs at hσ' with hp
    rw [← Option.some.inj hσ']
    exact h5

theorem pinSet_lt_root (U : Fin 2 → ℝ) (s σ u : ℝ) (hu : u ∈ pinSet LG (fun b => U b.1.1) s (trFix 0 σ) (D.bR P))
    (hnil : inner.lonePath = []) : u < σ := by
  have hchild : (D.bR P).IsChildOf (D.aR P) := by
    refine ⟨rfl, m.c, ?_⟩
    show bPath m inner = [] ++ [m.c]
    simp [bPath, hnil]
  exact hu.2.2.2.2.2.1 _ hchild σ (by unfold trFix; rw [D.aR_val P]; simp)

/-- **o104 Prop 7.4 (a) for couples, one decoration of times** (`ε = +`). -/
theorem protTime_root2 (L γ δ : ℝ) {d : ℕ} (U : Fin 2 → ℝ) (s σ : ℝ)
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun b => U b.1.1) s (trFix 0 σ) K =
      ∫ u in root2U LG m inner (U 0) σ,
        protTime L γ δ LGZ (fun _ => U 0) s (pairFix m inner σ u) (K ∘ D.gd.ι₁) *
          protTime L γ δ LGB (fun y => bClock U u y.1.1) s (fun _ => none) (K ∘ D.gd.ι₂) := by
  rw [protTime_pin L γ δ LG (fun b => U b.1.1) s (trFix 0 σ) K (D.bR P) (D.trFix_bR P σ),
    ← integral_indicator (measurableSet_root2U LG m inner (U 0) σ)]
  congr 1
  funext u
  by_cases hU : u ∈ root2U LG m inner (U 0) σ
  · rw [Set.indicator_of_mem (D.root2U_sub P U s σ hU), Set.indicator_of_mem hU,
      D.protTime_glue2 P L γ δ U s σ u hU.2.2.2.1.le K]
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun b => U b.1.1) s (trFix 0 σ) (D.bR P)
    · rw [Set.indicator_of_mem hP]
      have hσu : σ ≤ u := by
        by_contra hlt
        exact hU ⟨by rw [← D.layer_bR P]; exact hP.1, by rw [← D.layer_bR P]; exact hP.2.1, hP.2.2.1,
          hP.2.2.2.1, lt_of_not_ge hlt⟩
      have hin : inner.lonePath ≠ [] := fun hnil =>
        absurd (D.pinSet_lt_root P U s σ u hP hnil) (not_lt.mpr hσu)
      rw [D.protTime_glue2 P L γ δ U s σ u hP.2.2.2.1.le K, P.protTime_both_zero L γ δ (U 0) s σ u hσu hin,
        zero_mul]
    · rw [Set.indicator_of_notMem hP]

end Root2Data

end WaveTurbulence.Flower.ProtCut

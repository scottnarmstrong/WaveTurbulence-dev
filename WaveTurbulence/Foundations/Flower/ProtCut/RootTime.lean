/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootGlue

/-! # D2c PROT-CUT: the root pin, at one decoration (o104 Prop 7.4 (a), §13.1; (P1); time level)

A protected tree with code `X = pair m Qr Qg inner rest` (`rest ≠ nil`) has its root `𝔫_1` linked to
`𝔫_b` at `bPath m inner`. `RootData` collects the pieces: the closing pair `Z = pair m Qr Qg inner nil` (top), the
suffix (code `rest`, hanging at `lonePos m inner`), the interior (code `inner`) and the side couples `Qr`, `Qg`.

`protTime_rootCut`: with the root designated at `σ ≤ T`, the free-time integral is
`∫_{u ∈ rootU} (boundary phases at σ, u) · interior(σ, u) · Qr(σ, u) · Qg(σ, u) · suffix(u, s) du`, where
`rootU = (max(𝔏_b, 0), min(𝔏_b + 1, T, σ))`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The root pin: the root designated at `σ`. -/
def rootFix (σ : ℝ) {T : Fin 1 → TTree} (b : GBranch T) : Option ℝ :=
  if b.1.2 = [] then some σ else none

/-- The range of the partner time `u` of the root. -/
def rootU (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ : ℝ) : Set ℝ :=
  {u | (layerAt LG ((0 : Fin 1), bPath m inner) : ℝ) < u ∧ u < layerAt LG ((0 : Fin 1), bPath m inner) + 1 ∧
    0 < u ∧ u < T ∧ u < σ}

theorem measurableSet_rootU (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ : ℝ) :
    MeasurableSet (rootU LG m inner T σ) := by
  unfold rootU
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter
        ((measurableSet_lt measurable_id measurable_const).inter
          (measurableSet_lt measurable_id measurable_const))))

/-- **The pieces of a root-pinned protected tree** (o104 Prop 7.4 (a)). -/
structure RootData (LG : LayeredGarden 1) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain)
    (LGZ LGi LGs : LayeredGarden 1) (LGr LGg : LayeredGarden 2) : Prop where
  dec : (RegChain.pair m Qr Qg inner rest).DecodesTree LG.garden
  rest_ne : rest ≠ .nil
  decZ : (cpair m Qr Qg inner).DecodesTree LGZ.garden
  sigZ : LGZ.garden.sig 0 = LG.garden.sig 0
  decS : rest.DecodesTree LGs.garden
  sigS : LGs.garden.sig 0 = LG.garden.sig 0
  decI : inner.DecodesTree LGi.garden
  sigI : LGi.garden.sig 0 = slotSign (LG.garden.sig 0) m.c
  decR : Qr.Decodes LGr.garden
  decG : Qg.Decodes LGg.garden
  layZ : ∀ z : GNode LGZ.garden.tree, LGZ.layer z = layerAt LG ((0 : Fin 1), z.1.2)
  layS : ∀ z : GNode LGs.garden.tree, LGs.layer z = layerAt LG ((0 : Fin 1), lonePos m inner ++ z.1.2)
  layI : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt LG ((0 : Fin 1), m.c :: z.1.2)
  layR : ∀ z : GNode LGr.garden.tree,
    LGr.layer z = layerAt LG ((0 : Fin 1), rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)
  layG : ∀ z : GNode LGg.garden.tree,
    LGg.layer z = layerAt LG ((0 : Fin 1), gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

theorem dec' : (appendChain (cpair m Qr Qg inner) rest).DecodesTree LG.garden := D.dec

/-- The gluing of the closing pair (top) and the suffix (bottom). -/
theorem gd : GlueData LG.garden LGZ.garden LGs.garden (cpair m Qr Qg inner) :=
  glueData_tree D.dec' D.decZ D.sigZ D.decS D.sigS

/-- The closing pair and its three pieces. -/
theorem hp : PairData m Qr Qg inner LGZ.garden LGi.garden LGr.garden LGg.garden :=
  ⟨D.decZ, D.decI, by rw [D.sigI, D.sigZ], D.decR, D.decG⟩

/-- The root `𝔫_1` (`= 𝔫_a`) in the protected tree. -/
def aR : GBranch LG.garden.tree := D.gd.ofSum (.inl D.hp.rootB)

/-- The partner `𝔫_b` in the protected tree. -/
def bR : GBranch LG.garden.tree := D.gd.ofSum (.inl D.hp.bB)

theorem aR_path : D.aR.1 = ((0 : Fin 1), []) := rfl

theorem bR_path : D.bR.1 = ((0 : Fin 1), bPath m inner) := rfl

theorem rootFix_aR (σ : ℝ) : rootFix σ D.aR = some σ := by
  unfold rootFix
  exact if_pos rfl

theorem rootFix_bR (σ : ℝ) : rootFix σ D.bR = none := by
  unfold rootFix
  exact if_neg (by rw [D.bR_path]; exact bPath_ne_nil m inner)

theorem inr_path (y : GBranch LGs.garden.tree) :
    (D.gd.ofSum (.inr y)).1 = ((0 : Fin 1), lonePos m inner ++ y.1.2) := by
  rw [glue_ofSum_inr_path D.gd, cpair_lonePath]

/-! ### Lone parents -/

omit D in
theorem lonePath_eq : (RegChain.pair m Qr Qg inner rest).lonePath = lonePos m inner ++ rest.lonePath := by
  rw [show RegChain.pair m Qr Qg inner rest = appendChain (cpair m Qr Qg inner) rest from rfl,
    appendChain_lonePath, cpair_lonePath]

theorem rest_lonePath_ne : rest.lonePath ≠ [] := by
  intro h
  cases rest with
  | nil => exact D.rest_ne rfl
  | pair => simp [RegChain.lonePath] at h

theorem top_not_prefix (x : GBranch LGZ.garden.tree) : ¬ (cpair m Qr Qg inner).lonePath <+: x.1.2 := by
  have hm := x.2
  rw [show x.1.1 = 0 from Subsingleton.elim _ _] at hm
  exact ((D.gd.top_branch_iff _).mp hm).2

theorem hlone (b : GBranch LG.garden.tree) :
    LG.garden.IsLoneParent b ↔ ∃ y, b = D.gd.ofSum (.inr y) ∧ LGs.garden.IsLoneParent y := by
  constructor
  · rintro ⟨ℓ, hℓ, -, i, hi⟩
    have hpath : ℓ.1.2 = lonePos m inner ++ rest.lonePath := by
      by_contra hne
      unfold Garden.IsLone at hℓ
      rw [D.dec.2.1 ℓ, (lonePath_eq (m := m) (Qr := Qr) (Qg := Qg) (inner := inner) (rest := rest)), ite_eq_right hne] at hℓ
      exact absurd hℓ (by simp)
    obtain ⟨q, j, hq⟩ := (List.eq_nil_or_concat rest.lonePath).resolve_left D.rest_lonePath_ne
    rw [hq, List.concat_eq_append, ← List.append_assoc] at hpath
    have hb : b.1.2 = lonePos m inner ++ q := (List.append_inj' (hi.symm.trans hpath) rfl).1
    rcases hc : D.gd.toSum b with x | y
    · exfalso
      have he := D.gd.ofSum_toSum b
      rw [hc] at he
      have hx := D.top_not_prefix x
      have : x.1.2 = b.1.2 := by rw [← he]; rfl
      rw [cpair_lonePath, this, hb] at hx
      exact hx (List.prefix_append _ _)
    · have he := D.gd.ofSum_toSum b
      rw [hc] at he
      refine ⟨y, he.symm, ?_⟩
      have hy : y.1.2 = q := by
        have := congrArg (fun z : GBranch LG.garden.tree => z.1.2) he
        simp only [D.inr_path] at this
        exact List.append_cancel_left (this.trans hb)
      have hmem : rest.lonePath ∈ (LGs.garden.tree 0).leaves := by
        rw [D.decS.1]; exact lonePath_mem_leaves _ _
      refine ⟨⟨((0 : Fin 1), rest.lonePath), hmem⟩, ?_, Subsingleton.elim _ _, j, ?_⟩
      · unfold Garden.IsLone
        exact (D.decS.2.1 _).trans (by simp)
      · show rest.lonePath = y.1.2 ++ [j]
        rw [hy, hq, List.concat_eq_append]
  · rintro ⟨y, rfl, ℓ', hℓ', -, j, hj⟩
    have hpath : ℓ'.1.2 = rest.lonePath := by
      by_contra hne
      unfold Garden.IsLone at hℓ'
      rw [D.decS.2.1 ℓ', ite_eq_right hne] at hℓ'
      exact absurd hℓ' (by simp)
    have hmem : lonePos m inner ++ rest.lonePath ∈ (LG.garden.tree 0).leaves := by
      rw [← (lonePath_eq (m := m) (Qr := Qr) (Qg := Qg) (inner := inner) (rest := rest)), D.dec.1]; exact lonePath_mem_leaves _ _
    refine ⟨⟨((0 : Fin 1), lonePos m inner ++ rest.lonePath), hmem⟩, ?_, Subsingleton.elim _ _, j, ?_⟩
    · unfold Garden.IsLone
      exact (D.dec.2.1 _).trans (by rw [(lonePath_eq (m := m) (Qr := Qr) (Qg := Qg) (inner := inner) (rest := rest))]; simp)
    · show lonePos m inner ++ rest.lonePath = (D.gd.ofSum (.inr y)).1.2 ++ [j]
      rw [D.inr_path, ← hpath, hj]
      simp

theorem hlone₁ (x : GBranch LGZ.garden.tree) (hx : LGZ.garden.IsLoneParent x) : x = D.hp.bB :=
  D.hp.isLoneParent_G x hx

theorem hpar (x : GBranch LGZ.garden.tree) (y : GBranch LGs.garden.tree)
    (hc : (D.gd.ofSum (.inr y)).IsChildOf (D.gd.ofSum (.inl x))) : x = D.hp.bB := by
  have hy := GlueFix.child_inr_inl D.gd x y hc
  obtain ⟨-, i, hi⟩ := hc
  rw [D.inr_path] at hi
  have hy2 : y.1.2 = [] := congrArg Prod.snd hy
  simp only [hy2, List.append_nil, lonePos] at hi
  have hx : x.1.2 = bPath m inner := by
    have := (List.append_inj' hi rfl).1
    exact this.symm
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) hx)

theorem hpar' (y : GBranch LGs.garden.tree) (hy : y.1.2 = []) :
    (D.gd.ofSum (.inr y)).IsChildOf (D.gd.ofSum (.inl D.hp.bB)) := by
  refine ⟨Subsingleton.elim _ _, m.lone, ?_⟩
  rw [D.inr_path, hy]
  simp [lonePos, PairData.bB, GlueData.ofSum, topAddr]

/-! ### The glue step -/

/-- The designations after `𝔫_b` is designated at `u`. -/
def fixU (σ u : ℝ) : GBranch LG.garden.tree → Option ℝ := Function.update (rootFix σ) D.bR (some u)

theorem fixU_bR (σ u : ℝ) : D.fixU σ u D.bR = some u := Function.update_self _ _ _

theorem fixU_aR (σ u : ℝ) : D.fixU σ u D.aR = some σ := by
  unfold fixU
  rw [Function.update_of_ne, D.rootFix_aR]
  intro he
  have := congrArg (fun b : GBranch LG.garden.tree => b.1.2) he
  simp only [D.aR_path, D.bR_path] at this
  exact bPath_ne_nil m inner this.symm

theorem fixU_inr (σ u : ℝ) (y : GBranch LGs.garden.tree) : D.fixU σ u (D.gd.ofSum (.inr y)) = none := by
  have hne : D.gd.ofSum (.inr y) ≠ D.bR := by
    intro he
    have := congrArg (fun b : GBranch LG.garden.tree => b.1.2) he
    simp only [D.inr_path, D.bR_path] at this
    have h2 := congrArg List.length this
    simp [lonePos, bPath] at h2
  unfold fixU
  rw [Function.update_of_ne hne]
  unfold rootFix
  rw [if_neg]
  rw [D.inr_path]
  simp [lonePos]

theorem fixU_inl (σ u : ℝ) (x : GBranch LGZ.garden.tree) (h1 : x ≠ D.hp.rootB) (h2 : x ≠ D.hp.bB) :
    D.fixU σ u (D.gd.ofSum (.inl x)) = none := by
  have hne : D.gd.ofSum (.inl x) ≠ D.bR := by
    intro he
    exact h2 (by simpa using D.gd.ofSum_injective he)
  unfold fixU
  rw [Function.update_of_ne hne]
  unfold rootFix
  rw [if_neg]
  intro hx
  exact h1 (Subtype.ext (Prod.ext (Subsingleton.elim _ _) hx))

theorem hl₁ (x : GBranch LGZ.garden.tree) : LGZ.layer x.toNode = LG.layer (D.gd.ofSum (.inl x)).toNode := by
  rw [D.layZ, ← layerAt_node]
  rfl

theorem hl₂ (y : GBranch LGs.garden.tree) : LGs.layer y.toNode = LG.layer (D.gd.ofSum (.inr y)).toNode := by
  rw [D.layS, ← layerAt_node]
  exact congrArg (layerAt LG) (D.inr_path y).symm

theorem protTime_glueR (L γ δ : ℝ) {d : ℕ} (T s σ u : ℝ) (huT : u ≤ T) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s (D.fixU σ u) K =
      protTime L γ δ LGZ (fun _ => T) s (fun x => D.fixU σ u (D.gd.ofSum (.inl x))) (K ∘ D.gd.ι₁) *
        protTime L γ δ LGs (fun _ => u) s (fun _ => none) (K ∘ D.gd.ι₂) := by
  have hD := fun τ hτ => protDom_glue_free D.gd (fun _ => T) s s (D.fixU σ u) D.hp.bB u (D.fixU_bR σ u)
    (D.fixU_inr σ u) (fun _ => huT) D.hl₁ D.hl₂ D.hlone D.hlone₁ D.hpar D.hpar' τ hτ
  rw [protTime_glue L γ δ D.gd (fun _ => T) s (D.fixU σ u) (fun _ => T) s (fun _ => u) s K hD]
  congr 2
  funext y
  exact D.fixU_inr σ u y

/-! ### The pair step -/

theorem hli (z : GNode LGi.garden.tree) : LGi.layer z = LGZ.layer (D.hp.ιi z) := by
  rw [D.layI, D.layZ]; rfl

theorem hlr (z : GNode LGr.garden.tree) : LGr.layer z = LGZ.layer (D.hp.ιr z) := by
  rw [D.layR, D.layZ, ← D.sigZ]; rfl

theorem hlg (z : GNode LGg.garden.tree) : LGg.layer z = LGZ.layer (D.hp.ιg z) := by
  rw [D.layG, D.layZ, ← D.sigZ]; rfl

theorem fixZ_rootB (σ u : ℝ) : D.fixU σ u (D.gd.ofSum (.inl D.hp.rootB)) = some σ := D.fixU_aR σ u

theorem fixZ_bB (σ u : ℝ) : D.fixU σ u (D.gd.ofSum (.inl D.hp.bB)) = some u := D.fixU_bR σ u

theorem pb_ne {z z' : Fin 2 ⊕ (GBranch LGi.garden.tree ⊕ (GBranch LGr.garden.tree ⊕ GBranch LGg.garden.tree))}
    (hz : z ≠ z') : D.hp.pairBranch z ≠ D.hp.pairBranch z' := D.hp.pairBranch_injective.ne hz

theorem fixZ_βi (σ u : ℝ) (x : GBranch LGi.garden.tree) : D.fixU σ u (D.gd.ofSum (.inl (D.hp.βi x))) = none :=
  D.fixU_inl σ u _ (D.pb_ne (z := .inr (.inl x)) (z' := .inl 0) (by simp))
    (D.pb_ne (z := .inr (.inl x)) (z' := .inl 1) (by simp))

theorem fixZ_βr (σ u : ℝ) (y : GBranch LGr.garden.tree) : D.fixU σ u (D.gd.ofSum (.inl (D.hp.βr y))) = none :=
  D.fixU_inl σ u _ (D.pb_ne (z := .inr (.inr (.inl y))) (z' := .inl 0) (by simp))
    (D.pb_ne (z := .inr (.inr (.inl y))) (z' := .inl 1) (by simp))

theorem fixZ_βg (σ u : ℝ) (y : GBranch LGg.garden.tree) : D.fixU σ u (D.gd.ofSum (.inl (D.hp.βg y))) = none :=
  D.fixU_inl σ u _ (D.pb_ne (z := .inr (.inr (.inr y))) (z' := .inl 0) (by simp))
    (D.pb_ne (z := .inr (.inr (.inr y))) (z' := .inl 1) (by simp))

theorem protTime_pairR (L γ δ : ℝ) {d : ℕ} (T s σ u : ℝ) (hσT : σ ≤ T) (huT : u ≤ T)
    (K : GNode LGZ.garden.tree → Mom d) :
    protTime L γ δ LGZ (fun _ => T) s (fun x => D.fixU σ u (D.gd.ofSum (.inl x))) K =
      Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LGZ.garden K D.hp.rootB * σ : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LGZ.garden K D.hp.bB * u : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => σ) u (fun _ => none) (K ∘ D.hp.ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
              (K ∘ D.hp.ιr) *
            protTime L γ δ LGg (fun y => cupG m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
              (K ∘ D.hp.ιg))) := by
  have e := PairData.protTime_pair (LG := LGZ) D.hp L γ δ T s σ u (fun x => D.fixU σ u (D.gd.ofSum (.inl x)))
    (D.fixZ_rootB σ u) (D.fixZ_bB σ u) D.hli D.hlr D.hlg hσT huT
    (fun x τ hx => by simp only [D.fixZ_βi] at hx; simp at hx)
    (fun y τ hy => by simp only [D.fixZ_βr] at hy; simp at hy)
    (fun y τ hy => by simp only [D.fixZ_βg] at hy; simp at hy) K
  rw [e]
  have h1 : (fun x => D.fixU σ u (D.gd.ofSum (.inl (D.hp.βi x)))) = fun _ => none := funext (D.fixZ_βi σ u)
  have h2 : (fun y => D.fixU σ u (D.gd.ofSum (.inl (D.hp.βr y)))) = fun _ => none := funext (D.fixZ_βr σ u)
  have h3 : (fun y => D.fixU σ u (D.gd.ofSum (.inl (D.hp.βg y)))) = fun _ => none := funext (D.fixZ_βg σ u)
  rw [h1, h2, h3]

end RootData

end WaveTurbulence.Flower.ProtCut

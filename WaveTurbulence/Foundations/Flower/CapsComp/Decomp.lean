/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Classes
public import WaveTurbulence.Foundations.Flower.CapsId.Card
/-! # A3b CAPS-COMP: the structure of a capped garden, and the forward half of the carrier bijection

* `xmapG N G`: the structure of a capped garden (least tree of each component, component orders).
* `strSet`: the structures realized by the flower carrier; each is valid (`valid_of_mem`).
* `classX x hx c`: the class of component `c` of the structure `x` (supplement Lemma 2.1(2)–(4)).
* `fwd_mem_classX`: the components of the capped garden of a carrier member lie in the classes of its structure. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine

/-! ## Generic facts on glues and structures -/

theorem sig_glueN {m w : ℕ} {a : Fin m → ℕ} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (c : Fin m) (i : Fin (a c)) : (glueL σ LA).garden.sig (σ ⟨c, i⟩) = (LA c).garden.sig i := by
  show gSigN σ (fun c => (LA c).garden.sig) (σ ⟨c, i⟩) = _
  unfold gSigN
  rw [Equiv.symm_apply_apply]

theorem tree_glueN {m w : ℕ} {a : Fin m → ℕ} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (c : Fin m) (i : Fin (a c)) : (glueL σ LA).garden.tree (σ ⟨c, i⟩) = (LA c).garden.tree i :=
  gT_apply σ (fun c => (LA c).garden.tree) c i

theorem sum_blockOf {m w : ℕ} {a : Fin m → ℕ} {M : Type*} [AddCommMonoid M]
    (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (c : Fin m) (f : Fin w → M) :
    ∑ k ∈ blockOf σ c, f k = ∑ i, f (σ ⟨c, i⟩) := by
  unfold blockOf
  rw [sum_image]
  intro i _ i' _ e
  have := σ.injective e
  simpa using this

theorem mem_blockOf_iff {m w : ℕ} {a : Fin m → ℕ} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (c : Fin m)
    (k : Fin w) : k ∈ blockOf σ c ↔ ∃ i, σ ⟨c, i⟩ = k := by
  simp [blockOf]

theorem order_glue_piece {m w : ℕ} {a : Fin m → ℕ} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w)
    (LA : ∀ c, LayeredGarden (a c)) (c : Fin m) :
    ∑ k ∈ blockOf σ c, ((glueL σ LA).garden.tree k).order = (LA c).garden.order := by
  rw [sum_blockOf]
  unfold Garden.order
  exact Finset.sum_congr rfl fun i _ => by rw [tree_glueN]

namespace RawStr

variable {w N : ℕ} (x : RawStr w N)

theorem repAt_mem_blk (c : Fin x.m) : x.repAt c ∈ x.blk c := by
  rw [mem_blk]; exact x.repAt_mem c

theorem repAt_le (hx : ValidStr x) (c : Fin x.m) {k : Fin (2 * w)} (hk : k ∈ x.blk c) : x.repAt c ≤ k := by
  rw [mem_blk] at hk
  rw [← hk]; exact hx.le k

theorem repAt_orig (hx : ValidStr x) (c : Fin x.m) : ∃ j, x.repAt c = capσ w (.inl j) := by
  obtain ⟨s, hs⟩ := (capσ w).surjective (x.repAt c)
  rcases s with j | j
  · exact ⟨j, hs.symm⟩
  · exfalso
    have h1 := x.repAt_mem c
    rw [← hs, ← hx.mate] at h1
    have h2 := hx.le (capσ w (.inl j))
    rw [h1] at h2
    have : (w + j : ℕ) ≤ j := h2
    omega

theorem card_caps_blk (hx : ValidStr x) (c : Fin x.m) :
    ((x.blk c).filter (· ∈ capJ w)).card = x.R c := by
  have h := x.two_R hx c
  have h2 := x.card_blk_eq hx c
  have hs := Finset.card_filter_add_card_filter_not (s := x.blk c) (fun i : Fin (2 * w) => (i : ℕ) < w)
  have e : (x.blk c).filter (· ∈ capJ w) = (x.blk c).filter fun i : Fin (2 * w) => ¬ (i : ℕ) < w := by
    ext i; simp [capJ]
  rw [e]
  omega

theorem card_resJ (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ) (c : Fin x.m) :
    (resJ (x.sigmaX hx sgn) (capJ w) c).card = x.R c := by
  refine Eq.trans ?_ (x.card_caps_blk hx c)
  rw [← x.blockOf_sigmaX hx sgn c]
  unfold resJ blockOf
  rw [← Finset.card_image_of_injective _ (f := fun i => x.sigmaX hx sgn ⟨c, i⟩) (fun i i' e => by
    have := (x.sigmaX hx sgn).injective e; simpa using this)]
  congr 1
  ext k
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
  · rintro ⟨⟨i, rfl⟩, hi⟩; exact ⟨i, hi, rfl⟩

theorem one_le_R (hx : ValidStr x) (c : Fin x.m) : 1 ≤ x.R c := by
  have h := x.two_R hx c
  have : 0 < (x.blk c).card := Finset.card_pos.2 ⟨_, x.repAt_mem_blk c⟩
  omega

end RawStr

/-! ## The structure of a capped garden -/

section Xmap

variable {w : ℕ}

/-- The order of the component of tree `i`. -/
def compOrder (G : Garden (2 * w)) (i : Fin (2 * w)) : ℕ := ∑ k ∈ compOf G i, (G.tree k).order

/-- The structure of a capped garden. -/
def xmapG (N : ℕ) (G : Garden (2 * w)) : RawStr w N :=
  (rep G, fun j => if rep G (capσ w (.inl j)) = capσ w (.inl j) then
    ⟨min N (compOrder G (capσ w (.inl j))), Nat.lt_succ_of_le (min_le_left _ _)⟩ else 0)

theorem compOf_inr_eq_inl {G : Garden (2 * w)} (hG : CapShape G) (j : Fin w) :
    compOf G (capσ w (.inr j)) = compOf G (capσ w (.inl j)) := by
  have hleaf : ([] : Path) ∈ (G.tree (capσ w (.inr j))).leaves := by rw [hG.capLeaf j]; simp [TTree.leaves]
  let ℓ : GLeaf G.tree := ⟨(capσ w (.inr j), []), hleaf⟩
  have hmem : capσ w (.inl j) ∈ compOf G (capσ w (.inr j)) := by
    rw [mem_compOf]
    intro T hT hi
    rw [← hG.capPair ℓ j rfl]
    exact (closedTrees_iff G hG.plain T).1 hT ℓ hi
  exact (compOf_eq_of_mem hG.plain hmem).symm

theorem validStr_xmapG (N : ℕ) {G : Garden (2 * w)} (hG : CapShape G) : ValidStr (xmapG N G) :=
  ⟨rep_rep hG.plain, rep_le G, fun j => (rep_eq_of_compOf_eq (compOf_inr_eq_inl hG j)).symm⟩

/-- For a capped garden with structure `x`, the component of a tree listed at `⟨c, i⟩` is the block of `c`. -/
theorem compOf_eq_blockOf {N : ℕ} (x : RawStr w N) (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ)
    {G : Garden (2 * w)} (hpl : G.IsPlain) (hrep : rep G = x.1) (c : Fin x.m) (i : Fin (2 * x.R c)) :
    compOf G (x.sigmaX hx sgn ⟨c, i⟩) = blockOf (x.sigmaX hx sgn) c := by
  ext k
  rw [mem_compOf_iff_rep hpl, hrep, x.rep_sigmaX hx sgn, x.blockOf_sigmaX hx sgn, RawStr.mem_blk]

theorem blocks_closed {N : ℕ} (x : RawStr w N) (hx : ValidStr x) (sgn : Fin (2 * w) → ℤˣ)
    {G : Garden (2 * w)} (hpl : G.IsPlain) (hrep : rep G = x.1) :
    ∀ (ℓ : GLeaf G.tree) (c : Fin x.m) (i : Fin (2 * x.R c)), ℓ.1.1 = x.sigmaX hx sgn ⟨c, i⟩ →
      ∃ i' : Fin (2 * x.R c), (G.pair ℓ).1.1 = x.sigmaX hx sgn ⟨c, i'⟩ := by
  intro ℓ c i hi
  have h1 : (G.pair ℓ).1.1 ∈ compOf G ℓ.1.1 :=
    (closedTrees_iff G hpl _).1 (closedTrees_compOf hpl ℓ.1.1) ℓ (self_mem_compOf G _)
  rw [hi, compOf_eq_blockOf x hx sgn hpl hrep, mem_blockOf_iff] at h1
  obtain ⟨i', hi'⟩ := h1
  exact ⟨i', hi'.symm⟩

end Xmap

/-! ## The setting: the carrier, its structures, the classes -/

section Setting

variable {w : ℕ} (P : WTParams) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat) (ζ : ℤˣ)

/-- The carrier as a finset. -/
def carrierF : Finset (LayeredGarden w) := (FC23.flowerCarrier_finite P p N kind pat ζ).toFinset

/-- The structure of a carrier member. -/
def xF (LG : LayeredGarden w) : RawStr w N := xmapG N (capLayered LG p).garden

/-- The structures realized by the carrier. -/
def strSet : Finset (RawStr w N) := (carrierF P p N kind pat ζ).image (xF p N)

variable {P p N kind pat ζ}

theorem valid_of_mem {x : RawStr w N} (hx : x ∈ strSet P p N kind pat ζ) : ValidStr x := by
  obtain ⟨LG, hLG, rfl⟩ := mem_image.1 hx
  have hc := (Set.Finite.mem_toFinset _).1 hLG
  exact validStr_xmapG N (capGlob_of_mem_carrier P p N kind pat ζ hc).2.2.1

variable (P p N kind pat ζ)

/-- The partner rule of component `c`: the cap listed at `i` is paired into the original tree of the same index. -/
def matchX (x : RawStr w N) (hx : ValidStr x) (c : Fin x.m) : Fin (2 * x.R c) → Fin (2 * x.R c) → Prop :=
  fun i i' => x.sigmaX hx (capSgn ζ) ⟨c, i'⟩ = capσ w (.inl (origIdx (x.sigmaX hx (capSgn ζ) ⟨c, i⟩)))

/-- **The class of component `c` of the structure `x`.** -/
def classX (x : RawStr w N) (hx : ValidStr x) (c : Fin x.m) : Finset (LayeredGarden (2 * x.R c)) :=
  classOf P p (x.n c) (P.N (p + 1)) kind (resF (x.sigmaX hx (capSgn ζ)) (capSgn ζ) c)
    (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) (matchX N ζ x hx c)
    (resF (x.sigmaX hx (capSgn ζ)) (capExt pat .plain) c)

variable {P p N kind pat ζ}

theorem capSgn_of_glob {G : LayeredGarden (2 * w)} (hsi : ∀ j : Fin w, G.garden.sig (capσ w (.inl j)) = (-1) ^ (j : ℕ))
    (hsc : ∀ j : Fin w, G.garden.sig (capσ w (.inr j)) = -(ζ * (-1) ^ (j : ℕ))) (y : Fin (2 * w)) :
    G.garden.sig y = capSgn ζ y := by
  obtain ⟨s, rfl⟩ := (capσ w).surjective y
  rcases s with j | j
  · rw [hsi, capSgn_inl]
  · rw [hsc, capSgn_inr]

/-- Two `±1` units summing to zero are opposite. -/
theorem units_opp_of_sum {a b : ℤˣ} (h : (a : ℤ) + (b : ℤ) = 0) : a = -b := by
  rcases Int.units_eq_one_or a with ha | ha <;> rcases Int.units_eq_one_or b with hb | hb <;>
    subst ha <;> subst hb <;> simp_all

theorem sum_fin_two_of_eq {n : ℕ} (hn : n = 2) (f : Fin n → ℤ) :
    ∑ i, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  subst hn
  rw [Fin.sum_univ_two]; rfl

/-- **Forward half**: the components of the capped garden of a carrier member lie in the classes. -/
theorem fwd_mem_classX (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) {LG : LayeredGarden w}
    (hLG : LG ∈ carrierF P p N kind pat ζ) {x : RawStr w N} (hxL : xF p N LG = x) (hx : ValidStr x)
    {G : ∀ c : Fin x.m, LayeredGarden (2 * x.R c)}
    (hG : glueL (x.sigmaX hx (capSgn ζ)) G = capLayered LG p) (c : Fin x.m) :
    G c ∈ classX P p N kind pat ζ x hx c := by
  have hc := (Set.Finite.mem_toFinset _).1 hLG
  obtain ⟨_, _, hshape, hglob⟩ := capGlob_of_mem_carrier P p N kind pat ζ hc
  set σ := x.sigmaX hx (capSgn ζ) with hσ
  have hrep : rep (capLayered LG p).garden = x.1 := by rw [← hxL]; rfl
  have hcomp := compOf_eq_blockOf x hx (capSgn ζ) hshape.plain hrep
  have hx2 : ∀ j, x.2 j = (xF p N LG).2 j := fun j => by rw [hxL]
  rw [← hG] at hshape hglob hcomp hrep
  obtain ⟨hcrit, hord, hsi, hsc, hlab⟩ := hglob
  have hpl : (glueL σ G).garden.IsPlain := hshape.plain
  have hsg : ∀ y, (glueL σ G).garden.sig y = capSgn ζ y := capSgn_of_glob hsi hsc
  have hsigc : (G c).garden.sig = resF σ (capSgn ζ) c := by
    funext i; rw [← sig_glueN σ G c i, hsg]; rfl
  -- balance of the block
  have hbal : ∑ i, (((G c).garden.sig i : ℤˣ) : ℤ) = 0 := by
    have hcl : ClosedTrees (glueL σ G).garden (blockOf σ c) := closedTrees_blockOf σ G hpl c
    have := balanced_of_closed _ _ hcl
    rw [sum_blockOf] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [sig_glueN]
  -- the order of the component
  have hordc : (G c).garden.order = x.n c := by
    obtain ⟨j0, hj0⟩ := x.repAt_orig hx c
    have hrj : rep (glueL σ G).garden (capσ w (.inl j0)) = capσ w (.inl j0) := by
      rw [hrep, ← hj0]; exact x.repAt_mem c
    have hmemb : x.repAt c ∈ blockOf σ c := by rw [x.blockOf_sigmaX]; exact x.repAt_mem_blk c
    obtain ⟨i0, hi0⟩ := (mem_blockOf_iff σ c _).1 hmemb
    have hco : compOrder (glueL σ G).garden (capσ w (.inl j0)) = (G c).garden.order := by
      unfold compOrder
      rw [← hj0, ← hi0, hcomp c i0, order_glue_piece]
    have hle : (G c).garden.order ≤ N := by
      refine le_trans ?_ hord.le
      rw [glueN_order]
      exact Finset.single_le_sum (f := fun c => (G c).garden.order) (fun _ _ => Nat.zero_le _) (mem_univ c)
    unfold RawStr.n
    rw [hj0, origIdx_inl, hx2 j0]
    show _ = ((if rep (capLayered LG p).garden (capσ w (.inl j0)) = capσ w (.inl j0) then
      (⟨min N (compOrder (capLayered LG p).garden (capσ w (.inl j0))), _⟩ : Fin (N + 1)) else 0 : Fin (N + 1)) : ℕ)
    rw [← hG, ite_eq_left hrj]
    show (G c).garden.order = min N (compOrder (glueL σ G).garden (capσ w (.inl j0)))
    rw [hco]
    exact (min_eq_right hle).symm
  have hR1 : 1 ≤ x.R c := x.one_le_R hx c
  unfold classX
  rw [mem_classOf]
  refine ⟨⟨⟨⟨(isPlain_glueN σ G).1 hpl c, ?_, (canonCriterion_glueN σ G p).1 hcrit c⟩, ?_, hordc, hbal⟩,
    hsigc⟩, ?_, ?_, ?_⟩
  · by_cases h4 : 4 ≤ 2 * x.R c
    · exact Or.inl ⟨h4, irreducible_of_compOf σ G hpl hcomp c⟩
    · have hR : x.R c = 1 := by omega
      refine Or.inr ⟨by omega, ?_⟩
      have hs2 := sum_fin_two_of_eq (by omega : 2 * x.R c = 2) (fun i => (((G c).garden.sig i : ℤˣ) : ℤ))
      rw [hbal] at hs2
      have hopp := units_opp_of_sum hs2.symm
      have h0 : (G c).garden.sig ⟨0, by omega⟩ = 1 := by
        rw [hsigc]
        refine x.sgn_sigmaX_zero hx (capSgn ζ) c hR fun k k' hkk' => ?_
        have e1 : ∀ k : Fin (2 * x.R c), k = ⟨0, by omega⟩ ∨ k = ⟨1, by omega⟩ := fun k => by
          rcases k with ⟨k, hk⟩
          rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp
        rw [← hσ, ← hsg, ← hsg, sig_glueN, sig_glueN]
        rcases e1 k with rfl | rfl <;> rcases e1 k' with rfl | rfl
        · exact absurd rfl hkk'
        · exact hopp
        · rw [hopp]; simp
        · exact absurd rfl hkk'
      intro i
      rcases i with ⟨i, hi⟩
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [h0]; simp
      · have : (G c).garden.sig ⟨1, hi⟩ = -1 := by
          have h0' : (G c).garden.sig ⟨0, by omega⟩ = -(G c).garden.sig ⟨1, by omega⟩ := hopp
          rw [h0] at h0'
          have := congrArg Neg.neg h0'
          simpa using this.symm
        rw [this]; simp
  · show (G c).IsTrunc p (P.N (p + 1) ^ 4) (P.N p)
    have hle : (G c).garden.order ≤ N := by
      refine le_trans ?_ hord.le
      rw [glueN_order]
      exact Finset.single_le_sum (f := fun c => (G c).garden.order) (fun _ _ => Nat.zero_le _) (mem_univ c)
    rw [LFTwist.trunc_iff_topOrder _ _ _ _ (hle.trans (hN.trans (N_fourth_le_N P hp)))]
    exact fun i => ((G c).topOrder_le_order p i).trans (hle.trans hN)
  · intro i hi
    rw [mem_resJ, mem_capJ_iff] at hi
    obtain ⟨j, hj⟩ := hi
    rw [← tree_glueN σ G c i, hj]
    exact hshape.capLeaf j
  · intro ℓ hℓ
    rw [mem_resJ, mem_capJ_iff] at hℓ
    obtain ⟨j, hj⟩ := hℓ
    have := hshape.capPair (glueLeafN σ (fun c => (G c).garden.tree) ⟨c, ℓ⟩) j (by rw [glueLeafN_val]; exact hj)
    rw [show (glueL σ G).garden.pair = (glueGardenN σ fun c => (G c).garden).pair from rfl, glueN_pair_leaf,
      glueLeafN_val] at this
    have this' : σ ⟨c, ((G c).garden.pair ℓ).1.1⟩ = capσ w (.inl j) := this
    show σ ⟨c, ((G c).garden.pair ℓ).1.1⟩ = capσ w (.inl (origIdx (σ ⟨c, ℓ.1.1⟩)))
    rw [this', hj, origIdx_inr]
  · intro i hi
    rw [mem_resJ, mem_capJ_iff] at hi
    obtain ⟨s, hs⟩ := (capσ w).surjective (σ ⟨c, i⟩)
    rcases s with j | j
    · have hJ : resJ σ (capJ w) c = resJ σ (capJ w) c := rfl
      obtain ⟨h1, h2, h3⟩ := hlab j
      rw [hs] at h1 h2 h3
      refine ⟨(capStem_glueN σ G (capJ w) p c i).1 h1, (capKindOK_glueN σ G (capJ w) p _ c i kind).1 h2, ?_⟩
      have := (capPatExist_glueN σ G (capJ w) p c i (pat j)).1 h3
      show CapPatExist (G c) (resJ σ (capJ w) c) p i (capExt pat .plain (σ ⟨c, i⟩))
      rw [← hs, capExt_inl]
      exact this
    · exact absurd ⟨j, hs.symm⟩ hi

end Setting

end WaveTurbulence.Flower.CapsComp

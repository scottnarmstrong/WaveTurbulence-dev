/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentObjects
/-! Explicit coherent approximations from TARGET L1235–1246, (prooflayer1-1–2), using only
single-layer RegCpl.app / RegChain.app from (regref1-3). The chain slices are the consecutive
same-layer blocks described at L1236. No approximation function is supplied as data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceApp
open Finset TTree WaveTurbulence.Reg WaveTurbulence.Links

/-- TARGET L1236: retain the consecutive chain pairs in layer r. In a coherent embedding the
inner chain and the two attached couples of a retained pair are in the same layer, by layerreg1.
Only the continuation after that pair can descend to a lower layer. -/
def chainSlice {w : ℕ} (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) : RegChain → RegChain
  | .nil => .nil
  | .pair m Qr Qg inner rest =>
      let a' := addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])
      if layerAt LG a = r then
        .pair m Qr Qg inner (chainSlice LG a' r rest)
      else chainSlice LG a' r rest

/-- The lower residual couple Q_[r]. If no chains remain, it is the original lower couple,
not an ill-formed type-2 constructor with two empty chains. -/
def closeCouple (Xp Xm : RegChain) (Qlp : RegCpl) : RegCpl :=
  if Xp.isNil && Xm.isNil then Qlp else .type2 Xp Xm Qlp

/-- TARGET (prooflayer1-1), L1241: product of the explicit single-layer leading terms.
The q<q' branch is the symmetric formula using the negative chain. -/
noncomputable def couple {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 2) (Q : RegCpl) (q q' : ℕ) (t s : ℝ) (k : Mom d) : ℂ :=
  if q = q' then Q.app δ q (F q) t s k else
  match Q with
  | .triv =>
      if q' < q then Q.app δ q' (F q') (q' + 1) s k
      else Q.app δ q (F q) t (q + 1) k
  | .type1 _ _ _ _ =>
      if q' < q then Q.app δ q' (F q') (q' + 1) s k
      else Q.app δ q (F q) t (q + 1) k
  | .type2 Xp Xm Qlp =>
      if q' < q then
        (∏ r ∈ Ioo q' q,
          (chainSlice LG (0, []) r Xp).app δ r (F r) 1 (r + 1) r k) *
        (chainSlice LG (0, []) q Xp).app δ q (F q) 1 t q k *
        (closeCouple (chainSlice LG (0, []) q' Xp) Xm Qlp).app δ q' (F q') (q' + 1) s k
      else
        (∏ r ∈ Ioo q q',
          (chainSlice LG (1, []) r Xm).app δ r (F r) (-1) (r + 1) r k) *
        (chainSlice LG (1, []) q' Xm).app δ q' (F q') (-1) s q' k *
        (closeCouple Xp (chainSlice LG (1, []) q Xm) Qlp).app δ q (F q) t (q + 1) k

/-- TARGET (prooflayer1-2), L1244–1246. On the source domain q'<=q, the lower piece is a
single-layer paired tree; the lone leaf remains at the lower endpoint s. -/
noncomputable def tree {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (X : RegChain) (q q' : ℕ) (t s : ℝ) (k : Mom d) : ℂ :=
  if q = q' then X.app δ q (F q) (LG.garden.sig 0) t s k else
    (∏ r ∈ Ioo q' q,
      (chainSlice LG (0, []) r X).app δ r (F r) (LG.garden.sig 0) (r + 1) r k) *
    (chainSlice LG (0, []) q X).app δ q (F q) (LG.garden.sig 0) t q k *
    (chainSlice LG (0, []) q' X).app δ q' (F q') (LG.garden.sig 0) (q' + 1) s k

/-- The uniform-layer source approximation is literally the B2 formula. -/
theorem couple_same_layer {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 2) (Q : RegCpl) (q : ℕ) (t s : ℝ) (k : Mom d) :
    couple δ F LG Q q q t s k = Q.app δ q (F q) t s k := by
  simp only [couple, ite_true]

theorem tree_same_layer {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (X : RegChain) (q : ℕ) (t s : ℝ) (k : Mom d) :
    tree δ F LG X q q t s k = X.app δ q (F q) (LG.garden.sig 0) t s k := by
  simp only [tree, ite_true]

end WaveTurbulence.LGSpine.SourceApp

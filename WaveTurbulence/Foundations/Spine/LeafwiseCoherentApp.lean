/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseRegularApp
/-! TARGET prooflayer1-1–2 with the original identity of every individual input leaf retained. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset TTree WaveTurbulence.Reg WaveTurbulence.Links

noncomputable def treeLeaves {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeaves L γ δ LG H (fun _ => t) s k (fun _ => 0) 0

namespace LeafApp

/-- The original address of a leaf in the shortened chain slice. A retained pair keeps its
inner/side addresses; only the continuation path is recursively shortened. A skipped pair
moves the whole local address into its original continuation subtree. -/
def sliceAddress {w : ℕ} (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) :
    RegChain → Path → (Fin w × Path)
  | .nil, path => addrExt a path
  | .pair m _Qr _Qg inner rest, path =>
      let step := [m.c] ++ inner.lonePath ++ [m.lone]
      let a' := addrExt a step
      if layerAt LG a = r then
        if step.IsPrefix path then sliceAddress LG a' r rest (path.drop step.length)
        else addrExt a path
      else sliceAddress LG a' r rest path

def sliceProfiles {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (a : Fin w × Path) (r : ℕ) (X : RegChain) : LeafProfiles 1 d :=
  fun z => H (sliceAddress LG a r X z.2)

/-- Profile transport for a lower couple obtained by shortening one of its two chains. -/
def lowerProfiles {d : ℕ} (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (r : ℕ) (Xp Xm : RegChain) (side : Fin 2) : LeafProfiles 2 d :=
  fun z => if z.1 = side then
    H (sliceAddress LG (side, []) r (if side = 0 then Xp else Xm) z.2)
  else H z

/-- Literal prooflayer1-1, with each single-layer app multilinear in its transported leaves. -/
noncomputable def coherentCouple {d : ℕ} (δ : ℝ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) (Q : RegCpl) (q q' : ℕ) (t s : ℝ) (k : Mom d) : ℂ :=
  if q = q' then couple δ q H Q t s k else
  match Q with
  | .triv =>
      if q' < q then couple δ q' H Q (q' + 1) s k
      else couple δ q H Q t (q + 1) k
  | .type1 _ _ _ _ =>
      if q' < q then couple δ q' H Q (q' + 1) s k
      else couple δ q H Q t (q + 1) k
  | .type2 Xp Xm Qlp =>
      if q' < q then
        (∏ r ∈ Ioo q' q, tree δ r (sliceProfiles LG H (0, []) r Xp)
          (SourceApp.chainSlice LG (0, []) r Xp) 1 (r + 1) r k) *
        tree δ q (sliceProfiles LG H (0, []) q Xp)
          (SourceApp.chainSlice LG (0, []) q Xp) 1 t q k *
        couple δ q' (lowerProfiles LG H q' Xp Xm 0)
          (SourceApp.closeCouple (SourceApp.chainSlice LG (0, []) q' Xp) Xm Qlp) (q' + 1) s k
      else
        (∏ r ∈ Ioo q q', tree δ r (sliceProfiles LG H (1, []) r Xm)
          (SourceApp.chainSlice LG (1, []) r Xm) (-1) (r + 1) r k) *
        tree δ q' (sliceProfiles LG H (1, []) q' Xm)
          (SourceApp.chainSlice LG (1, []) q' Xm) (-1) s q' k *
        couple δ q (lowerProfiles LG H q Xp Xm 1)
          (SourceApp.closeCouple Xp (SourceApp.chainSlice LG (1, []) q Xm) Qlp) t (q + 1) k

/-- Literal prooflayer1-2 with the same address transport. -/
noncomputable def coherentTree {d : ℕ} (δ : ℝ) (LG : LayeredGarden 1)
    (H : LeafProfiles 1 d) (X : RegChain) (q q' : ℕ) (t s : ℝ) (k : Mom d) : ℂ :=
  if q = q' then tree δ q H X (LG.garden.sig 0) t s k else
    (∏ r ∈ Ioo q' q, tree δ r (sliceProfiles LG H (0, []) r X)
      (SourceApp.chainSlice LG (0, []) r X) (LG.garden.sig 0) (r + 1) r k) *
    tree δ q (sliceProfiles LG H (0, []) q X)
      (SourceApp.chainSlice LG (0, []) q X) (LG.garden.sig 0) t q k *
    tree δ q' (sliceProfiles LG H (0, []) q' X)
      (SourceApp.chainSlice LG (0, []) q' X) (LG.garden.sig 0) (q' + 1) s k

end LeafApp
end WaveTurbulence.LGSpine

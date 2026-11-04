/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-! # Natural transport of decoded pair lists under address-prefix embeddings -/

public section
namespace WaveTurbulence.Reg
open TTree

mutual
/-- Couple decoding commutes with any literal address map respecting path extension. -/
theorem couple_pairsAt_map {w v : ℕ} (Q : RegCpl)
    (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (a b : Fin w × Path) :
    Q.pairsAt (f a) (f b) = (Q.pairsAt a b).map (fun p => (f p.1,f p.2)) := by
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    simp only [RegCpl.pairsAt,List.map_append,← hf,
      couple_pairsAt_map r f hf,couple_pairsAt_map g f hf,couple_pairsAt_map d f hf]
  | type2 p m q =>
    simp only [RegCpl.pairsAt,List.map_append,← hf,
      chain_pairsAt_map p f hf,chain_pairsAt_map m f hf,couple_pairsAt_map q f hf]
termination_by structural Q

/-- Chain pair decoding commutes with address transport, at either root sign. -/
theorem chain_pairsAt_map {w v : ℕ} (X : RegChain)
    (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (ζ : ℤˣ) (a : Fin w × Path) :
    X.pairsAt ζ (f a) = (X.pairsAt ζ a).map (fun p => (f p.1,f p.2)) := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [RegChain.pairsAt,hr,hg,ite_true,ite_false,List.map_append,← hf,
        couple_pairsAt_map r f hf,couple_pairsAt_map g f hf,
        chain_pairsAt_map i f hf,chain_pairsAt_map s f hf]
termination_by structural X
end

end WaveTurbulence.Reg

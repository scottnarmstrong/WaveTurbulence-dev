# Packets M1 MOLE + M2 BLOCKS (pre-freeze) — molecules of gardens, decorations, cuts, counting quantities, blocks

Read `COMMON.md` first. Blueprint packets M1, M2 (rows `T.defmol`, `MOL.countq`, `T.propcplmol`, `DH212.reconstruction`,
`T.disjointlem`, block rows); near the Stage-2 chain (S2a/S4/G1–G3/G8; review I9: 𝔈/𝔄/𝔇𝔢𝔳 live here).

The molecule definitions are drafted (Wave B tier B2 stage 2, audited APPROVED: `docs/campaign/orch/audits/WaveB2-stage23.md`)
in `/home/scott/wt-scratch/waveb2-snap-1/` (and the live `/home/scott/wt-scratch/waveb2/WaveB2-Molecules.lean`): molecules
with half-edges (F40), molecules of gardens, decorations of molecules, blocks, vines/ladders (F37), gaps SG/LG/ZG, cuts,
𝔈/𝔄/𝔇𝔢𝔳. Not frozen yet. Work in untracked scratch `/home/scott/wt-scratch/mole/` against local copies of
`/home/scott/wt-scratch/waveb-snap-5/` (B1) and the B2 molecules draft; import the COMB-CORE scratch API
(`/home/scott/wt-scratch/comb-core/`) where useful. Report any defect in the drafts (do not change them).

Goals (do not end your turn at milestones):
1. Molecule API: the molecule of a garden (TARGET L1297–L1302; DH21-2 Defs 6.1–6.2), atoms of degree ≤ 4, bonds,
   connectivity and χ = n − R + 1 for irreducible gardens (`propcplmol`, TARGET L1304–L1306), decorations of molecules
   and their correspondence with garden decorations (L1308–L1325).
2. DH21-2 Prop 6.4 (`reconstruction`: the number of gardens with a given molecule is ≤ (C₀R)! C₀^n; encoding by position
   codes 0–3).
3. Blocks and hyper-blocks (L1328–L1331; DH23 Def 4.10, Lemma 4.11 `disjointlem`), realizations.
4. Cuts (half-edge moves) and the counting quantities 𝔈, 𝔄, 𝔇𝔢𝔳 of an operation (`MOL.countq`), generic in the molecule.
Done: `READY mole`.

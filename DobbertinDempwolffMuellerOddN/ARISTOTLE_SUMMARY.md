# Summary of changes for run e5738eeb-53b1-4eb0-80ac-311cef1b941c
## What I did

### 1. Made the library build and runnable
The sources imported modules under a `Dobbertin1999MVP.*` prefix, but the files were physically laid out directly under `Core/`, `Dobbertin1999/`, `FiniteField/`, so nothing compiled. I:
- Reorganized the tree into the intended `Dobbertin1999MVP/` package (matching the imports and the entry-file/README docs);
- Added the `Dobbertin1999MVP.lean` entry point with the headline aliases;
- Updated `lakefile.toml` (`defaultTargets`/`lean_lib` = `Dobbertin1999MVP`).

`lake build` now succeeds (whole project), and all five headline results are `sorry`-free, resting only on `propext`, `Classical.choice`, `Quot.sound`:
`mcm_permutation`, `dempwolff_mueller_permutation_ktransfer`, `kasami_key_identity`, `kasami_is_apn`, `kasami_is_apn_solution_count`.

### 2. Redundancy analysis
I computed the exact transitive dependency closure of the five headline theorems and cross-checked it against every declaration in the project. This showed which lemmas actually contribute and which are dead weight.

### 3. Removed redundant modules and lemmas
- **Deleted two entirely-unused modules**: `FiniteField/AutBase.lean` (a Singer-cycle / additive-polynomial theory, 0 of 32 declarations used) and `FiniteField/Lemma31.lean` (a superseded alternative to `BareLemma31Skeleton`, which is the version actually used — 0 of 11 used), and removed their imports.
- **Removed unused helper lemmas** from the partially-used modules: 14 in `FrobAlg`, 6 in `ExpArith`, 2 in `AdjointBij`, 2 in `Thm32`.

Net effect: the code shrank from ~2300 lines / 12 files to ~1770 lines / 11 files, and every remaining declaration now traces to the headlines — except four `Dobbertin1999/MCMtoAPN` wrapper theorems (`gold_permutation`, `mcm_injective_bridge`, `kasami_collision_forces_equal_u`, `truncTrace_artin_schreier`). These are thin re-exports of the corresponding `Core/KasamiAPN` lemmas; the final theorems reach into `Core` directly, so they are not strictly needed, but I kept them because they are the paper's named proof steps for Corollary 2 and are documented as such in the README and module docstrings. They can be dropped if you prefer strict minimality.

### 4. Simplifications / replacing ad-hoc proofs
- Discovered that `apn_of_normalized` (the APN WLOG reduction) never needed the coprimality hypothesis — its `x ↦ x/a` scaling argument works for any exponent. Generalizing it made the whole lemma `kasami_exp_coprime` (a ~30-line gcd computation) unnecessary, so it was removed.
- Replaced a leftover interactive `exact?` in `kasami_key_identity` with the direct Mathlib term `add_pow_char_pow`, and removed another leftover `exact?` in `exists_linking_exp`.
- Removed unused hypotheses (`hk_odd` in `exists_linking_exp`) and unused `simp` arguments in the touched proofs, updating call sites accordingly.

### Notes
- The core proofs (`FiniteField/BareLemma31Skeleton`, `Thm32`, `TraceNorm`, etc.) still emit some cosmetic linter messages (unused section variables / unused `simp` arguments / a couple of `ring` "try `ring_nf`" info hints) inside dense machine-style proofs. These are non-fatal and were left untouched to avoid destabilizing working proofs; they can be cleaned incrementally if desired.
- No axioms or `@[implemented_by]` were introduced.

All changes are committed and pushed to `main`. Relative paths of the deleted files: `Dobbertin1999MVP/FiniteField/AutBase.lean`, `Dobbertin1999MVP/FiniteField/Lemma31.lean`.
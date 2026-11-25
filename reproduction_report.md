# Reproduction report

Date: 2026-11-25 (UTC 18:27). Machine: Linux x86-64, elan with `leanprover/lean4:v4.34.1`.

Test: a fresh copy of this repository (no `.lake/`), then the two commands of the README.

| Step | Command | Result | Time |
|---|---|---|---|
| 1 | `lake exe cache get` | dependencies cloned at the commits of `lake-manifest.json`; 8907 Mathlib files decompressed | 251 s |
| 2 | `lake build` | `Build completed successfully (2815 jobs)`; no errors, no warnings | 95 s |
| 3 | `#print axioms` on `finite_path_series`, `finite_path_series_summable`, `double_integral_eq_two_branches`, `integral_filter_branches`, `pathFilter_eq` | only `propext`, `Classical.choice`, `Quot.sound` | — |
| 4 | search for `sorry`, `axiom`, `native_decide` in the sources | none | — |

Disk used by `.lake/` after the build: 7.7 GB.

Caveat: the compiled Mathlib archives came from the machine's local Mathlib cache
(`~/.cache/mathlib`), which `lake exe cache get` fills on first use; on a machine without it the
same command downloads them. The CI workflow (`.github/workflows/lean_action_ci.yml`) repeats the
build on a clean GitHub runner at every push.

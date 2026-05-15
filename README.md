# PMM-FP Code Supplement

Reproducibility supplement for:

> **Polynomial Maximization Method with Fractional Polynomial Basis: A Frequentist Bridge to Bayesian Fractional Polynomials**  
> *Statistical Modelling* (submitted 2026-05-14)

---

## What this repository contains

| Directory | Contents |
|-----------|----------|
| `lean/` | Lean 4 source (9 files), `lakefile.lean`, `lean-toolchain`, build audit log |
| `R/` | R scripts for figure and table generation from stored results |
| `data/` | Stored Monte Carlo summary (38 KB) and GBSG analysis outputs |
| `results/tables/` | Pre-generated CSV + LaTeX tables for all paper claims |
| `results/figures/` | Pre-generated PDF figures (Fig. 1 and Fig. 2) |
| `session_info.txt` | R session information at submission time |

---

## Quick reproducibility check

```bash
# Regenerate figures and tables from stored data (no special packages beyond mfp):
Rscript --vanilla run_all.R
```

---

## Lean formal verification

The `lean/` directory contains all Lean 4 source files. To verify:

```bash
cd lean
lake build
```

**Requirements:** Lean 4 v4.26.0, Mathlib v4.26.0 (both specified in `lean/lean-toolchain` and `lean/lakefile.lean`). The first build downloads Mathlib (~1 GB cache). Subsequent builds use the cache.

**Audit evidence:** `lean/audit/lake_build_log.txt` records the build at submission time (0 errors, 0 active `sorry`s). The theorem map in `lean/audit/theorem_map.md` links each paper statement to its Lean file.

---

## Regenerating figures

```bash
Rscript --vanilla R/make_submission_figures.R [output_dir]
```

Reads stored data from `results/tables/` and `data/gbsg_20260512/`. No EstemPMM package required. Produces:

- `results/figures/fig_mc_g2.pdf` — Figure 1 (Monte Carlo calibration bar chart)
- `results/figures/fig_gbsg_application.pdf` — Figure 2 (GBSG real-data 4-panel)

---

## Regenerating LaTeX tables

```bash
Rscript --vanilla R/build_matched_tables.R data/mc_matched_summary.csv results/tables
```

Reads the stored Monte Carlo summary and writes `tab_mc_*.{csv,tex}` to `results/tables/`. No EstemPMM package required.

---

## Re-running Monte Carlo (optional)

Full Monte Carlo re-runs require the `EstemPMM` R package (v0.3.2, available on CRAN):

```r
install.packages("EstemPMM")
```

The stored `data/mc_matched_summary.csv` replicates all paper tables without re-running.

---

## GBSG real-data analysis

The GBSG dataset is public via the R package `mfp`:

```r
install.packages("mfp")
data(GBSG, package = "mfp")
```

The stored outputs in `data/gbsg_20260512/` (predictions, residual summaries, bootstrap g2 estimates) replicate the paper's §5.2 claims. Re-running the full analysis requires `EstemPMM` (v0.3.2, CRAN).

---

## Not included

| Item | Reason |
|------|--------|
| Hubin et al. fish-nutrition data | No public repository; manuscript makes no replication claim |
| PATP arXiv identifier | Preprint under processing at submission time |
| Full Monte Carlo R harness | Requires EstemPMM v0.3.2 (CRAN) |

---

## Software versions

- R 4.5.2 (aarch64-apple-darwin24, macOS Tahoe 26.3.1)  
- Lean 4 v4.26.0, Mathlib v4.26.0  
- R packages: `mfp` (GBSG data), `FBMS` (BFP comparison, optional)

See `session_info.txt` for the full R session at submission time.

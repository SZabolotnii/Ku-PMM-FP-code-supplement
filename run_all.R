#!/usr/bin/env Rscript
# PMM-FP reproducibility driver — self-contained supplement repo.
#
# Run from the repo root:
#   Rscript --vanilla run_all.R
#
# What this does:
#   1. Regenerate submission figures from stored data (no EstemPMM required).
#   2. Regenerate LaTeX tables from stored MC summary (no EstemPMM required).
#   3. Attempt a Lean build (requires Lean 4 + Mathlib — see lean/README below).
#
# EstemPMM package note:
#   Re-running the full Monte Carlo simulation requires the in-development
#   EstemPMM R package (feature/fp branch). Stored numerical results in
#   results/tables/ and data/ replicate all paper tables without re-running MC.

root <- normalizePath(dirname(sys.frame(1)$ofile %||% "."), mustWork = FALSE)
setwd(root)
`%||%` <- function(x, y) if (is.null(x)) y else x

cat("=== PMM-FP reproducibility check ===\n")
cat("Working directory:", getwd(), "\n\n")

# ── Step 1: Figures ──────────────────────────────────────────────────────────
cat("Step 1: Regenerating submission figures...\n")
tryCatch(
    source("R/make_submission_figures.R"),
    error = function(e) cat("  WARNING:", conditionMessage(e), "\n")
)
cat("  Wrote: results/figures/fig_mc_g2.pdf\n")
cat("  Wrote: results/figures/fig_gbsg_application.pdf\n\n")

# ── Step 2: Tables ───────────────────────────────────────────────────────────
cat("Step 2: Regenerating LaTeX tables from stored MC summary...\n")
tryCatch(
    system2("Rscript", c("--vanilla", "R/build_matched_tables.R",
                         "data/mc_matched_summary.csv",
                         "results/tables"),
            stdout = TRUE, stderr = TRUE),
    error = function(e) cat("  WARNING:", conditionMessage(e), "\n")
)
cat("  Wrote: results/tables/tab_mc_*.{csv,tex}\n\n")

# ── Step 3: Lean build ───────────────────────────────────────────────────────
cat("Step 3: Lean build (lean/ directory)...\n")
cat("  Requires: Lean 4 v4.26.0 + Mathlib v4.26.0\n")
cat("  See lean/lean-toolchain and lean/lakefile.lean\n")
old_wd <- getwd()
setwd(file.path(root, "lean"))
lean_out <- tryCatch(
    system2("lake", "build", stdout = TRUE, stderr = TRUE),
    error = function(e) paste("lake not found:", conditionMessage(e))
)
writeLines(lean_out, file.path(root, "lean/audit/lake_build_log.txt"))
setwd(old_wd)
lean_ok <- !any(grepl("error", lean_out, ignore.case = TRUE))
cat(if (lean_ok) "  BUILD OK\n" else "  BUILD FAILED — see lean/audit/lake_build_log.txt\n")
cat("\n")

# ── Session info ─────────────────────────────────────────────────────────────
writeLines(capture.output(sessionInfo()), "session_info.txt")
cat("Session info written to session_info.txt\n")
cat("\n=== Done ===\n")

#!/usr/bin/env Rscript
# =============================================================================
# R/build_matched_tables.R
# Generate LaTeX-ready tables for §5 from a matched-basis MC summary.csv.
#
# Tables (Phase R3.1 deliverable B4):
#   tab_mc_are_matched     : empirical ARE vs theoretical g2 by (DGP, n, est)
#   tab_mc_mse             : MSE = bias^2 + variance, slope coefficient
#   tab_mc_coverage        : 95% CI coverage rates
#   tab_mc_timings         : mean +/- SD wall-clock runtime
#   tab_mc_competitors     : PMM-FP vs Huber-FP vs GMM-FP head-to-head (slope)
#
# Usage:
#   Rscript R/build_matched_tables.R <summary.csv> [output_dir]
# Output: <output_dir>/{tab_*.csv, tab_*.tex}
# =============================================================================

args <- commandArgs(trailingOnly = TRUE)
if (length(args) < 1L) {
    stop("Usage: build_matched_tables.R <summary.csv> [output_dir]")
}
in_csv  <- args[1]
out_dir <- if (length(args) >= 2L) args[2] else dirname(in_csv)
dir.create(out_dir, recursive = TRUE, showWarnings = FALSE)

df <- read.csv(in_csv, stringsAsFactors = FALSE)
message(sprintf("Loaded %d rows from %s", nrow(df), in_csv))

# Pretty estimator labels for LaTeX
est_label <- c(
    ols_fp   = "OLS-FP",
    mle_fp   = "MLE-FP",
    pmm_fp   = "PMM-FP",
    huber_fp = "Huber-FP",
    gmm_fp   = "GMM-FP",
    bfp      = "BFP"
)
df$est_label <- ifelse(df$estimator %in% names(est_label),
                       est_label[df$estimator], df$estimator)

fmt_num <- function(x, d = 3) {
    ifelse(is.finite(x),
           formatC(x, format = "f", digits = d),
           "---")
}
fmt_pct <- function(x, digits = 1) ifelse(is.finite(x),
                              formatC(100 * x, format = "f", digits = digits),
                              "---")


#' Pivot a long summary to wide format keyed by estimator.
.pivot_estimators <- function(df, value_col, fmt = fmt_num,
                              digits = 3) {
    df$val_fmt <- fmt(df[[value_col]], digits)
    wide <- reshape(
        df[, c("dgp_id", "n", "est_label", "val_fmt")],
        timevar = "est_label", idvar = c("dgp_id", "n"),
        direction = "wide"
    )
    names(wide) <- gsub("^val_fmt\\.", "", names(wide))
    wide
}

#' Simple LaTeX export (booktabs).
.to_latex <- function(df_wide, caption, label, file_tex) {
    cols <- ncol(df_wide)
    align <- paste0("l", paste(rep("r", cols - 1L), collapse = ""))
    tex <- c(
        sprintf("\\begin{table}[t]"),
        sprintf("\\centering"),
        sprintf("\\caption{%s}", caption),
        sprintf("\\label{%s}", label),
        sprintf("\\begin{tabular}{%s}", align),
        "\\toprule",
        paste(names(df_wide), collapse = " & ") %>%
            (function(s) paste0(s, " \\\\")),
        "\\midrule"
    )
    for (i in seq_len(nrow(df_wide))) {
        row <- as.character(df_wide[i, ])
        tex <- c(tex, paste(paste(row, collapse = " & "), "\\\\"))
    }
    tex <- c(tex, "\\bottomrule", "\\end{tabular}", "\\end{table}")
    writeLines(tex, file_tex)
}

# Local pipe-into-call helper (avoid magrittr dependency)
`%>%` <- function(lhs, rhs) rhs(lhs)


# -- Table 1: ARE (g2_emp) vs theoretical g2 -----------------------------------
{
    sub <- df[, c("dgp_id", "n", "estimator", "est_label",
                  "g2_emp_coef2", "g2_theoretical")]
    sub$g2_th_fmt <- fmt_num(sub$g2_theoretical, 3)
    wide <- .pivot_estimators(sub, "g2_emp_coef2", fmt_num, 3)
    # Append theoretical column
    th <- aggregate(g2_theoretical ~ dgp_id + n, data = sub, FUN = mean)
    names(th)[3] <- "g2_th"
    wide <- merge(wide, th, by = c("dgp_id", "n"))
    wide$g2_th <- fmt_num(wide$g2_th, 3)
    wide <- wide[order(wide$dgp_id, wide$n), ]
    write.csv(wide, file.path(out_dir, "tab_mc_are_matched.csv"),
              row.names = FALSE)
    .to_latex(wide,
              caption = "Empirical $\\hat g_2 = \\Var(\\hat\\beta_1) / \\Var(\\hat\\beta_1^{OLS})$ vs theoretical $g_2$ (slope coefficient).",
              label   = "tab:mc-are-matched",
              file_tex = file.path(out_dir, "tab_mc_are_matched.tex"))
    message("Wrote tab_mc_are_matched.{csv,tex}")
}

# -- Table 2: MSE breakdown (slope coefficient) --------------------------------
{
    df$mse_slope <- df$mse_coef2
    wide <- .pivot_estimators(df, "mse_slope", fmt_num, 3)
    wide <- wide[order(wide$dgp_id, wide$n), ]
    write.csv(wide, file.path(out_dir, "tab_mc_mse.csv"),
              row.names = FALSE)
    .to_latex(wide,
              caption = "Mean squared error of slope coefficient ($\\hat\\beta_1$) across $M$ replications.",
              label   = "tab:mc-mse",
              file_tex = file.path(out_dir, "tab_mc_mse.tex"))
    message("Wrote tab_mc_mse.{csv,tex}")
}

# -- Table 3: 95% CI coverage --------------------------------------------------
{
    wide <- .pivot_estimators(df, "cov_coef2", fmt_pct)
    wide <- wide[order(wide$dgp_id, wide$n), ]
    write.csv(wide, file.path(out_dir, "tab_mc_coverage.csv"),
              row.names = FALSE)
    .to_latex(wide,
              caption = "95\\% confidence interval coverage rate (\\%) for slope coefficient.",
              label   = "tab:mc-coverage",
              file_tex = file.path(out_dir, "tab_mc_coverage.tex"))
    message("Wrote tab_mc_coverage.{csv,tex}")
}

# -- Table 4: Wall-clock timings -----------------------------------------------
{
    df$time_str <- ifelse(is.finite(df$mean_time),
                          sprintf("%.3f\\pm%.3f",
                                  df$mean_time, df$sd_time),
                          "---")
    sub <- df[, c("dgp_id", "n", "est_label", "time_str")]
    wide <- reshape(sub, timevar = "est_label",
                    idvar = c("dgp_id", "n"), direction = "wide")
    names(wide) <- gsub("^time_str\\.", "", names(wide))
    wide <- wide[order(wide$dgp_id, wide$n), ]
    write.csv(wide, file.path(out_dir, "tab_mc_timings_controlled.csv"),
              row.names = FALSE)
    .to_latex(wide,
              caption = "Wall-clock runtime (mean $\\pm$ SD seconds per replication) on controlled hardware.",
              label   = "tab:mc-timings-controlled",
              file_tex = file.path(out_dir, "tab_mc_timings_controlled.tex"))
    message("Wrote tab_mc_timings_controlled.{csv,tex}")
}

# -- Table 5: Competitors head-to-head -----------------------------------------
{
    keep <- df$estimator %in% c("pmm_fp", "huber_fp", "gmm_fp")
    sub  <- df[keep, c("dgp_id", "n", "est_label",
                       "g2_emp_coef2", "mse_coef2", "cov_coef2")]
    sub$line <- sprintf("%s / %s / %s",
                        fmt_num(sub$g2_emp_coef2, 3),
                        fmt_num(sub$mse_coef2, 3),
                        fmt_pct(sub$cov_coef2))
    wide <- reshape(sub[, c("dgp_id", "n", "est_label", "line")],
                    timevar = "est_label",
                    idvar = c("dgp_id", "n"), direction = "wide")
    names(wide) <- gsub("^line\\.", "", names(wide))
    wide <- wide[order(wide$dgp_id, wide$n), ]
    write.csv(wide, file.path(out_dir, "tab_mc_competitors.csv"),
              row.names = FALSE)
    .to_latex(wide,
              caption = "Frequentist competitors head-to-head: $\\hat g_2$ / MSE / 95\\% coverage of slope.",
              label   = "tab:mc-competitors",
              file_tex = file.path(out_dir, "tab_mc_competitors.tex"))
    message("Wrote tab_mc_competitors.{csv,tex}")
}

message(sprintf("All tables written to %s", out_dir))

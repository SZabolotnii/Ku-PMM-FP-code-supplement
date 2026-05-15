#!/usr/bin/env Rscript
# Generate submission-grade figures for the compact Statistical Modelling draft.

args <- commandArgs(trailingOnly = TRUE)
out_dir <- if (length(args) >= 1L) args[1] else "results/figures"
dir.create(out_dir, recursive = TRUE, showWarnings = FALSE)

read_required <- function(path) {
    if (!file.exists(path)) {
        stop(sprintf("Required input not found: %s", path), call. = FALSE)
    }
    read.csv(path, stringsAsFactors = FALSE, check.names = FALSE)
}

num <- function(x) suppressWarnings(as.numeric(x))
method_label <- function(x) {
    map <- c(
        ols_fp = "OLS-FP",
        pmm_fp_a = "PMM-FP pos",
        bfp = "BFP"
    )
    out <- ifelse(x %in% names(map), map[x], x)
    unname(out)
}

mc <- read_required("results/tables/tab_mc_are_matched.csv")
pred <- read_required("data/gbsg_20260512/predictions.csv")
boot <- read_required("results/tables/bootstrap_betas.csv")
modelsel <- read_required("results/tables/model_selection_freq.csv")

# ---------------------------------------------------------------------------
# Figure 1: Monte Carlo large-sample calibration — grouped bar chart.
# ---------------------------------------------------------------------------
fig_mc <- file.path(out_dir, "fig_mc_g2.pdf")
pdf(fig_mc, width = 6.4, height = 4.1, pointsize = 10)
op <- par(mar = c(4.8, 4.4, 2.0, 0.8), las = 1)
on.exit(par(op), add = TRUE)

dgp_order <- c("Gauss", "Beta25", "Gamma3", "Exp1", "LogN")
dgp_order <- dgp_order[dgp_order %in% mc$dgp_id]

z <- mc[num(mc$n) == 1000, ]
z <- z[match(dgp_order, z$dgp_id), ]
emp <- num(z$`PMM-FP`)
th  <- num(z$g2_th)

# Two rows: row 1 = theoretical g2, row 2 = empirical PMM-FP
mat <- rbind(th, emp)
colnames(mat) <- dgp_order

bar_cols <- c("#9ecae1", "#2171b5")   # light blue = theoretical, dark blue = empirical

bp <- barplot(
    mat,
    beside    = TRUE,
    col       = bar_cols,
    ylim      = c(0, 1.18),
    ylab      = "Variance ratio",
    names.arg = dgp_order,
    las       = 2,
    border    = NA,
    space     = c(0.1, 0.6)          # narrow gap within group, wider between groups
)
abline(h = 1, col = "gray40", lty = 3, lwd = 1.2)
legend(
    "topright",
    legend = c(expression(paste("Theoretical ", g[2])), "Empirical PMM-FP"),
    fill   = bar_cols,
    border = NA,
    bty    = "n",
    cex    = 0.88
)
mtext("Matched-basis Monte Carlo at n = 1000", side = 3, line = 0.6, cex = 0.9)
dev.off()

# ---------------------------------------------------------------------------
# Figure 2: GBSG real-data evidence — readable layout.
# ---------------------------------------------------------------------------
fig_gbsg <- file.path(out_dir, "fig_gbsg_application.pdf")
# smj.cls textwidth = 6 in. Render PDF close to natural print width so the
# \linewidth scale factor stays near 1.0 and the chosen pointsize survives.
pdf(fig_gbsg, width = 6.2, height = 6.0, pointsize = 11)
op <- par(
    mfrow      = c(2, 2),
    mar        = c(4.2, 5.0, 2.6, 1.8),
    oma        = c(0, 0, 0, 0),
    las        = 1,
    cex.main   = 1.05,
    cex.lab    = 0.95,
    cex.axis   = 0.85
)
on.exit(par(op), add = TRUE)

# Panel A: partial dependence of fitted curves on tumour size.
# Predictions of OLS-FP also depend on age and hormone therapy, so the raw
# per-observation fitted values zigzag when plotted against tumsize alone.
# Binning by tumsize and averaging gives a clean partial-dependence view.
# PMM-FP full (1/x^2 basis) is omitted: §5.2 already documents its
# conditioning instability for this sample size, so showing it would mislead.
nbins <- 20
bin   <- cut(pred$tumsize, breaks = nbins, include.lowest = TRUE)
agg   <- aggregate(
    cbind(tumsize    = pred$tumsize,
          ols_fp     = pred$pred_ols_fp,
          pmm_fp_pos = pred$pred_pmm_fp_pos) ~ bin,
    FUN = mean
)
plot(
    pred$tumsize, pred$y_obs,
    pch = 16, cex = 0.55, col = "#5A5A5A55",
    xlab = "Tumour size", ylab = "log(rfst)",
    main = "A. Fitted curves (bin-averaged)"
)
lines(agg$tumsize, agg$ols_fp,     col = "#4C78A8", lwd = 2.5)
lines(agg$tumsize, agg$pmm_fp_pos, col = "#E15759", lwd = 2.5)
legend(
    "topright", legend = c("OLS-FP", "PMM-FP pos"),
    col = c("#4C78A8", "#E15759"), lty = 1,
    lwd = 2.5, bty = "n", cex = 0.95
)

# Panel B: bootstrap coefficient intervals with SE annotations.
boot$label <- method_label(boot$method)
boot       <- boot[order(boot$point), ]
y          <- seq_len(nrow(boot))
xrng       <- range(c(boot$ci_lo, boot$ci_hi), finite = TRUE)
# Reserve ~30% of the x-range on the right for SE labels so they never
# overflow into the neighbouring panel even at small print width.
xpad       <- 0.32 * diff(xrng)
xlim       <- c(xrng[1], xrng[2] + xpad)
plot(
    boot$point, y, xlim = xlim, ylim = c(0.5, length(y) + 0.5),
    yaxt = "n", ylab = "", xlab = "Tumour-size coefficient",
    pch = 16, col = "#333333", main = "B. Bootstrap 95% intervals"
)
axis(2, at = y, labels = boot$label, las = 1)
abline(v = 0, col = "gray70", lty = 3)
segments(boot$ci_lo, y, boot$ci_hi, y, lwd = 3, col = "#333333")
points(boot$point, y, pch = 16, col = "#E15759", cex = 1.3)
text(
    boot$ci_hi, y,
    labels = sprintf("SE=%.3f", num(boot$se)),
    pos = 4, offset = 0.35, cex = 0.85, col = "#444444"
)

# Panel C: Q-Q plot motivating PMM-FP (non-Gaussian OLS residuals).
res_ols <- pred$y_obs - pred$pred_ols_fp
res_std <- (res_ols - mean(res_ols, na.rm = TRUE)) /
                sd(res_ols, na.rm = TRUE)
qqnorm(
    res_std,
    pch  = 16, cex = 0.55, col = "#33333380",
    main = "C. OLS-FP residual Q-Q plot",
    xlab = "Theoretical quantiles",
    ylab = "Standardised residual"
)
qqline(res_std, col = "#E15759", lwd = 2.5)
# moments come from results/.../eda_residual_summary.csv (n = 686)
res_summary <- tryCatch(
    read_required("data/gbsg_20260512/eda_residual_summary.csv"),
    error = function(e) NULL
)
if (!is.null(res_summary)) {
    g3 <- num(res_summary$gamma3_emp[1])
    g4 <- num(res_summary$gamma4_emp[1])
    sw <- num(res_summary$shapiro_W[1])
} else {
    g3 <- -1.74; g4 <- 4.91; sw <- 0.870
}
legend(
    "topleft",
    legend = c(
        bquote(hat(gamma)[3] == .(sprintf("%.2f", g3))),
        bquote(hat(gamma)[4] == .(sprintf("%.2f", g4))),
        bquote("Shapiro " * italic(W) == .(sprintf("%.3f", sw)))
    ),
    bty = "n", cex = 0.95, adj = c(0, 0.5), y.intersp = 1.15
)

# Panel D: model-selection frequencies, Cleveland lollipop on sqrt scale.
# The frequency distribution is "1 dominant + 4 tiny", so a linear bar chart
# leaves the small bars almost invisible. sqrt-scale lollipops keep the
# dominance message while making the minor models perceptible.
decode_pow <- function(p) {
    if (is.na(p) || p == "NA") return(NA_character_)
    p <- as.numeric(p)
    if (p == 0)    return("ln x")
    if (p == 1)    return("x")
    if (p == 0.5)  return("sqrt(x)")
    if (p == -0.5) return("1/sqrt(x)")
    sprintf("x^%g", p)
}
decode_label <- function(s) {
    parts  <- strsplit(s, ",")[[1]]
    pieces <- vapply(parts, decode_pow, character(1))
    pieces <- pieces[!is.na(pieces)]
    if (length(pieces) == 2 && pieces[1] == pieces[2]) {
        return(sprintf("%s + %s ln x", pieces[1], pieces[1]))
    }
    paste(pieces, collapse = " + ")
}
top    <- head(modelsel, 5)
freq   <- num(top$frequency)
labels <- vapply(top$model_powers, decode_label, character(1))
ord    <- order(freq)                          # ascending so the biggest is on top
freq   <- freq[ord]
labels <- labels[ord]
sf     <- sqrt(freq)                           # sqrt visual scale
yv     <- seq_along(freq)
# Slightly more room on the left so long labels (e.g. "x^-2 + x^-2 ln x")
# fit; right pad reserved for the "%" annotation.
op2 <- par(mar = c(4.2, 7.5, 2.6, 4.0))
on.exit(par(op2), add = TRUE)
plot(
    sf, yv,
    xlim = c(0, 1.35),
    ylim = c(0.5, length(yv) + 0.5),
    type = "n",
    xaxt = "n", yaxt = "n",                    # suppress default ticks
    xlab = "Bootstrap frequency (sqrt-scale)",
    ylab = "",
    main = "D. FP model selection"
)
xticks <- c(0, 0.05, 0.25, 0.5, 1.0)
axis(1, at = sqrt(xticks),
     labels = sprintf("%g", xticks), cex.axis = 0.85)
axis(2, at = yv, labels = labels, las = 1, cex.axis = 0.9)
segments(0, yv, sf, yv, col = "#76B7B2", lwd = 4)
points(sf, yv, pch = 19, col = "#2E8A8C", cex = 1.3)
text(sf, yv,
     labels = sprintf("%.1f%%", 100 * freq),
     pos = 4, offset = 0.5, cex = 0.9, col = "#333333")
dev.off()

cat(sprintf("Wrote %s\n", fig_mc))
cat(sprintf("Wrote %s\n", fig_gbsg))

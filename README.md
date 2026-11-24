# cnd-lean

Lean 4 formalization of CND and ECND, two online server-selection algorithms for atomic congestion games with quantized hybrid feedback.

## Build

Install Lean through [elan](https://github.com/leanprover/elan). The repository pins Lean `v4.24.0` and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

```sh
git clone https://github.com/SKYdayDUCK/cnd-lean.git
cd cnd-lean
lake exe cache get
lake build
lake env lean Audit.lean
```

Use `import CNDLean` to bring the proofs into scope. `Audit.lean` checks that `CNDLean` can be imported alongside mathlib's optional-stopping module and reports the axioms of the theorem entry points below.

| Result | Lean declaration |
| --- | --- |
| CND, bounded model with explicit regret rates | `Part2.CNDHorizon.FiniteBounded.paper_original_main_with_rates` |
| CND, conditionally sub-Gaussian model with explicit regret rates | `Part2.CNDHorizon.FiniteSG.paper_original_sg_main_with_rates` |
| Adjacent-grid randomized rounding and the conditional moment bound | `Part2.AdjacentEncoderSG.conditional_mgf` |
| ECND, bounded model with unit confidence and radius scales | `Part2.ExponentialFiniteGap.unit_scale_budget_main` |
| ECND, conditionally sub-Gaussian model under the theorem's legality conditions | `Part2.ExponentialSGFinite.original_legal_budget_main` |

The source also includes probability transport, the conditionally negative definite radius, and the finite-horizon boundary cases. The theorem statements specify the feedback laws, confidence conditions, and rate assumptions.

## Explicit dynamic regret rates for ECND

The bounded and conditionally sub-Gaussian cases are covered by
`Part2.ExponentialSublinear.bounded_dynamic_regret` and
`Part2.ExponentialSublinear.sg_dynamic_regret`. Both use the original
exponential update, a uniform expert prior, unit confidence and radius
scales, and a fixed rate in the following band for each expert.

$$
\frac{1}{4W\sqrt T} \le \eta_e \le \frac{1}{2W\sqrt T}.
$$

Here $T$ is the horizon and $W$ is the broadcast-cost span bound.
If each constant-arm interval needs at most $q_T$ cover pieces, each
served by an expert starting at that piece, the expert term is at most
$4W(s+1)q_T\sqrt T(\log |E| + e - 2)$, where $s$ is the comparator
switch count and $|E|$ is the expert count. The sampling term scales as
$\sqrt{T(s+1)}$ up to logarithms, and the private-learning budget enters
once. The bounds hold simultaneously for all comparator paths at the
chosen horizon on one high-probability event.

`all_interval_schedule` constructs a bank of $KT(T+1)$ virtual experts,
including inactive endpoint pairs, with one piece per comparison run.
For fixed server count and cost scales, $(s+1)\log T=o(\sqrt T)$ suffices
for sublinear regret with this bank. The asymptotic implication is checked
in `Part2.ExponentialSublinearLimit`. The library also checks a linear
regret example for a fixed positive rate in the expert update.

## License

The formalization is released under the [MIT License](LICENSE). Its [mathlib dependency](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/LICENSE) is licensed under Apache 2.0.

## 中文说明

本仓库包含 CND 和 ECND 的 Lean 4 证明，覆盖有界潜在对抗性漂移、条件次高斯扩展，以及指数专家更新的遗憾界。运行上面的命令即可构建并查看主要定理依赖的公理。

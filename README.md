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

## License

The formalization is released under the [MIT License](LICENSE). Its [mathlib dependency](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/LICENSE) is licensed under Apache 2.0.

## 中文说明

本仓库包含 CND 和 ECND 的 Lean 4 证明，覆盖有界潜在对抗性漂移、条件次高斯扩展，以及指数专家更新的遗憾界。运行上面的命令即可构建并查看主要定理依赖的公理。

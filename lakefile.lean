import Lake
open Lake DSL

package «cnd-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib CNDLean where
  srcDir := "Lean"
  globs := #[
    .one `CNDLean,
    .submodules `Part2,
    .submodules `staging,
    .one `ActualRadius,
    .one `CNDCausalChoice,
    .one `CNDCompactSelection,
    .one `CNDConfidenceChoice,
    .one `CNDConfidenceSlabs,
    .one `CNDMatrixProx,
    .one `CNDMinimumNormMeasurable,
    .one `CNDPhysicalRegret,
    .one `ExactGreedyMeasurable,
    .one `ExactGreedyTransport,
    .one `GaussianClosure,
    .one `InformationBudget,
    .one `InformationDimension,
    .one `OriginalRadiusBridge,
    .one `PrivateInformationBudget,
    .one `RateAbsorption,
    .one `SqrtClosure,
    .one `SwitchingRuns,
    .one `TangentChart
  ]

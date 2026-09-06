import Lake
open Lake DSL

package audit

-- Audit-only mathematics dependency. Runtime Rust/Solidity dependencies are unchanged.
-- Provision and inspect these exact source revisions before executing Lake hooks.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "a719ba5c3115d47b68bf0497a9dd1bcbb21ea663"

@[default_target]
lean_lib Audit

-- Explicit historical-only target. Never imported by the current audit root.
lean_lib HistoricalAudit

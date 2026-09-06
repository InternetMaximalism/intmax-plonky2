import Lake
open Lake DSL

package audit

@[default_target]
lean_lib Audit

-- Explicit historical-only target. Never imported by the current audit root.
lean_lib HistoricalAudit

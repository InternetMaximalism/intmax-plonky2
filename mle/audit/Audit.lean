/-
  Audit.lean — ルートモジュール

  Historical archive: the model targets ee80ee6d with the bee025f9 D3 follow-up.
  PCS binding is assumed and WHIR/transcript behavior is partly abstracted.
  A successful build does not certify the current wire-v3 implementation.
  See README.md for scope and ../README.md for current release conditions.

  lean-formal-audit 段階1 成果物: mle/paper/plonky2_mle_paper_v2.md の
  抽象プロトコル全体の Lean 4 形式化。SCOPE.md 参照。
-/
import Audit.Field
import Audit.Prelude
import Audit.Poly
import Audit.Mle
import Audit.Pcs
import Audit.Transcript
import Audit.Sumcheck
import Audit.Whir
import Audit.Protocol
import Audit.Statements
-- 段階2: 実装対照 (Rust mle/src + Solidity mle/contracts)
import Audit.Impl.RustTranscript
import Audit.Impl.RustSumcheck
import Audit.Impl.RustVerifier
import Audit.Impl.SolVerifier
import Audit.Impl.Divergences
import Audit.Impl.ImplStatements
-- 段階3: 証明
import Audit.Algebra
import Audit.Proofs.SumcheckCore
import Audit.Proofs.Statements
import Audit.Proofs.MleLemmas
import Audit.Proofs.EqPoly
import Audit.Proofs.D3
import Audit.Proofs.D3Strong

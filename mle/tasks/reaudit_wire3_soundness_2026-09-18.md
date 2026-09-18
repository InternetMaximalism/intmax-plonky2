# wire-v3 MLE/WHIR 検証器 健全性再監査（2026-09-18）

対象: 本サブモジュールの親リポジトリ配備ピン `b569e0d7`（Lean 監査ブランチ `e5ece29e` とコードは同一。差分は文書のみ）。
入口: `PinnedMleVerifierV2.verifyCompactPublicInputs` / `fraudVerdictCompact`（親の全呼出しがこの 2 つ）。
攻撃者モデル: **証明バイト列（compact proof・WHIR narg・hint）のみを完全制御**。VK・回路設定・WHIR
プロファイル・chain id はコード常駐で正直。目標は「偽の statement（誤った公開入力、または回路制約を破る
witness）に対する受理」= CRITICAL の探索。

方法: 4 系統の独立調査（各系統がコンパイル・実行済み PoC を作成）と、オーケストレータによる全 PoC の再実行。
Lean 監査（`mle/audit`, 157 モデル / 6542 定理）が意図的に扱わなかった層 — Solidity の転写元である
plonky2 本体との意味論一致、実バイト列に対する Fiat–Shamir 順序、実コード上の置換論証 — を優先した。

## 0. 結論

**CRITICAL / HIGH は見つからなかった。** 4 系統すべてで、証明バイト列のみを制御する攻撃者が偽の statement を
受理させる経路は構成できなかった。これは「不在の証明」ではなく「探索結果」であり、§4 の残余項目が残る。
過去に pre-repair 検証器で実証された 2 件の偽造（root 吸収前の RLC、公開入力ハッシュ未再計算）は、
本コードでバイト単位／行単位に閉じていることを再確認した。

## 1. 攻撃シナリオ台帳（シナリオ → 閉じ方 → 証拠）

| # | シナリオ | 閉じ方 | 証拠 |
|---|---|---|---|
| S1 | MLE 側のゲート制約が plonky2 より弱い（制約欠落・添字ずれ・定数 prefix の除去漏れ） | plonky2 `evaluate_gate_constraints` を真値とする差分。14 族・本番パラメータ（Arithmetic 20 演算, BaseSum 63, Exponentiation 66, Reducing 43, ReducingExt 32, RandomAccess 4bit, Coset 4/6 等）で全スロット一致。Rust→JSON→Solidity Ext3 評価器まで本番 2 設定 × 18 ベクタで一致 | `mle/tests/poc_gates_differential.rs`（2 passed）, `poc_gates_production_vectors.rs`（3 passed）, `contracts/test/PocGateExt3Production.t.sol`（4 passed） |
| S2 | 選択子/フィルタ意味論（`UNUSED_SELECTOR = u32::MAX`, many_selector, α による他ゲート項との打消し） | `compute_filter` は plonky2 の逐語転写。1 行につき非零フィルタは 1 ゲートのみ。`Σ_c α^c C_c` はゲート間でスロット共有だが打消し不能 | `gates.md` §2、mixed-selector ベクタ（全 13 行同時寄与）で一致 |
| S3 | 重複ゲート記録による選択の曖昧化 | plonky2 が `id()` で dedup、`gate_row_index` が記録に含まれ位置一致を要求。証明バイトから到達不能 | `plonky2/src/gates/gate.rs:277-281`, `gate_ext3.rs:446-450`, `Plonky2GateEvaluatorExt3.sol:247-261` |
| S4 | コピー制約違反の witness（ゲート制約は全て満たす） | norm/logUp 恒等式をコードから導出。`x³−2` は Goldilocks 上既約（`2^((p−1)/3) ≡ 4294967295 ≠ 1`）なので `N` は体ノルム、`N(v)=0 ⇔ v=0`。`F_p[B,Γ]` 上の部分分数一意性から多重集合等式 → plonky2 のコピー制約。helper 列は `eq(τ,·)`-重み付き `T·N(D)−1=0` で行ごとに固定 | `poc_perm_copy_constraint.rs`（6 passed）: 1 箇所のみ破った witness（123 制約は全行 0）が `norm/logUp terminal equation failed` で拒否 |
| S5 | 公開入力の差替え（過去偽造 #2） | Poseidon ハッシュを検証器が再計算（`MleVerifierV2.sol:382`）+ `D_PI` 項で VK map の witness セルに直接束縛 | PoC(ii)(iii) 拒否、`PocOuterCanonicality` |
| S6 | 未コミット列 `g^row` の改竄 | 検証器が終端で `subgroup_eval` を VK から自前計算し代入。sumcheck の健全性は検証器が評価できる多項式に対して成立 | `poc_perm_vk_binding.rs` (vii) 拒否 |
| S7 | root 吸収前の RLC（過去偽造 #1） | narg 上で root 0–264、6 claim 264–408、cross-OOD 408–552、**両 RLC の squeeze は 552** | `PocWhirFiatShamir.t.sol`（19 passed）, Rust native trace 照合 |
| S8 | 未束縛の第 6 claim（mask 0x1f）を打消しノブに使う | 代数的には `claim₅ ← claim₅ − δ·vRlc₀cRlc₀/(vRlc₂cRlc₁)` で可能だが、両 RLC は全 claim 吸収後に決まる | mask=0 でも 6 claim 各々の改竄が拒否 |
| S9 | Merkle 葉/内部節点の第二原像、深さ/添字の証明側供給 | 葉長 128/384 ≠ 節点 64、深さ・添字順序はプロファイル固定 | `whir.md` §2 |
| S10 | WHIR パラメータ（クエリ数・PoW・rate）の証明側供給 | ゼロ。n=21: queries [29,19,14,12,10], PoW ≈20–22 bit。仮定は**証明済み Johnson 限界**（推測分岐なし） | `WhirProfilesV2.sol`, `v2_max_resource.json` 再計算一致 |
| S11 | 非正準リム（過去 C2 クラス、`sub(p,X)` の K オフセット） | 全 3 入口で `InvalidMleProof()`（`requireCanonicalLimbs=false` 経路も core が再検査） | `PocOuterCanonicality.t.sol`（9 passed） |
| S12 | transcript 吸収漏れ・順序（evals 吸収前の index point 等） | 20 吸収ステップと 2 系統 challenge の順序が Rust と一致。index point は 6 constituent vector 吸収後 | `outer.md` §2、既存 golden |
| S13 | sumcheck 初期 claim の証明側供給・a₀ 復元誤り | 両系統とも定数 0、`a₀=(claim−Σa_k)·2⁻¹` | `outer.md` §3 |
| S14 | デコーダの別名・末尾無視・オフセット溢れ | 厳密長消費（`CompactMleProofV2.sol:111`）、境界検査 | `outer.md` §7 |
| S15 | WHIR 呼出しに prover 供給値が渡る | 期待値は検証器の fold、点は transcript 由来、root はピン/吸収済み、戻り値検査あり | `MleVerifierV2.sol:357-376` |
| S16 | fraud 判定の誤分類（OOG/パニックが INVALID に） | OOG は常に STARVED、無効証明が VALID/PI_MISMATCH になることなし | `PocOuterFraudVerdict.t.sol` |

## 2. 発見事項（いずれも CRITICAL/HIGH ではない）

- **M-1（MEDIUM・活性/経済、未計測）** `fraudVerdictCompact` は本体が枠の ≈85.9% 未満で拒否した場合のみ
  INVALID を返す。攻撃者は WHIR hint 末尾で拒否を起こし、正直証明の ≈95% のガスを消費させられる
  （envelope 最大フィクスチャで 12.03M vs 12.67M）。調査員の「本番 ≈19M」は外挿であり、本番回路は
  envelope 内（degree_bits ≤ 13, width 160）なので拒否コストの上界は同フィクスチャの ≈12M。親の
  `MIN_MLE_VERIFY_GAS = 25M` と calldata 約 4M を合わせた必要 tx ガスが約 30M 近傍になる点は親側の設計項目。
- **WHIR `_dotEqWithRow`（MEDIUM・到達不能）** `numCols ≤ eqW.length` を検査せず配列外 `mload`。
  `numCommitments==1 && numVectors>1` でのみ到達し、`MleVerifierV2.sol:518` が 3/1 にピン留め。
- **Merkle 葉/節点のドメイン分離なし（INFO）** 葉長 64 は `numVariables==4` のみ。配備回路は ≥ 9。
- **Poseidon 部分ラウンド定数（INFO）** `gate_ext3.rs:848-854` は全 22 ラウンドで定数加算、plonky2 は最終
  ラウンドで加算しない。`FAST_PARTIAL_ROUND_CONSTANTS[21]==0` により値は同一。assert が無い。
- **`epsilon_log` の過大計上（INFO・安全側）** 零分母は完全性事象（`T·N(D)−1=−1` で充足不能）。
- **`permutation/logup.rs` は wire v3 で死コード（INFO）**、`fraudVerdictEncoded` の `staticcall`、
  `test_rustFormalNormLogupTerminalGolden` に Rust 側 producer が無い、等。

## 3. Lean 監査の未証明項目との対応

Lean 側で「意味論の橋が未構築」とされた copy/routing 制約は、本再監査で**コード上の論証と実験**により
閉じた（S4）。ただし Lean の定理ではない。`AssemblyResidue` の同時充足、公開入力束縛の形式化、
Fiat–Shamir grinding の課金は引き続き Lean 側の未完項目。

## 4. 残余（未検証・仮定）

1. coset / bit-reversal 規約の Solidity–Rust 間の自己整合的誤り（最終多項式検査があるため正直
   フィクスチャで検出される類。リスク小だが第一原理からの再導出は未実施）。
2. WHIR 変異 PoC は n=10 のみ（n=21 未実施）。
3. `PoseidonGateExt3.sol` / `CosetInterpolationGateExt3.sol` は挙動同値のみで行単位読解なし。
4. 親リポジトリ側: 返却された公開入力の束縛、証明種別と verifier インスタンスの対応、M-1 の実計測。
5. 文献仮定: WHIR の proximity gap / Johnson 限界、Keccak の ROM 仮定、Fiat–Shamir grinding。
6. `circuit_digest` が `luts` を推移的に含むか（配備回路は lookup 非使用でピン留め）。

## 5. 成果物

再実行ログ（オーケストレータ）: Rust 8 passed（`poc_perm_copy_constraint` 6, `poc_gates_differential` 2）、
Solidity 36 passed（5 スイート）。調査員の詳細報告は
`/Users/andropov/repos/intmax-lean-wire3-candidates/reaudit/{gates,whir,outer,permutation}.md`。

| ファイル | 内容 |
|---|---|
| `mle/tests/poc_gates_differential.rs` | plonky2 `evaluate_gate_constraints` vs `gate_ext3`（14 族） |
| `mle/tests/poc_gates_production_vectors.rs` | 配備 2 設定の gate 表再現 + 本番ベクタ生成 |
| `mle/testdata/poc_gate_ext3_production_vectors.json` | 上記ベクタ（2 設定 × 18） |
| `mle/contracts/test/PocGateExt3Production.t.sol` | Solidity Ext3 評価器の本番パラメータ再生 |
| `mle/tests/poc_perm_copy_constraint.rs` | コピー制約違反・PI 差替え・helper 偽造の拒否 |
| `mle/tests/poc_perm_vk_binding.rs` | sigma 再配線・PI map 再照準・subgroup 列改竄の拒否 |
| `mle/tests/poc_perm_explore.rs` | sigma からコピー類を復号する計装 |
| `mle/contracts/test/PocWhirFiatShamir.t.sol` | 内側 FS 順序・claim 束縛・Merkle/最終検査の変異 |
| `mle/contracts/test/PocWhirDotEqBounds.t.sol` | `_dotEqWithRow` 境界の実証（到達不能） |
| `mle/contracts/test/PocOuterCanonicality.t.sol` | 全入口の非正準リム拒否 |
| `mle/contracts/test/PocOuterFraudVerdict.t.sol` | fraud 判定の列挙とガス計測 |

この文書のみを根拠に「critical な健全性問題なし」を宣言しない（`mle/audit/REPORT.md` の方針に同じ）。

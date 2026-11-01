# GARDEN CANOPY — A FORMAL SELF-DIAGONALIZATION ABOVE LNGN

**日本語プロジェクト名：庭園樹冠数（Garden Canopy Number, GCN）**

このリポジトリは、巨大数庭園数（Large Number Garden Number, LNGN）と同じ関数・同じ初期値を使い、その値を厳密に上回る有限自然数を構成し、Lean 4で一般定理として証明する長期研究プロジェクトです。

## 現在の中心定義

LNGNの公開定義に現れる関数を、同じ意味で解釈した全域関数 \(f:\mathbb N\to\mathbb N\) とします。Knuthの上矢印を用い、

\[
s=10\uparrow^{10}10,\qquad L(f)=f^{10}(s)
\]

と置きます。ここで \(f^k\) は関数合成を k 回行うことです。

有限個の値の最大値を

\[
P_f(n)=\max\{f(0),f(1),\ldots,f(n)\}
\]

とし、増幅関数を

\[
E_f(n)=\max\{n+1,\;2^{n+1},\;P_f(n)+1\}
\]

と定義します。新しい数を

\[
\boxed{\operatorname{GCN}(f)=E_f^{\,L(f)+1}(L(f))}
\]

と定めます。すなわち、E_fをL(f)+1回合成して、L(f)から開始した値です。

## この定義が与える比較

Leanコードは、任意の全域関数 f に対して次の定理を証明します。

\[
\operatorname{GCN}(f)>L(f)
\]

したがって、同じ f と同じ seed で評価する限り、GCNはLNGNを厳密に上回ります。さらに、

\[
\operatorname{GCN}(f)>f(L(f)),\qquad
\operatorname{GCN}(f)\ge 2^{L(f)+1}
\]

も証明します。後者は、少なくともLNGNの値を指数に使った指数関数までGCNが到達することを示します。fの単調性は仮定しません。E_f(n)がnとf(n)の両方を厳密に超えるように設計したためです。

## 重要な定義上の留保

このリポジトリの初期Lean証明は、任意の全域関数 f に関する**条件なしの一般定理**です。しかし、LNGNの元の理論T・Gödel符号化・満足関係・モデル列をLean内に完全移植したものではありません。

したがって現段階では、次の二つを区別します。

1. **証明済みを目指す核：** どの全域関数 f を代入しても GCN(f) > LNGN(f) が成り立つという算術的定理。
2. **未完了の意味論的接続：** 元論文・作者の定義にある f が、Leanで用いる関数と同一の全域関数として構成できることの形式化。

LNGN自体について、Googology Wikiの一覧は2026年時点でもwell-definedness（定義が一意に定まるか）の判定を未確定として扱っています。よって、このプロジェクトもその意味論的問題を解決したと主張しません。GCNの比較は同じ関数解釈を共有する相対比較です。

## プロジェクトの原則

- 定義、意味論、定理、計算実行、CI結果を別々に記録する。
- 未証明の定理を証明済みと表示しない。
- Leanのkernelで検査される証明を優先し、sorry/admit/独自公理で穴を隠さない。
- 「世界最大の有限整数」とは主張しない。有限自然数には常にn+1があるため最大の有限整数は存在しない。
- 「最大級」「圧倒的」は、ここではLNGNとの明示的な大小定理と反復増幅の構造を指し、全ての巨大数記述体系を凌駕するという未証明の主張ではない。

## ディレクトリ

- GardenCanopy.lean — 算術的定義と一般大小定理
- M1_SOURCE_AUDIT.md — 原作者の一次資料・改訂履歴・符号化・M1監査ゲートの固定
- PROOF_SKETCH.md — 高校数学レベルの証明骨子
- LNGN_SPEC.md — LNGNの公開定義、前提、意味論上の未解決点
- FORMALIZATION_STATUS.md — 証明状況と長期タスク
- lakefile.toml / lean-toolchain — 再現可能なLeanプロジェクト設定
- .github/workflows/lean.yml — GitHub Actionsでのビルド

## 参考資料

- [原作者の一次資料](https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理?oldid=61601) — 2019-12-03公開、2023-10-19の修正反映版。詳細なリビジョン固定と採用規則は [M1_SOURCE_AUDIT.md](M1_SOURCE_AUDIT.md)。
- [巨大数庭園数（日本語）](https://googology.fandom.com/ja/wiki/巨大数庭園数) — 定義の二次的整理。
- [Large Number Garden Number（English）](https://googology.fandom.com/wiki/Large_Number_Garden_Number) — 英語版の記述とwell-definednessに関する留保。
- [高階集合論を超えた1階述語論理](https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理) — 作者の元の定義を追うための入口。
- [Growth rates of my functions](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Growth_rates_of_my_functions) — 異なる理論間の比較には共通基礎理論の固定が重要であるという作者の注意。
- [巨大数の話（traP, 2023）](https://trap.jp/post/2040/) — 対角化・高速増大階層の入門的説明。

## 検証

Leanのバージョンは安定版としてLean 4.35.0を固定しています。GitHub ActionsではLean 4.35.0のlake build --wfailに加え、プロジェクト名前空間の公理依存をaxiom-auditで検査します。成功したrunのSHA・ログと対象コミットを必ず対応づけます。

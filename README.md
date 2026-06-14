# Lean4

Lean 4 と [Mathlib4](https://github.com/leanprover-community/mathlib4) を使った、定理証明の学習・演習用リポジトリです。命題論理から自然数・可換モノイド、圏論まで、テーマ別の演習問題を少しずつ解き進めています。

## 環境

- **Lean toolchain**: `leanprover/lean4:v4.27.0-rc1`（[lean-toolchain](lean-toolchain) で固定）
- **ビルドシステム**: [Lake](https://github.com/leanprover/lean4/tree/master/src/lake)（[lakefile.toml](lakefile.toml)）
- **依存**: Mathlib4（`master`）

[.devcontainer/](.devcontainer/) を用意しているので、VS Code の Dev Container でもそのまま開発できます。

## ビルド方法

```bash
# 依存（Mathlib など）の取得
lake exe cache get   # Mathlib のビルド済みキャッシュを取得（推奨）
lake build           # ライブラリと実行ファイルをビルド
lake exe lean4       # Main.lean の main を実行（"Hello!" を表示）
```

## 構成

| ディレクトリ / ファイル | 内容 |
| --- | --- |
| [Lean4/](Lean4/) | メインの演習問題集。`Basic.lean` 系（`Basic_101` 〜 `Basic_961`）と、節ごとの `*_練習問題.lean`、圏論の `Category_001.lean` など |
| [Logic/](Logic/) | 命題論理（[PropLogic.lean](Logic/PropLogic.lean)）と述語論理（[PredLogic.lean](Logic/PredLogic.lean)）の練習 |
| [FirstProof/](FirstProof/) | 自作の自然数 `MyNat` の定義（[NaturalNumber.lean](FirstProof/NaturalNumber.lean)） |
| [NatCommMonoid/](NatCommMonoid/) | `MyNat` を題材にした帰納法・型クラス・`simp`・`ac_rfl` などの演習 |
| [Main.lean](Main.lean) | 実行エントリポイント |
| [Lean4.lean](Lean4.lean) | ライブラリのルートモジュール |

## 演習の進め方

- `Basic_*.lean` は 15 問前後のまとまりで構成され、各問題は `sorry` / `TODO` を埋める形式です。
- 多くは Mathlib を使わずに（`import Init.Classical` 程度で）解けるよう、前のファイルで定義した補題を再利用しながら積み上げています。
- 圏論の問題（[Category_001.lean](Lean4/Category_001.lean)）は Mathlib の `CategoryTheory` を使い、`simp` / `simpa` / `rfl` から試すのが基本方針です。

進捗は各コミットの「◯◯まで完了」というメッセージで管理しています。

--------------------------------------------------------------------------------
-- Basic_651.lean
-- 演習問題 651〜700（keys付きRel合成の代数 / transpose / Hadamard / graph / multi-head / spec）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 601〜650 は Basic_601 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_601

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wTrans / wMul / wScale / wId / wGraph / WSpec）
--------------------------------------------------------------------------------

-- WRel の transpose（引数をひっくり返す）
def wTrans {α β : Type} (R : WRel α β) : WRel β α :=
  fun b a => R a b

-- WRel の要素積（Hadamard 積）
def wMul {α β : Type} (R S : WRel α β) : WRel α β :=
  fun a b => R a b * S a b

-- スカラー倍（Nat）
def wScale {α β : Type} (t : Nat) (R : WRel α β) : WRel α β :=
  fun a b => t * R a b

-- WRel の（0/1）恒等（maskW を使うので noncomputable）
noncomputable def wId (X : Type) : WRel X X :=
  maskW (relId X)

-- 関数 f の graph を 0/1 の WRel にしたもの（maskW を使うので noncomputable）
noncomputable def wGraph {α β : Type} (f : α → β) : WRel α β :=
  maskW (relGraph f)

-- 「仕様 T の外は重み 0」という意味の weighted-spec
def WSpec {α β : Type} (R : WRel α β) (T : Rel α β) : Prop :=
  ∀ a b, ¬ T a b → R a b = 0

--------------------------------------------------------------------------------
-- 651〜660：relCompList / relInKeys の “代数”
--------------------------------------------------------------------------------

-- 651：空 keys の relCompList は空関係
theorem ex651 (R : Rel α β) (S : Rel β γ) :
    relCompList ([] : List β) R S = (relBot α γ) := by

  funext a1 g1
  dsimp [relCompList, relBot]
  apply propext
  constructor
  intro h
  obtain ⟨b, hb, hR, hS⟩ := h
  cases hb
  intro h
  contradiction

-- 652：cons 展開（head で当たるか tail に流す）
theorem ex652 (b : β) (keys : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList (b :: keys) R S
      =
    relAdd (fun a c => R a b ∧ S b c) (relCompList keys R S) := by

  funext a1 g1
  dsimp [relCompList, relAdd]
  apply propext
  constructor
  intro h
  obtain ⟨b1, hb1, hR, hS⟩ := h





-- 653：singleton keys の relCompList
theorem ex653 (b : β) (R : Rel α β) (S : Rel β γ) :
    relCompList [b] R S = (fun a c => R a b ∧ S b c) := by
  -- TODO
  sorry

-- 654：append 分解（keys を 2 ブロックに分けると OR）
theorem ex654 (keys1 keys2 : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList (keys1 ++ keys2) R S
      =
    relAdd (relCompList keys1 R S) (relCompList keys2 R S) := by
  -- TODO
  sorry

-- 655：keys の単調性（候補が増えるほど relCompList は増える）
theorem ex655 (keys keys' : List β) (R : Rel α β) (S : Rel β γ) :
    (∀ b, b ∈ keys → b ∈ keys') →
      relCompList keys R S ⊆ relCompList keys' R S := by
  -- TODO
  sorry

-- 656：R/S の単調性（R⊆R', S⊆S' なら relCompList も ⊆）
theorem ex656 (keys : List β) (R R' : Rel α β) (S S' : Rel β γ) :
    (R ⊆ R') → (S ⊆ S') →
      relCompList keys R S ⊆ relCompList keys R' S' := by
  -- TODO
  sorry

-- 657：左の和（∨）に分配：relCompList keys (R+R') S = ...
theorem ex657 (keys : List β) (R R' : Rel α β) (S : Rel β γ) :
    relCompList keys (relAdd R R') S
      =
    relAdd (relCompList keys R S) (relCompList keys R' S) := by
  -- TODO
  sorry

-- 658：右の和（∨）に分配：relCompList keys R (S+S') = ...
theorem ex658 (keys : List β) (R : Rel α β) (S S' : Rel β γ) :
    relCompList keys R (relAdd S S')
      =
    relAdd (relCompList keys R S) (relCompList keys R S') := by
  -- TODO
  sorry

-- 659：relCompList の結合（2段 witness の並べ替え）
theorem ex659 (keysβ : List β) (keysg : List γ)
    (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    relCompList keysg (relCompList keysβ R S) T
      =
    relCompList keysβ R (relCompList keysg S T) := by
  -- TODO
  sorry

-- 660：relInKeys の append は OR になる
theorem ex660 (keys1 keys2 : List β) :
    relInKeys (α:=α) (keys1 ++ keys2)
      =
    relAdd (relInKeys (α:=α) keys1) (relInKeys (α:=α) keys2) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 661〜670：wTrans / wMul（Hadamard）/ wCompList との相性
--------------------------------------------------------------------------------

-- 661：wTrans は 2 回で元に戻る
theorem ex661 (R : WRel α β) :
    wTrans (wTrans R) = R := by
  -- TODO
  sorry

-- 662：wTrans は wAdd と可換
theorem ex662 (R S : WRel α β) :
    wTrans (wAdd R S) = wAdd (wTrans R) (wTrans S) := by
  -- TODO
  sorry

-- 663：wTrans は wZero と可換
theorem ex663 :
    wTrans (wZero α β) = wZero β α := by
  -- TODO
  sorry

-- 664：wTrans は wMask と可換（mask 側は transpose する）
theorem ex664 (R : WRel α β) (M : Rel α β) :
    wTrans (wMask R M) = wMask (wTrans R) (relTrans M) := by
  -- ヒント：by classical; funext b a; simp [wTrans, wMask, maskW, relTrans]
  -- TODO
  sorry

-- 665：transpose は縮約の順序を逆にする（weighted 版）
theorem ex665 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wTrans (wCompList keys R S) = wCompList keys (wTrans S) (wTrans R) := by
  -- ヒント：Nat.mul_comm が本体
  -- TODO
  sorry

-- 666：support は transpose と可換
theorem ex666 (R : WRel α β) :
    wSupp (wTrans R) = relTrans (wSupp R) := by
  -- TODO
  sorry

-- 667：support(Hadamard) は ∧ になる
theorem ex667 (R S : WRel α β) :
    wSupp (wMul R S) = relMul (wSupp R) (wSupp S) := by
  -- ヒント：Nat の積の正（ex608）を使う
  -- TODO
  sorry

-- 668：wMul の可換
theorem ex668 (R S : WRel α β) :
    wMul R S = wMul S R := by
  -- TODO
  sorry

-- 669：wMul の結合
theorem ex669 (R S T : WRel α β) :
    wMul (wMul R S) T = wMul R (wMul S T) := by
  -- TODO
  sorry

-- 670：wMul は wAdd に分配（点ごと）
theorem ex670 (R S T : WRel α β) :
    wMul (wAdd R S) T = wAdd (wMul R T) (wMul S T) := by
  -- ヒント：Nat.add_mul
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 671〜680：wId / wGraph（0/1 行列）と support / keys
--------------------------------------------------------------------------------

-- 671：support(wId) = relId
theorem ex671 :
    wSupp (wId α) = relId α := by
  -- ヒント：wId = maskW (relId α)、ex613 を使う
  -- TODO
  sorry

-- 672：wId を左から縮約すると「a ∈ keys」のときだけ通る（左単位の keys 版）
theorem ex672 (keys : List α) (R : WRel α β) :
    wCompList keys (wId α) R = wMask R (fun a _ => a ∈ keys) := by
  -- TODO
  sorry

-- 673：wId を右から縮約すると「b ∈ keys」のときだけ通る（右単位の keys 版）
theorem ex673 (keys : List β) (R : WRel α β) :
    wCompList keys R (wId β) = wMask R (relInKeys (α:=α) keys) := by
  -- TODO
  sorry

-- 674：keys が α 全体を含むなら（左）真の単位になる
theorem ex674 (keys : List α) (R : WRel α β) :
    (∀ a, a ∈ keys) → wCompList keys (wId α) R = R := by
  -- ヒント：ex672 を使って mask が常に True になることを示す
  -- TODO
  sorry

-- 675：keys が β 全体を含むなら（右）真の単位になる
theorem ex675 (keys : List β) (R : WRel α β) :
    (∀ b, b ∈ keys) → wCompList keys R (wId β) = R := by
  -- TODO
  sorry

-- 676：support(wGraph f) = relGraph f
theorem ex676 (f : α → β) :
    wSupp (wGraph f) = relGraph f := by
  -- ヒント：wGraph = maskW (relGraph f)、ex613
  -- TODO
  sorry

-- 677：graph を左に置いた縮約の support は “f a が keys にいる” で潰れる
theorem ex677 (keys : List β) (f : α → β) (S : WRel β γ) :
    ∀ a c,
      wSupp (wCompList keys (wGraph f) S) a c
        ↔ (f a ∈ keys ∧ wSupp S (f a) c) := by
  -- ヒント：ex621（support(attn)=relCompList）→ witness b を b=f a に潰す
  -- TODO
  sorry

-- 678：graph を右に置いた縮約の support は “c = g b” で潰れる
theorem ex678 (keys : List β) (R : WRel α β) (g : β → γ) :
    ∀ a c,
      wSupp (wCompList keys R (wGraph g)) a c
        ↔ (∃ b, b ∈ keys ∧ wSupp R a b ∧ g b = c) := by
  -- TODO
  sorry

-- 679：graph-graph の縮約（support 版）
theorem ex679 (keys : List β) (f : α → β) (g : β → γ) :
    ∀ a c,
      wSupp (wCompList keys (wGraph f) (wGraph g)) a c
        ↔ (f a ∈ keys ∧ g (f a) = c) := by
  -- TODO
  sorry

-- 680：keys が十分大きいと graph の合成がそのまま（support で）
theorem ex680 (keys : List β) (f : α → β) (g : β → γ) :
    (∀ b, b ∈ keys) →
      wSupp (wCompList keys (wGraph f) (wGraph g)) = relGraph (fun a => g (f a)) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 681〜690：multi-head（wAdd）とスカラー倍（wScale）
--------------------------------------------------------------------------------

-- 681：QK を足した attention の support は OR（multi-head の基本）
theorem ex681 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys (wAdd QK1 QK2) KV)
      =
    relAdd (wSupp (wCompList keys QK1 KV)) (wSupp (wCompList keys QK2 KV)) := by
  -- ヒント：ex511（線形性）→ ex612（support(R+S)=∨）
  -- TODO
  sorry

-- 682：KV を足した attention の support も OR
theorem ex682 (keys : List β) (QK : WRel α β) (KV1 KV2 : WRel β γ) :
    wSupp (wCompList keys QK (wAdd KV1 KV2))
      =
    relAdd (wSupp (wCompList keys QK KV1)) (wSupp (wCompList keys QK KV2)) := by
  -- TODO
  sorry

-- 683：各 head の到達は “sum-head” の到達に含まれる（片側）
theorem ex683 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) :
    wSupp (wCompList keys QK1 KV) ⊆ wSupp (wCompList keys (wAdd QK1 QK2) KV) := by
  -- ヒント：wCompList の WLe 単調性＋ ex615（WLe→supp包含）でも可
  -- TODO
  sorry

-- 684：両 head が spec を満たせば sum-head も満たす
theorem ex684 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (wCompList keys QK1 KV) ⊆ T) →
    (wSupp (wCompList keys QK2 KV) ⊆ T) →
    (wSupp (wCompList keys (wAdd QK1 QK2) KV) ⊆ T) := by
  -- ヒント：ex681 で OR にして cases
  -- TODO
  sorry

-- 685：sum-head が spec を満たすなら、各 head も満たす
theorem ex685 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (wCompList keys (wAdd QK1 QK2) KV) ⊆ T) →
      (wSupp (wCompList keys QK1 KV) ⊆ T) ∧ (wSupp (wCompList keys QK2 KV) ⊆ T) := by
  -- ヒント：ex683（包含）で落とす
  -- TODO
  sorry

-- 686：wMask は wAdd に分配する（点ごと分配）
theorem ex686 (R S : WRel α β) (M : Rel α β) :
    wMask (wAdd R S) M = wAdd (wMask R M) (wMask S M) := by
  -- ヒント：Nat.add_mul
  -- TODO
  sorry

-- 687：mask してから multi-head しても、multi-head してから mask しても同じ（重みレベル）
theorem ex687 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (M : Rel α β) :
    wCompList keys (wMask (wAdd QK1 QK2) M) KV
      =
    wAdd (wCompList keys (wMask QK1 M) KV) (wCompList keys (wMask QK2 M) KV) := by
  -- ヒント：ex686 → ex511
  -- TODO
  sorry

-- 688：wScale 0 はゼロ
theorem ex688 (R : WRel α β) :
    wScale 0 R = wZero α β := by
  -- TODO
  sorry

-- 689：t>0 なら、スカラー倍しても support は変わらない
theorem ex689 (t : Nat) (R : WRel α β) :
    (t > 0) → wSupp (wScale t R) = wSupp R := by
  -- ヒント：Nat.mul_pos と「¬(m>0)→m=0」など
  -- TODO
  sorry

-- 690：左側をスカラー倍すると、縮約結果もスカラー倍される（線形性）
theorem ex690 (keys : List β) (t : Nat) (R : WRel α β) (S : WRel β γ) :
    wCompList keys (wScale t R) S = wScale t (wCompList keys R S) := by
  -- ヒント：ex539/ex538（Σ と * の交換）＋ Nat.mul_assoc
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 691〜700：WSpec（「仕様の外は0」）と安全設計の “重みレベル” 表現
--------------------------------------------------------------------------------

-- 691：WSpec は「support ⊆ T」と同値
theorem ex691 (R : WRel α β) (T : Rel α β) :
    WSpec R T ↔ (wSupp R ⊆ T) := by
  -- ヒント：
  --   (→) : wSupp R a b は R a b >0。T でなければ R a b=0 になって矛盾。
  --   (←) : ¬T なら ¬(R>0) なので Nat.eq_zero_of_not_pos で 0。
  -- TODO
  sorry

-- 692：wZero は任意の spec を満たす
theorem ex692 (T : Rel α β) :
    WSpec (wZero α β) T := by
  -- TODO
  sorry

-- 693：同じ spec なら足しても spec を満たす
theorem ex693 (R S : WRel α β) (T : Rel α β) :
    WSpec R T → WSpec S T → WSpec (wAdd R S) T := by
  -- TODO
  sorry

-- 694：要素積（Hadamard）は spec を ∧ で細くする
theorem ex694 (R S : WRel α β) (T U : Rel α β) :
    WSpec R T → WSpec S U → WSpec (wMul R S) (relMul T U) := by
  -- TODO
  sorry

-- 695：mask すると spec は保たれる（むしろ強くなる）
theorem ex695 (R : WRel α β) (T : Rel α β) (M : Rel α β) :
    WSpec R T → WSpec (wMask R M) T := by
  -- ヒント：wMask ≤ R を使ってもよい
  -- TODO
  sorry

-- 696：support(QK) ⊆ (supp(KV)▷T) なら、attn の重みは T の外で 0
theorem ex696 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp QK ⊆ rRes (wSupp KV) T) →
      WSpec (attnWRel keys QK KV) T := by
  -- ヒント：ex622（support ⊆ T）＋ ex691（WSpec↔support⊆）
  -- TODO
  sorry

-- 697：安全マスク（residual）を入れると、必ず WSpec を満たす（重みレベル）
theorem ex697 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    WSpec (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) T := by
  -- ヒント：ex650（support ⊆ T）＋ ex691
  -- TODO
  sorry

-- 698：spec は右に単調（T ⊆ T' なら WSpec R T → WSpec R T'）
theorem ex698 (R : WRel α β) (T T' : Rel α β) :
    (T ⊆ T') → WSpec R T → WSpec R T' := by
  -- TODO
  sorry

-- 699：spec を 2 つ同時に満たすなら、∧ も満たす（tightening）
theorem ex699 (R : WRel α β) (T U : Rel α β) :
    WSpec R T → WSpec R U → WSpec R (relMul T U) := by
  -- TODO
  sorry

-- 700：入力側/出力側の spec があると、縮約後の spec は relComp で表せる
theorem ex700 (keys : List β) (R : WRel α β) (S : WRel β γ)
    (T : Rel α β) (U : Rel β γ) :
    WSpec R T → WSpec S U → WSpec (wCompList keys R S) (relComp T U) := by
  -- ヒント：support(wCompList) ⊆ relCompList ⊆ relComp を経由して ex691 へ
  -- TODO
  sorry

end TL

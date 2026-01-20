--------------------------------------------------------------------------------
-- Basic_601.lean
-- 演習問題 601〜650（support/boolean化/keys付き縮約/残余による安全設計）
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 551〜600 は Basic_551 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_551

namespace TL

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（support / keys 付き Rel 合成）
--------------------------------------------------------------------------------

-- WRel を「正の場所だけ True」にして Rel に落とす（support / boolean化）

-- 空/全の Rel（便利）

-- keys : List β を witness の候補として固定した Rel の合成
-- 「∃ b, b ∈ keys ∧ R a b ∧ S b c」
def relCompList {α β γ : Type} (keys : List β) (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, b ∈ keys ∧ R a b ∧ S b c

-- keys 制約（b ∈ keys）を Rel として切り出す（mask 的に使う）
def relInKeys {α β : Type} (keys : List β) : Rel α β :=
  fun _ b => b ∈ keys

--------------------------------------------------------------------------------
-- 601〜610：wsum の補題（存在⇔正、0⇔全0 など）
--------------------------------------------------------------------------------

-- 601：wsum の ext（リスト中の点ごとの一致で和が一致）
theorem ex601 {X : Type} (xs : List X) (f g : X → Nat) :
    (∀ x, x ∈ xs → f x = g x) → wsum xs f = wsum xs g := by
  -- TODO
  sorry

-- 602：wsum の定数和（k を length 回足す）
theorem ex602 {X : Type} (xs : List X) (k : Nat) :
    wsum xs (fun _ => k) = k * xs.length := by
  -- TODO
  sorry

-- 603：map との交換
theorem ex603 {X Y : Type} (xs : List X) (g : X → Y) (f : Y → Nat) :
    wsum (xs.map g) f = wsum xs (fun x => f (g x)) := by
  -- TODO
  sorry

-- 604：∃ (mem かつ正) なら wsum は正
theorem ex604 {X : Type} (xs : List X) (f : X → Nat) :
    (∃ x, x ∈ xs ∧ f x > 0) → wsum xs f > 0 := by
  -- TODO
  sorry

-- 605：wsum が正なら ∃ (mem かつ正)
theorem ex605 {X : Type} (xs : List X) (f : X → Nat) :
    wsum xs f > 0 → (∃ x, x ∈ xs ∧ f x > 0) := by
  -- TODO
  sorry

-- 606：まとめ：wsum xs f > 0 ↔ ∃x∈xs, f x > 0
theorem ex606 {X : Type} (xs : List X) (f : X → Nat) :
    (wsum xs f > 0) ↔ (∃ x, x ∈ xs ∧ f x > 0) := by
  -- TODO（ex604/ex605 を使うのが自然）
  sorry

-- 607：wsum xs f = 0 ↔ ∀x∈xs, f x = 0
theorem ex607 {X : Type} (xs : List X) (f : X → Nat) :
    wsum xs f = 0 ↔ (∀ x, x ∈ xs → f x = 0) := by
  -- TODO（ex606 と「>0 でない」ことの言い換え等）
  sorry

-- 608：Nat の積の正（積>0 ↔ 両方>0）
theorem ex608 (m n : Nat) :
    (m * n > 0) ↔ (m > 0 ∧ n > 0) := by
  -- TODO
  sorry

-- 609：Nat の和の正（和>0 ↔ どちらか>0）
theorem ex609 (m n : Nat) :
    (m + n > 0) ↔ (m > 0 ∨ n > 0) := by
  -- TODO
  sorry

-- 610：Nat の積が 0（m*n=0 ↔ m=0 ∨ n=0）
theorem ex610 (m n : Nat) :
    (m * n = 0) ↔ (m = 0 ∨ n = 0) := by
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 611〜620：WRel を Rel に落とす（support）と、keys 合成（relCompList）
--------------------------------------------------------------------------------

-- 611：support(0) は空関係
theorem ex611 :
    wSupp (wZero α β) = (relBot α β) := by
  -- TODO
  sorry

-- 612：support(R+S) は「support R ∨ support S」
theorem ex612 (R S : WRel α β) :
    wSupp (wAdd R S) = relAdd (wSupp R) (wSupp S) := by
  -- TODO（ex609 を使う）
  sorry

-- 613：support(maskW M) は M そのもの
theorem ex613 (M : Rel α β) :
    wSupp (maskW M) = M := by
  -- ヒント：by classical; funext a b; by_cases h : M a b <;> simp [maskW, wSupp, h]
  -- TODO
  sorry

-- 614：support(wMask R M) は「support R ∧ M」
theorem ex614 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) = relMul (wSupp R) M := by
  -- ヒント：by classical; funext a b; by_cases h : M a b <;> simp [wMask, maskW, wSupp, h]
  -- TODO
  sorry

-- 615：WLe なら support は包含（R≤S ⇒ supp R ⊆ supp S）
theorem ex615 (R S : WRel α β) :
    WLe R S → (wSupp R ⊆ wSupp S) := by
  -- ヒント：dsimp [WLe, RelLe, wSupp]; intro h a b hpos; exact Nat.lt_of_lt_of_le hpos (h a b)
  -- TODO
  sorry

-- 616：relCompList は普通の relComp に含まれる（keys 制約を捨てる）
theorem ex616 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList keys R S ⊆ relComp R S := by
  -- TODO
  sorry

-- 617：wCompList が正なら、どこかの b∈keys で項が正
theorem ex617 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    ∀ a c,
      wSupp (wCompList keys R S) a c →
        (∃ b, b ∈ keys ∧ (R a b * S b c) > 0) := by
  -- ヒント：dsimp [wSupp, wCompList] at *; ex605 を f := (fun b => R a b * S b c) に適用
  -- TODO
  sorry

-- 618：項が正なら両因子も正（R a b * S b c > 0 ⇒ R a b>0 ∧ S b c>0）
theorem ex618 (R : WRel α β) (S : WRel β γ) :
    ∀ a b c, (R a b * S b c > 0) → (R a b > 0 ∧ S b c > 0) := by
  -- ヒント：ex608 を使う
  -- TODO
  sorry

-- 619：support(wCompList) ⊆ relCompList(support R)(support S)
theorem ex619 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys R S) ⊆ relCompList keys (wSupp R) (wSupp S) := by
  -- ヒント：a c を取り、ex617→ex618 で ∃b∈keys ∧ suppR ∧ suppS を作る
  -- TODO
  sorry

-- 620：逆向き：relCompList(suppR)(suppS) ⊆ support(wCompList)
theorem ex620 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    relCompList keys (wSupp R) (wSupp S) ⊆ wSupp (wCompList keys R S) := by
  -- ヒント：∃b∈keys から、(R a b * S b c)>0 を作って ex604 へ
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 621〜630：Attention（wCompList）を support で Rel 的に見る／安全仕様
--------------------------------------------------------------------------------

-- 621：support(attnWRel) の具体形（relCompList になる）
theorem ex621 (keys : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (attnWRel keys QK KV) = relCompList keys (wSupp QK) (wSupp KV) := by
  -- ヒント：attnWRel は wCompList の別名。ex619/ex620 を両方向で
  -- TODO
  sorry

-- 622：仕様 T に対する安全条件（support(QK) ⊆ (supp(KV) ▷ T) ⇒ support(attn) ⊆ T）
theorem ex622 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp QK ⊆ rRes (wSupp KV) T) →
    (wSupp (attnWRel keys QK KV) ⊆ T) := by
  -- ヒント：ex621 で support(attn) を relCompList にし、witness b で rRes を叩く
  -- TODO
  sorry

-- 623：mask すると support は必ず M に入る（supp(wMask R M) ⊆ M）
theorem ex623 (R : WRel α β) (M : Rel α β) :
    wSupp (wMask R M) ⊆ M := by
  -- ヒント：ex614 で supp(wMask) = suppR ∧ M にして右射影
  -- TODO
  sorry

-- 624：残余で作った安全マスク：QKsafe := wMask QK (KV ▷ T)
--      ⇒ support(attn QKsafe KV) ⊆ T
theorem ex624 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex623 で supp(QKsafe) ⊆ rRes(...); それを ex622 へ
  -- TODO
  sorry

-- 625：仕様を強めると安全マスクは単調（T ⊆ T' ⇒ (KV▷T) ⊆ (KV▷T')）
theorem ex625 (KV : WRel β γ) (T T' : Rel α γ) :
    (T ⊆ T') → (rRes (wSupp KV) T ⊆ rRes (wSupp KV) T') := by
  -- ヒント：Basic_451 の ex483 を使う（S := wSupp KV）
  -- TODO
  sorry

-- 626：KV 側を強める（到達先が増える）と安全マスクは厳しくなる（反単調）
theorem ex626 (KV KV' : WRel β γ) (T : Rel α γ) :
    (wSupp KV ⊆ wSupp KV') → (rRes (wSupp KV') T ⊆ rRes (wSupp KV) T) := by
  -- ヒント：Basic_451 の ex484 を使う
  -- TODO
  sorry

-- 627：WLe(QK,QK') なら support(QK) ⊆ support(QK')
theorem ex627 (QK QK' : WRel α β) :
    WLe QK QK' → (wSupp QK ⊆ wSupp QK') := by
  -- ヒント：ex615
  -- TODO
  sorry

-- 628：WLe の両側単調性で attnWRel も単調（重みそのもの）
theorem ex628 (keys : List β) (QK QK' : WRel α β) (KV KV' : WRel β γ) :
    WLe QK QK' → WLe KV KV' → WLe (attnWRel keys QK KV) (attnWRel keys QK' KV') := by
  -- ヒント：Basic_501 側の “wCompList は両側単調”（ex548 相当）を使う
  -- TODO
  sorry

-- 629：重みの単調性から support でも単調（attn の到達先が増える）
theorem ex629 (keys : List β) (QK QK' : WRel α β) (KV KV' : WRel β γ) :
    WLe QK QK' → WLe KV KV' →
    (wSupp (attnWRel keys QK KV) ⊆ wSupp (attnWRel keys QK' KV')) := by
  -- ヒント：ex628 → ex615
  -- TODO
  sorry

-- 630：keys を増やす（append）と support は増える（下から単調）
theorem ex630 (keys more : List β) (R : WRel α β) (S : WRel β γ) :
    wSupp (wCompList keys R S) ⊆ wSupp (wCompList (keys ++ more) R S) := by
  -- ヒント：a c を固定し、ex604/ex605 を使って “同じ witness b” を append 側へ持ち上げる（mem_append）
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 631〜640：mask と縮約の相互作用（設計向け：≤ や「keys 上でだけ True」など）
--------------------------------------------------------------------------------

-- 631：右側をマスクしても合成結果は増えない（右版 ex549）
theorem ex631 (keys : List β) (R : WRel α β) (S : WRel β γ) (N : Rel β γ) :
    WLe (wCompList keys R (wMask S N)) (wCompList keys R S) := by
  -- ヒント：wsum の単調性（ex503）＋ 1項ずつ “マスクしても増えない”（ex524/ex533 相当）
  -- TODO
  sorry

-- 632：両側マスクでも増えない
theorem ex632 (keys : List β)
    (R : WRel α β) (M : Rel α β) (S : WRel β γ) (N : Rel β γ) :
    WLe (wCompList keys (wMask R M) (wMask S N)) (wCompList keys R S) := by
  -- ヒント：ex549 と ex631 を WLe の推移で合成
  -- TODO
  sorry

-- 633：keys 上では常に True なマスクは（その keys の縮約に限って）消せる
theorem ex633 (keys : List β) (R : WRel α β) (M : Rel α β) (S : WRel β γ) :
    (∀ a b, b ∈ keys → M a b) →
    wCompList keys (wMask R M) S = wCompList keys R S := by
  -- ヒント：各項で if_pos を使って maskW=1 を示し、wsum を ext（ex601）で押す
  -- TODO
  sorry

-- 634：keys 制約（relInKeys）でマスクしても wCompList は変わらない
theorem ex634 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wCompList keys (wMask R (relInKeys (α:=α) keys)) S = wCompList keys R S := by
  -- ヒント：ex633 を M := relInKeys keys に適用（a は捨てられる）
  -- TODO
  sorry

-- 635：Rel 側でも同様：relCompList keys R S = relComp (R ∧ inKeys) S
theorem ex635 (keys : List β) (R : Rel α β) (S : Rel β γ) :
    relCompList keys R S = relComp (relMul R (relInKeys (α:=α) keys)) S := by
  -- TODO
  sorry

-- 636：keys-residuation（片方向）
-- (relCompList keys R S ⊆ T) → (relMul R (inKeys keys) ⊆ (S ▷ T))
theorem ex636 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relCompList keys R S ⊆ T) →
    (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) := by
  -- ヒント：a b ⟨hR, hmem⟩ を取り、c と hS から relCompList の witness を作って仮定へ
  -- TODO
  sorry

-- 637：keys-residuation（逆方向）
-- (relMul R (inKeys keys) ⊆ (S ▷ T)) → (relCompList keys R S ⊆ T)
theorem ex637 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) →
    (relCompList keys R S ⊆ T) := by
  -- ヒント：witness b を取り、仮定を b に適用
  -- TODO
  sorry

-- 638：keys-residuation（同値）
theorem ex638 (keys : List β) (R : Rel α β) (S : Rel β γ) (T : Rel α γ) :
    (relCompList keys R S ⊆ T) ↔
      (relMul R (relInKeys (α:=α) keys) ⊆ rRes S T) := by
  -- TODO（ex636/ex637）
  sorry

-- 639：WRel 側の「安全設計」を keys-residuation で読む（support 版）
theorem ex639 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (attnWRel keys QK KV) ⊆ T) ↔
      (relMul (wSupp QK) (relInKeys (α:=α) keys) ⊆ rRes (wSupp KV) T) := by
  -- ヒント：ex621 で supp(attn) を relCompList へ、ex638 を適用
  -- TODO
  sorry

-- 640：spec を満たす “最大の（keys 制約つき）QK-support” を書く
-- QKmax := (inKeys keys) ∧ (KV ▷ T) とすると relCompList keys QKmax (supp KV) ⊆ T
theorem ex640 (keys : List β) (KV : WRel β γ) (T : Rel α γ) :
    relCompList keys (relMul (relInKeys (α:=α) keys) (rRes (wSupp KV) T)) (wSupp KV) ⊆ T := by
  -- ヒント：ex637 を R := (relInKeys keys) ∧ (rRes (supp KV) T) に適用（右射影で rRes を得る）
  -- TODO
  sorry

--------------------------------------------------------------------------------
-- 641〜650：まとめ（support/keys/残余/マスク）を “Attention をテンソル論理で表す” 方向へ
--------------------------------------------------------------------------------

-- 641：QKsafe := wMask QK ((supp KV) ▷ T) は「keys-residuation」視点で最小限の修正
theorem ex641 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    relMul (wSupp (wMask QK (rRes (wSupp KV) T))) (relInKeys (α:=α) keys)
      ⊆ rRes (wSupp KV) T := by
  -- ヒント：ex623（supp(wMask) ⊆ mask条件）＋ ∧ の右射影
  -- TODO
  sorry

-- 642：ex641 を使って、attn の仕様を一行で示せる形
theorem ex642 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex639 の (→) か (←) をうまく使う（どちらでも可）
  -- TODO
  sorry

-- 643：mask の合成（AND 化）：wMask (wMask R M1) M2 = wMask R (M1 ∧ M2)
theorem ex643 (R : WRel α β) (M1 M2 : Rel α β) :
    wMask (wMask R M1) M2 = wMask R (fun a b => M1 a b ∧ M2 a b) := by
  -- ヒント：Basic_501 の ex543 相当を再利用してOK
  -- TODO
  sorry

-- 644：安全マスクの “重ね掛け” は 1 回に潰せる（設計の簡約）
theorem ex644 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T1 T2 : Rel α γ) :
    attnWRel keys
      (wMask (wMask QK (rRes (wSupp KV) T1)) (rRes (wSupp KV) T2))
      KV
    =
    attnWRel keys
      (wMask QK (fun a b => rRes (wSupp KV) T1 a b ∧ rRes (wSupp KV) T2 a b))
      KV := by
  -- ヒント：ex643 で QK 側を整理
  -- TODO
  sorry

-- 645：仕様も AND でまとめられる（T := T1 ∧ T2）
theorem ex645 (KV : WRel β γ) (T1 T2 : Rel α γ) :
    rRes (wSupp KV) (fun a c => T1 a c ∧ T2 a c)
      =
    relMul (rRes (wSupp KV) T1) (rRes (wSupp KV) T2) := by
  -- ヒント：Basic_401 の rRes の定義展開で一直線（∀c の中の ∧）
  -- TODO
  sorry

-- 646：上の 2 つを合わせて “複数仕様” の安全設計を 1 本化（見通し）
theorem ex646 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T1 T2 : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) (fun a c => T1 a c ∧ T2 a c))) KV)
      ⊆ (fun a c => T1 a c ∧ T2 a c) := by
  -- ヒント：ex642 を T := (T1 ∧ T2) で適用
  -- TODO
  sorry

-- 647：keys を 2 ブロックに分けた attn の support は OR になる（Rel 視点）
theorem ex647 (keys1 keys2 : List β) (QK : WRel α β) (KV : WRel β γ) :
    wSupp (attnWRel (keys1 ++ keys2) QK KV)
      =
    relAdd (wSupp (attnWRel keys1 QK KV)) (wSupp (attnWRel keys2 QK KV)) := by
  -- ヒント：ex621 で relCompList へ、append は mem_append で OR になる
  -- TODO
  sorry

-- 648：keys 分割の spec 検証：両ブロックが T を満たせば全体も T
theorem ex648 (keys1 keys2 : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    (wSupp (attnWRel keys1 QK KV) ⊆ T) →
    (wSupp (attnWRel keys2 QK KV) ⊆ T) →
    (wSupp (attnWRel (keys1 ++ keys2) QK KV) ⊆ T) := by
  -- ヒント：ex647 で OR に分解し、cases で流す
  -- TODO
  sorry

-- 649：最終チェック：support 視点の “multi-head + residual safety” の基本形
-- 2-head の QK を足し、残余で安全化しても spec を満たす
theorem ex649 (keys : List β) (QK1 QK2 : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask (wAdd QK1 QK2) (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex642 を QK := (QK1+QK2) で適用
  -- TODO
  sorry

-- 650：まとめ：このファイルの “設計式” を 1 行で言う（文章の代わりの定理）
-- 「support(attn) ⊆ T を保証したいなら、QK を (supp KV ▷ T) でマスクせよ」
theorem ex650 (keys : List β) (QK : WRel α β) (KV : WRel β γ) (T : Rel α γ) :
    wSupp (attnWRel keys (wMask QK (rRes (wSupp KV) T)) KV) ⊆ T := by
  -- ヒント：ex642 そのもの（exact ex642 _ _ _ _ でもOK）
  -- TODO
  sorry

end TL

--------------------------------------------------------------------------------
-- Basic_841.lean
-- 演習問題 841〜855（fast-track 7：reach-sum semantics / wId・wGraph と到達テンソル）
--
-- ※ import Mathlib なし
-- ※ 解答は入れない（全部 TODO / sorry）
-- ※ 826〜840 は Basic_826 を import して再利用
--------------------------------------------------------------------------------

import Init.Classical
import Lean4.Basic_826

namespace TL

-- NOTE:
-- `if ... then ... else ...` や `decide (...)` を式の中で使うため、
-- Prop の決定可能性が必要です。
open Classical
attribute [local instance] Classical.propDecidable

variable {α β γ δ ε : Type}

--------------------------------------------------------------------------------
-- 0) このファイルで追加する定義（wsumW：WRel の “OR-和”）
--------------------------------------------------------------------------------

-- keys 上で「各 b の行列を足してから 0/1 に潰す」和
-- （0/1 行列を入れたときは “OR” に対応する）
--
--   wsumW keys F a c = if (Σ b∈keys, F b a c) > 0 then 1 else 0
noncomputable def wsumW (keys : List β) (F : β → WRel α γ) : WRel α γ :=
  wBool (fun a c => wsum keys (fun b => F b a c))

--------------------------------------------------------------------------------
-- 841〜845：wsumW の基本計算規則 / reach を “OR-和” で表す
--------------------------------------------------------------------------------

-- 841：空の OR-和は 0
theorem ex841 (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) ([] : List β) F = wZero α γ := by
  -- TODO
  -- ヒント：
  --   * funext a c; dsimp [wsumW, wBool]; dsimp [wsum]
  --   * wBool で 0 は 0/1 に潰しても 0
  sorry

-- 842：cons の計算（1 項 + tail の OR-和）
theorem ex842 (b : β) (keys : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) (b :: keys) F
      =
    wBool (wAdd (F b) (fun a c => wsum keys (fun b => F b a c))) := by
  -- TODO
  -- ヒント：
  --   * dsimp [wsumW]; dsimp [wsum]
  --   * funext a c; rfl まで持っていく
  sorry

-- 843：右が graph の reach は “各 b の列選択” を OR-和したもの
theorem ex843 (keys : List β) (R : WRel α β) (g : β → γ) :
    wReachComp keys R (wGraph g)
      =
    wsumW keys (fun b => wMask (fun a c => wBool R a b) (fun _ c => g b = c)) := by
  -- TODO
  -- ヒント：
  --   * wsumW の定義を展開すると “各 b について足す”
  --   * 0/1 同士の和→最後に wBool（maskW）へ
  --   * まずは “support（到達）” で同値を示す方が楽
  sorry

-- 844：一般版：reach は “各 b の AND（固定 b）” を OR-和したもの
theorem ex844 (keys : List β) (R : WRel α β) (S : WRel β γ) :
    wReachComp keys R S
      =
    wsumW keys (fun b =>
      wMask (fun a c => wBool R a b) (fun _ c => wSupp S b c)) := by
  -- TODO
  -- ヒント：
  --   * ex833（reach = maskW(∃ b∈keys, ... )）を使うと楽
  --   * wsumW は「∃ b∈keys, 項>0」を表していることを示す（ex606 を使う）
  --   * wMask で “S b c > 0” を掛けていると思えばよい
  sorry

-- 845：wsumW の意味論：OR-和の 0/1 は「どれか 1 つでも >0」
theorem ex845 (keys : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) keys F
      =
    maskW (fun a c => ∃ b, b ∈ keys ∧ F b a c > 0) := by
  -- TODO
  -- ヒント：
  --   * dsimp [wsumW, wBool, maskW, wSupp]
  --   * ex606 を xs:=keys, f:=fun b => F b a c に適用
  --   * funext a c; by_cases h : (∃ b, b ∈ keys ∧ F b a c > 0)
  --     で if の枝をそろえる
  sorry

--------------------------------------------------------------------------------
-- 846〜850：wId / wGraph と reach を wsumW で観察（行選択・列選択）
--------------------------------------------------------------------------------

-- 846：右が wId の reach は「列 b を選ぶテンソル」を OR-和したもの
theorem ex846 (keys : List β) (R : WRel α β) :
    wReachComp keys R (wId β)
      =
    wsumW keys (fun b => wMask (fun a c => wBool R a b) (fun _ c => b = c)) := by
  -- TODO
  -- ヒント：
  --   * ex843 に g := fun b => b を入れる
  --   * wGraph (fun b => b) = wId β（定義展開で示せる）
  sorry

-- 847：左が wId の reach を wsumW で書く（行を 1 本ずつ OR-和）
theorem ex847 (keys : List α) (S : WRel α γ) :
    wReachComp keys (wId α) S
      =
    wsumW keys (fun a0 =>
      wMask (fun a c => if a = a0 then 1 else 0) (fun _ c => wSupp S a0 c)) := by
  -- TODO
  -- ヒント：
  --   * ex844 に R := wId α を入れる
  --   * wBool (wId α) a a0 は if a = a0 then 1 else 0
  sorry

-- 848：左が graph の reach（行選択の到達版）
theorem ex848 (keys : List β) (f : α → β) (S : WRel β γ) :
    wReachComp keys (wGraph f) S
      =
    wMask (fun a c => wBool S (f a) c) (fun a _ => f a ∈ keys) := by
  -- TODO
  -- ヒント：
  --   * これは ex832 と同じステートメント（再掲）
  --   * もしくは ex844（sum 版）から、graph の一意性で b を f a に潰す
  sorry

-- 849：graph-graph の reach（関数合成 + keys マスク）
theorem ex849 (keys : List β) (f : α → β) (g : β → γ) :
    wReachComp keys (wGraph f) (wGraph g)
      =
    maskW (fun a c => f a ∈ keys ∧ g (f a) = c) := by
  -- TODO
  -- ヒント：ex835 と同じ（再掲）
  sorry

-- 850：keys が {f a} を全て含むなら、graph の reach はマスクが消える
theorem ex850 (keys : List β) (f : α → β) (S : WRel β γ) :
    (∀ a : α, f a ∈ keys) →
      wReachComp keys (wGraph f) S
        =
      (fun a c => wBool S (f a) c) := by
  -- TODO
  -- ヒント：
  --   * ex836 を funext でまとめる
  --   * あるいは ex848 を使って wMask の条件を if_pos で消す
  sorry

--------------------------------------------------------------------------------
-- 851〜855：wsumW の代数（transpose / append / 重複 / 単調性）
--------------------------------------------------------------------------------

-- 851：transpose と wsumW は可換
theorem ex851 (keys : List β) (F : β → WRel α γ) :
    wTrans (wsumW (α:=α) (β:=β) (γ:=γ) keys F)
      =
    wsumW (α:=γ) (β:=β) (γ:=α) keys (fun b => wTrans (F b)) := by
  -- TODO
  -- ヒント：
  --   * funext c a; dsimp [wsumW, wTrans]
  --   * まずは wSupp（>0）が同じことを示すのが楽
  --   * wSupp(wBool _) は元と同じ（ex796）
  sorry

-- 852：append は OR（bool-sum）になる
theorem ex852 (keys₁ keys₂ : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) (keys₁ ++ keys₂) F
      =
    wBool (wAdd (wsumW (α:=α) (β:=β) (γ:=γ) keys₁ F)
                (wsumW (α:=α) (β:=β) (γ:=γ) keys₂ F)) := by
  -- TODO
  -- ヒント：
  --   * ex845 で両辺を maskW(∃...) に落とすのが楽
  --   * “∃ b∈(xs++ys), ...” は xs 側 / ys 側に分解できる
  --   * 0/1 の OR は wBool(wAdd ...) で表せる（ex755 / ex820 など）
  sorry

-- 853：同じ b を 2 回足しても OR なので変わらない
theorem ex853 (b : β) (keys : List β) (F : β → WRel α γ) :
    wsumW (α:=α) (β:=β) (γ:=γ) (b :: b :: keys) F
      =
    wsumW (α:=α) (β:=β) (γ:=γ) (b :: keys) F := by
  -- TODO
  -- ヒント：
  --   * ex845 による “∃ b∈...” の形で見れば明らか
  --   * List.mem_cons / or_assoc などで整理
  sorry

-- 854：keys 上で全部 0（到達なし）なら OR-和も 0
theorem ex854 (keys : List β) (F : β → WRel α γ) :
    (∀ b, b ∈ keys → F b = wZero α γ) →
      wsumW (α:=α) (β:=β) (γ:=γ) keys F = wZero α γ := by
  -- TODO
  -- ヒント：
  --   * ex845 で maskW(∃ b∈keys, ...) に落とし、∃ を否定して if_neg
  --   * あるいは ex607（wsum=0 ↔ 全項=0）を使ってもよい
  sorry

-- 855：単調性：各 b で F b ≤ G b なら OR-和も ≤
theorem ex855 (keys : List β) (F G : β → WRel α γ) :
    (∀ b, WLe (F b) (G b)) →
      WLe (wsumW (α:=α) (β:=β) (γ:=γ) keys F)
          (wsumW (α:=α) (β:=β) (γ:=γ) keys G) := by
  -- TODO
  -- ヒント：
  --   * ex615（WLe→support包含）と ex845（wsumW=maskW(∃...)）を使うのが楽
  --   * 最後は ex801（maskW M ≤ R ↔ M ⊆ wSupp R）などでもよい
  sorry

end TL



-- 演習問題１

example (P : Prop) : (¬P → P) → P := by

  intro np_to_p

  apply Classical.byContradiction

  intro np

  have p : P := np_to_p np

  have f: False := np p

  exact f



-- 演習問題２

example (P : Prop) : P ∨ ¬P := by

  apply Classical.byContradiction

  intro h_not_em -- 「P ∨ ¬P」ではない、という仮定

  -- ここからどうやって False を導き出すか...

  apply h_not_em

  by_cases p : P

  left

  exact p

  right

  exact p



-- 演習問題２ （別解）

example (P : Prop) : P ∨ ¬P := by

  apply Classical.byContradiction

  intro h_not_em -- 「P ∨ ¬P」ではない、という仮定

  -- ここからどうやって False を導き出すか...

  apply h_not_em

  right

  intro hp

  apply h_not_em

  left

  exact hp



-- 演習問題３

example (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) := by

  intro a

  apply Classical.byContradiction

  intro h_not

  apply a

  constructor

  apply Classical.byContradiction

  intro nhp

  apply h_not

  left

  exact nhp

  apply Classical.byContradiction

  intro nhq

  apply h_not

  right

  exact nhq



-- 演習問題 4：カリー化

example (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → (Q → R)) := by

  constructor

  intro p_and_q_to_r

  intro hp

  intro hq

  have p_and_q : P ∧ Q := by

    constructor

    exact hp

    exact hq

  apply p_and_q_to_r

  exact p_and_q

  intro p_to_q_to_r

  intro p_and_q

  apply p_to_q_to_r

  exact p_and_q.left

  exact p_and_q.right



-- 演習問題 5：分配則（∧ over ∨）

example (P Q R : Prop) : (P ∧ (Q ∨ R)) → (P ∧ Q) ∨ (P ∧ R) := by

  intro p_and_q_or_r

  have hp : P := p_and_q_or_r.left

  have q_or_r : Q ∨ R := p_and_q_or_r.right

  cases p_and_q_or_r.right with

  | inl hq =>

    left

    constructor

    exact hp

    exact hq

  | inr hr =>

    right

    constructor

    exact hp

    exact hr



-- 演習問題 6：ド・モルガンの法則（逆向き）

-- ※前回解いた問題の逆方向です。こちらは背理法なしで解けます。

example (P Q : Prop) : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by

  intro not_p_or_not_q

  intro p_and_q

  have hp : P := by

    exact p_and_q.left

  have hq : Q := by

    exact p_and_q.right

  cases not_p_or_not_q with

  | inl not_p =>

    apply not_p

    exact hp

  | inr not_q =>

    apply not_q

    exact hq



-- 演習問題 7：もう一つのド・モルガン

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by

  constructor

  intro not_p_or_q

  constructor

  intro hp

  apply not_p_or_q

  left

  exact hp

  intro hq

  apply not_p_or_q

  right

  exact hq

  intro not_p_and_not_q

  intro p_or_q

  have not_p : ¬ P := by

    exact not_p_and_not_q.left

  have not_q : ¬ Q := by

    exact not_p_and_not_q.right

  cases p_or_q with

  | inl hp =>

    apply not_p

    exact hp

  | inr hq =>

    apply not_q

    exact hq



-- 第2グループ：古典論理（背理法が必要）

-- 演習問題 8：二重否定除去

example (P : Prop) : ¬ ¬ P ↔ P := by

  constructor

  intro not_not_p

  apply Classical.byContradiction

  intro not_p

  apply not_not_p

  exact not_p

  intro p

  intro not_p

  apply not_p

  exact p



-- 演習問題 9：対偶（完全版）

example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by

  constructor

  intro p_to_q

  intro not_q

  intro hp

  apply not_q

  apply p_to_q

  exact hp

  intro not_q_to_not_p

  intro hp

  apply Classical.byContradiction

  intro not_q

  have not_p : ¬ P := by

    apply not_q_to_not_p

    exact not_q

  apply not_p

  exact hp



-- 演習問題 10：ならばの書き換え

example (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by

  constructor

  intro p_to_q

  by_cases hp : P

  have hq : Q := by

    apply p_to_q

    exact hp

  right

  exact hq

  left

  exact hp

  intro not_p_or_q

  intro hp

  cases not_p_or_q with

  | inl not_p =>

    apply False.elim

    apply not_p

    exact hp

  | inr hq =>

    exact hq



-- 第3グループ：論理学の難問（パズル難易度：高）

-- 演習問題 11：パースの法則（Peirce's Law）

example (P Q : Prop) : ((P → Q) → P) → P := by

  by_cases hp : P

  intro a

  exact hp

  intro b

  apply b

  intro c

  apply False.elim

  apply hp

  exact c



-- 演習問題 12：ならばの否定

example (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q := by

  constructor

  intro a

  constructor

  apply Classical.byContradiction

  intro not_p

  apply a

  intro hp

  apply False.elim

  apply not_p

  exact hp

  intro hq

  apply a

  intro hp

  exact hq

  intro b

  intro c

  have hp : P := by

    exact b.left

  have not_q : ¬ Q := by

    exact b.right

  have hq : Q := by

    apply c

    exact hp

  apply not_q

  exact hq



-- 演習問題 13：含意の分配（古典論理の真骨頂）

example (P Q R : Prop) : (P → Q ∨ R) → (P → Q) ∨ (P → R) := by

  intro a

  by_cases p : P

  have q_or_r : Q ∨ R := by

    apply a

    exact p

  cases q_or_r with

  | inl hq =>

    left

    intro a

    exact hq

  | inr hr =>

    right

    intro b

    exact hr

  left

  intro hp

  apply False.elim

  apply p

  exact hp

variable {α : Type} -- 議論の対象となる「型」（集合のようなもの）



-- 演習問題 14：全称量化子（∀）と「かつ（∧）」

-- 「全てのxについて、PかつQ」は、「全てのxについてP」かつ「全てのxについてQ」と同じです。

example (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by

  constructor

  intro a

  constructor

  intro b

  have pb_and_qb : P b ∧ Q b := by

    apply a

  have pb : P b := by

    exact pb_and_qb.left

  exact pb

  intro c

  have pc_and_qc : P c ∧ Q c := by

    apply a

  have qc : Q c := by

    exact pc_and_qc.right

  exact qc

  intro d

  intro e

  have f: ∀ (x : α), P x := by

    exact d.left

  have g : ∀ (x : α), Q x := by

    exact d.right

  have pe : P e := by

    apply f

  have qe : Q e := by

    apply g

  constructor

  exact pe

  exact qe



-- 演習問題 15：存在量化子（∃）の導入

-- 「Pを満たす具体的な a がある」なら、「ある x が存在して P x」と言えます。

-- ヒント: apply Exists.intro a を使ってみてください

example (P : α → Prop) (a : α) : P a → ∃ x, P x := by

  intro b

  exists a



-- 演習問題 16：存在量化子（∃）の利用

-- 「全ての x で PならQ」であり、「Pな x が存在する」なら、「Qな x も存在する」はずです。

-- ヒント: cases h_ex with | intro x hp => で「存在」の中身を取り出せます

example (P Q : α → Prop) : (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) := by

  intro a

  intro b

  obtain ⟨x, px⟩ := b

  have b : P x → Q x := by

    apply a

  have qx : Q x := by

    apply b

    exact px

  exists x



-- 演習問題 17：量化子の順序交換

-- 「ある x がいて、全ての y に対して R x y」なら

-- 「全ての y に対して、R x y となるような x が存在する（さっきのxを使えばいい）」

example (R : α → α → Prop) : (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) := by

  intro a

  intro b

  have e : ∃ x, R x b := by

    obtain ⟨c, d⟩ := a

    have rcb : R c b := by

      apply d

    exists c

  obtain ⟨f, g⟩ := e

  exists f



-- 演習問題 18：量化子のド・モルガン（直観主義論理で言える版）

-- 「存在しない」は「全てについて～ではない」と同じです。

-- この証明は背理法なし（直観主義論理）で解けます。

example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by

  constructor

  intro a

  intro b

  intro c

  apply a

  exists b

  intro d

  intro e

  obtain ⟨f, g⟩ := e

  have not_pf : ¬ P f := by

    apply d

  apply not_pf

  exact g



-- 演習問題 19：推移律

-- AならばB、BならばC。では、Aならば？

example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by

  intro a

  intro b

  intro c

  apply b

  apply a

  exact c



-- 演習問題 20：または（∨）の含意

-- 「PかQならばR」は、「PならばR、かつ、QならばR」と同じです。

example (P Q R : Prop) : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by

  constructor

  intro a

  constructor

  intro b

  apply a

  left

  exact b

  intro c

  apply a

  right

  exact c

  intro d

  intro e

  have p_to_r : P → R := by

    exact d.left

  have q_to_r : Q → R := by

    exact d.right

  cases e with

  | inl hp =>

    apply p_to_r

    exact hp

  | inr hq =>

    apply q_to_r

    exact hq



-- 演習問題 21：古典論理のパズル

-- 「PならばQ」あるいは「QならばP」。直観的には変ですが、古典論理では真です。

-- ヒント: by_cases p : P を使ってみましょう。

example (P Q : Prop) : (P → Q) ∨ (Q → P) := by

  by_cases p : P

  by_cases q : Q

  left

  intro a

  exact q

  right

  intro b

  exact p

  by_cases q : Q

  left

  intro c

  exact q

  left

  intro d

  apply False.elim

  apply p

  exact d



-- 演習問題 22：全称量化子の分配

-- 全員が「PならQ」を満たし、かつ全員が「P」を満たすなら、全員「Q」なはずです。

example (P Q : α → Prop) : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by

  intro a

  intro b

  intro c

  apply a

  apply b



-- 演習問題 23：存在量化子の入れ替え

-- 「ある x と y のペアがいる」なら、順序を変えてもペアは存在します。

example (R : α → α → Prop) : (∃ x, ∃ y, R x y) → ∃ y, ∃ x, R x y := by

  intro a

  obtain ⟨x, ⟨y, rxy⟩⟩ := a

  exists y

  exists x



-- 演習問題 24：存在と「または」

-- 「PまたはQな奴がいる」と「Pな奴がいる、または、Qな奴がいる」は同じです。

example (P Q : α → Prop) : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by

  constructor

  intro a

  obtain ⟨x, p_or_q⟩ := a

  cases p_or_q with

  | inl hp =>

    left

    exists x

  | inr hq =>

    right

    exists x

  intro b

  cases b with

  | inl ex_p =>

    obtain ⟨x, hp⟩ := ex_p

    exists x

    left

    exact hp

  | inr ex_q =>

    obtain ⟨x, hq⟩ := ex_q

    exists x

    right

    exact hq



-- 演習問題 25：全称と「かつ」

-- これは演習14の再確認です。スラスラ書けるかチェック！

example (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by

  constructor

  intro a

  constructor

  intro b

  have pb_and_qb : P b ∧ Q b := by

    apply a

  have pb : P b := by

    exact pb_and_qb.left

  exact pb

  intro c

  have pc_and_qc : P c ∧ Q c := by

    apply a

  have qc : Q c := by

    exact pc_and_qc.right

  exact qc

  intro d

  intro e

  have f:  ∀ (x : α), P x := by

    exact d.left

  have g : ∀ (x : α), Q x := by

    exact d.right

  constructor

  apply f

  apply g



-- 演習問題 26：量化子と定数

-- Q は x に依存しない命題です。

-- 「(ある x がいて P x) ならば Q」は、「全ての x について (P x ならば Q)」と同じです。

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) → Q) ↔ (∀ x, P x → Q) := by

  constructor

  intro a

  intro b

  intro c

  apply a

  exists b

  intro d

  intro e

  obtain ⟨f, g⟩ := e

  have h : P f → Q := by

    apply d

  apply h

  apply g



-- 演習問題 27：全称量化子のド・モルガン（古典論理版）

-- 演習18の逆です。「全てP、ではない」なら「Pじゃない奴が少なくとも一人いる」。

-- これは背理法 (Classical.byContradiction) が必要になる難問です。

example (P : α → Prop) : ¬ (∀ x, P x) → ∃ x, ¬ P x := by

  intro a

  apply Classical.byContradiction

  intro b

  apply a

  intro c

  apply Classical.byContradiction

  intro d

  apply b

  exists c



-- 演習問題 28：パラドックス？

-- 「私は嘘つきだ」と私が言うことはありえるでしょうか？

-- P と ¬P が等価になることはない、という証明です。

example (P : Prop) : ¬ (P ↔ ¬ P) := by

  intro a

  have b : P → ¬ P := by

    intro c

    rw [← a]

    exact c

  have d : ¬ P → P := by

    intro e

    rw [a]

    exact e

  by_cases p : P

  have f : ¬ P := by

    apply b

    exact p

  apply f

  exact p

  apply p

  apply d

  exact p



-- 演習問題 29：対偶と量化子

-- 「PならQ」が全員成り立つとき、「Qじゃない奴がいる」なら「Pじゃない奴がいる」。

-- ヒント: obtain で「Qじゃない奴」を取り出し、その人に全称命題を適用します。

example (P Q : α → Prop) : (∀ x, P x → Q x) → (∃ x, ¬ Q x) → (∃ x, ¬ P x) := by

  intro a

  intro b

  obtain ⟨c, d⟩ := b

  have e : P c → Q c := by

    intro f

    apply a

    exact f

  apply Classical.byContradiction

  intro g

  apply d

  apply e

  apply Classical.byContradiction

  intro h

  apply g

  exists c



-- 演習問題 30：ド・モルガンの法則（命題論理・古典）

-- 「PかつQ」ではない ↔ 「Pじゃない」または「Qじゃない」。

-- 右から左は簡単ですが、左から右（→）は背理法か対偶が必要です。

example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by

  constructor

  intro a

  apply Classical.byContradiction

  intro b

  apply a

  constructor

  apply Classical.byContradiction

  intro c

  apply b

  left

  exact c

  apply Classical.byContradiction

  intro d

  apply b

  right

  exact d

  intro e

  intro f

  have g : P := by

    exact f.left

  have h : Q := by

    exact f.right

  cases e with

  | inl not_p =>

    apply not_p

    exact g

  | inr not_q =>

    apply not_q

    exact h



-- 演習問題 31：存在量化子の分配（または）

-- 「PかQな奴がいる」は「Pな奴がいる、または、Qな奴がいる」と完全に同じです。

-- iff (↔) なので双方向の証明が必要です。cases と left/right の練習です。

example (P Q : α → Prop) : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by

  constructor

  intro a

  obtain ⟨b, c⟩ := a

  cases c with

  | inl hp =>

    left

    exists b

  | inr hq =>

    right

    exists b

  intro d

  cases d with

  | inl ex_p =>

    obtain ⟨e, f⟩ := ex_p

    exists e

    left

    exact f

  | inr ex_q =>

    obtain ⟨g, h⟩ := ex_q

    exists g

    right

    exact h



-- 演習問題 32：量化子のスコープ（全称）

-- A は x に関係ない命題です。

-- 「Aならば（全員 P x）」は、「全員について（Aならば P x）」と同じです。

-- これは直観主義論理で証明可能です。

example (P : α → Prop) (A : Prop) : (A → ∀ x, P x) ↔ (∀ x, A → P x) := by

  constructor

  intro a

  intro b

  intro c

  have d : ∀ (x : α), P x := by

    apply a

    exact c

  apply d

  intro e

  intro f

  intro g

  apply e

  exact f



-- 演習問題 33：量化子のスコープ（存在・難問）

-- 「(ある x がいて P x) ならば A」 ↔ 「全ての x について (P x ならば A)」

-- 演習26の変形版です。左から右、右から左、混乱せずにいけるでしょうか？

example (P : α → Prop) (A : Prop) : ((∃ x, P x) → A) ↔ (∀ x, P x → A) := by

  constructor

  intro a

  intro b

  intro c

  apply a

  exists b

  intro d

  intro e

  obtain ⟨f, g⟩ := e

  have h : P f → A := by

    apply d

  apply h

  exact g



-- 演習問題 34：古典論理の証明（Consequentia Mirabilis）

-- 「Pじゃないと仮定するとPになっちゃう」なら、Pは真です。

-- パースの法則の親戚のような問題です。背理法 (byContradiction) を使いましょう。

example (P : Prop) : (¬ P → P) → P := by

  intro a

  by_cases p : P

  exact p

  apply a

  exact p



-- 演習問題 35：複雑な三段論法

-- 条件が分岐していますが、結局どちらの道を行っても S にたどり着きます。

-- cases をうまく使って道を切り開いてください。

example (P Q R S : Prop) : (P → Q ∨ R) → (Q → S) → (R → S) → P → S := by

  intro a

  intro b

  intro c

  intro d

  have e : Q ∨ R := by

    apply a

    exact d

  cases e with

  | inl hq =>

    apply b

    exact hq

  | inr hr =>

    apply c

    exact hr

variable [Inhabited α]



-- 演習問題 36：ドリンカーのパラドックス（超難問）

-- 「酒場に、ある人物 x がいて、『もし x が飲むなら、全員飲む』というふざけた理屈が成り立つ」

-- 古典論理の有名な定理です。「全員飲むか、飲まない奴がいるか」で by_cases してみてください。

example (D : α → Prop) : ∃ x, (D x → ∀ y, D y) := by

  by_cases h : ∀ y, D y

  exists default

  intro a

  exact h

  have b : ∃ y, ¬ D y := by

    apply Classical.byContradiction

    intro c

    apply h

    intro d

    apply Classical.byContradiction

    intro e

    apply c

    exists d

  obtain ⟨f, g⟩ := b

  exists f

  intro h

  apply False.elim

  apply g

  exact h



-- 演習問題 37：全称量化子と「または」の結合（古典）

-- 「全員がP、または、A」↔「(全員がP) または A」。

-- 左から右（→）が非常に難しいです。A が真か偽かで by_cases するのが定石です。

example (P : α → Prop) (A : Prop) : (∀ x, P x ∨ A) ↔ (∀ x, P x) ∨ A := by

  by_cases a : A

  constructor

  intro b

  right

  exact a

  intro c

  intro d

  right

  exact a

  constructor

  intro e

  left

  intro f

  have g : P f ∨ A := by

    apply e

  have h : P f := by

    cases g with

    | inl hp =>

      exact hp

    | inr ha =>

      apply False.elim

      apply a

      exact ha

  exact h

  intro i

  intro j

  left

  have k : (∀ (x : α), P x) := by

    cases i with

    | inl all_p =>

      exact all_p

    | inr a_true =>

      apply False.elim

      apply a

      exact a_true

  apply k



-- 演習問題 38：二重否定の除去と量化子

-- 「全員 P x」の否定の否定は、「全員 P x」です（古典論理において）。

-- 演習18や27の総決算です。

example (P : α → Prop) : ¬¬ (∀ x, P x) → ∀ x, P x := by

  intro a

  intro b

  apply Classical.byContradiction

  intro c

  apply a

  intro d

  apply c

  apply d



variable (a b c d : Nat)



-- 演習問題 39：書き換えの基本

-- 足し算の順序を入れ替えます。

-- ヒント: rw [Nat.add_comm]

example : a + b = b + a := by

  rw [Nat.add_comm]



-- 演習問題 40：結合法則

-- カッコの位置を変えます。

-- ヒント: rw [Nat.add_assoc]

example : (a + b) + c = a + (b + c) := by

  rw [Nat.add_assoc]



-- 演習問題 41：場所を指定して書き換える

-- ゴールには (a + b) が2箇所ありますが、Leanは「最初に見つけた場所」しか変えません。

-- 2回 rw すれば両方変わります。

example : a + b + (a + b) = b + a + (b + a) := by

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]

  rw [Nat.add_comm]

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]



-- 演習問題 42：仮定を使った書き換え

-- 等式 h : a = b を使って、ゴールの a を b に変身させます。

-- ヒント: rw [h]

example : a = b → a + c = b + c := by

  intro d

  rw [d]



-- 演習問題 43：仮定「を」書き換える

-- ゴールはそのままで、手持ちの仮定 h の形を変えてゴールに近づけます。

-- ヒント: rw [Nat.add_comm] at h

example : a + b = c → b + a = c := by

  intro d

  rw [Nat.add_comm]

  exact d



-- 演習問題 44：逆向きの書き換え

-- h を使って、ゴールの右辺 b を a に戻してください。

-- ヒント: rw [← h]

example : a = b → a + c = b + c := by

  intro d

  rw [← d]



-- 演習問題 45：交換法則の指名手配

-- カッコの中の (b + c) だけを (c + b) にしたいです。

-- 普通に rw [Nat.add_comm] すると、一番外側の a + ... がひっくり返ってしまいます。

-- ヒント: rw [Nat.add_comm b c]

example : a + (b + c) = a + (c + b) := by

  rw [Nat.add_comm b c]



-- 演習問題 46：結合と交換のコンボ

-- 3つの数を完全に逆順にします。

-- ヒント: assoc でカッコをずらし、comm で交換し... パズルのように解きます。

example : (a + b) + c = c + b + a := by

  rw [Nat.add_comm]

  rw [Nat.add_comm a b]

  rw [Nat.add_assoc]



-- 演習問題 47：掛け算の結合法則

-- 掛け算 (mul) も足し算と同じように assoc や comm が使えます。

-- ヒント: rw [Nat.mul_assoc]

example : (a * b) * c = a * (b * c) := by

  rw [Nat.mul_assoc]



-- 演習問題 48：分配法則（展開）

-- 掛け算の分配法則を使います。

-- ヒント: rw [Nat.left_distrib]

example : a * (b + c) = a * b + a * c := by

  rw [Nat.left_distrib]



------------------------------------------------------------------------------------------------



-- 演習問題 49：ゼロの足し算

-- 基本中の基本です。

-- ヒント: rw [Nat.add_zero]

example : a + 0 = a := by

  rw [Nat.add_zero]



-- 演習問題 50：ゼロの掛け算（消滅）

-- どんなに複雑でも 0 を掛ければ 0 です。

-- ヒント: rw [Nat.mul_zero]

example : (a + b) * 0 = 0 := by

  rw [Nat.mul_zero]



-- 演習問題 51：イチの掛け算（お掃除）

-- 1 を掛けても変わらないので、消してスッキリさせます。

-- ヒント: one_mul, mul_one を組み合わせてください。

example : 1 * a * 1 = a := by

  rw [Nat.one_mul]

  rw [Nat.mul_one]



-- 演習問題 52：複合お掃除

-- 0 は消えて、1 も消えます。

-- ヒント: 順番に rw していけば自然と解けます。

example : (a + 0) * (1 * b) = a * b := by

  rw [Nat.add_zero]

  rw [Nat.one_mul]



-- 演習問題 53：因数分解の準備（逆書き換え）

-- ここは発想の転換が必要です。

-- 「a」単体を、「a * 1」という形に **戻して** (←)、共通因数を作れるようにします。

-- ヒント: rw [← Nat.mul_one a]

example : a = a * 1 := by

  rw [Nat.mul_one a]



------------------------------------------------------------------------------------------------



-- 演習問題 54：因数分解の基本

-- a * b + a を a * (b + 1) に変形します。

-- ヒント: まず右側の a を a * 1 に変えて (← mul_one)、それから分配法則の逆 (← left_distrib) を使います。

example : a * b + a = a * (b + 1) := by

  rw[Nat.left_distrib]

  rw[Nat.mul_one a]



-- 演習問題 55：逆順の因数分解

-- a + a * b を a * (1 + b) に変形します。

-- さっきと項の順番が逆ですが、やることは同じです。

example : a + a * b = a * (1 + b) := by

  rw[Nat.left_distrib]

  rw[Nat.mul_one a]



-- 演習問題 56：展開（分配法則）

-- 今度は逆に、カッコを開きます。

-- a * (b + 1) を a * b + a に戻してください。

-- ヒント: rw [Nat.left_distrib], rw [Nat.mul_one]

example : a * (b + 1) = a * b + a := by

  rw[Nat.left_distrib]

  rw[Nat.mul_one a]



-- 演習問題 57：右からの展開

-- (a + 1) * b を展開します。

-- ヒント: rw [Nat.right_distrib]

example : (a + 1) * b = a * b + b := by

  rw[Nat.right_distrib]

  rw[Nat.one_mul b]



-- 演習問題 58：足し算を掛け算に

-- a + a は、a が 2つあるので a * (1 + 1) と同じです。

-- これも因数分解の一種です。両方の a に「隠れた1」を見つけましょう。

example : a + a = a * (1 + 1) := by

  rw[Nat.left_distrib]

  rw[Nat.mul_one a]



------------------------------------------------------------------------------------------------



-- 演習問題 59：交換法則との組み合わせ

-- b * a + a を a * (b + 1) に変形します。

-- さっきやった因数分解ですが、 b * a の順番が逆です。

-- ヒント: まず a * b に直してから (← mul_comm)、さっきと同じ手順です。

example : b * a + a = a * (b + 1) := by

  rw[Nat.left_distrib]

  rw[Nat.mul_one]

  rw[Nat.mul_comm b a]



-- 演習問題 60：ゼロの性質との組み合わせ

-- (a + 0) * (b + 1) を展開して整理します。

-- ヒント: まずカッコの中の + 0 を消しましょう (← add_zero)。

-- その後、展開 (← left_distrib) して、最後に * 1 を消します (← mul_one)。

example : (a + 0) * (b + 1) = a * b + a := by

  rw[Nat.left_distrib]

  rw[Nat.add_zero]

  rw[Nat.mul_one]



-- 演習問題 61：足し算の交換法則

-- a * b + a * c を a * (c + b) にまとめます。

-- ヒント: まず分配法則の逆 (← left_distrib) でまとめると a * (b + c) になります。

-- でもゴールは (c + b) なので、カッコの中を入れ替える必要があります (← add_comm)。

example : a * b + a * c = a * (c + b) := by

  rw[Nat.left_distrib]

  rw[Nat.add_comm]



-- 演習問題 62：3つの項（結合法則）

-- a * b + a + a を a * (b + 2) にしたいところですが、まずは a * (b + 1 + 1) を目指します。

-- ヒント: 左から順番に因数分解していきます。

-- まず前の2つ (a * b + a) をまとめます。そのあと、もう一度残りの + a とまとめます。

-- ※ rw [Nat.left_distrib] を2回使うことになるはずです。

example : a * b + a + a = a * (b + 1 + 1) := by

  rw[Nat.left_distrib]

  rw[Nat.left_distrib]

  rw[Nat.mul_one a]



-- 演習問題 63：右側からの展開と交換

-- (1 + b) * a を a + b * a に変形します。

-- ヒント: 右からの分配法則 (← right_distrib) を使い、

-- 1 * a をきれいにし (← one_mul)、最後に足し算の順番を入れ替えます (← add_comm)。

example : (1 + b) * a = a + b * a := by

  rw[Nat.right_distrib]

  rw[Nat.one_mul]



------------------------------------------------------------------------------------------------



-- 演習問題 64：掛け算の結合法則

-- (a * b) * c を a * (b * c) に変えます。

-- 実はこれが Nat.mul_assoc そのものです。

example : (a * b) * c = a * (b * c) := by

  rw[Nat.mul_assoc]



-- 演習問題 65：結合法則と交換法則のコンボ

-- (a * b) * c を b * (a * c) に変形します。

-- ヒント: まずカッコを組み替えて (← mul_assoc)、次に a と b を入れ替えます (← mul_comm)。

-- どの項を入れ替えるか、よく見て指定してください。

example : (a * b) * c = b * (a * c) := by

  rw[Nat.mul_comm a b]

  rw[Nat.mul_assoc]



-- 演習問題 66：足し算の結合法則

-- a + (b + c) を (a + b) + c に戻します。

-- Nat.add_assoc は「(a + b) + c = ...」という向きなので、

-- 逆方向に使うときは ← をつけます (rw [← Nat.add_assoc])。

example : a + (b + c) = (a + b) + c := by

  rw [Nat.add_assoc]



-- 演習問題 67：4つの項の足し算

-- (a + b) + (c + d) を ((a + b) + c) + d に変形します。

-- 全体を大きく見ると X + (c + d) という形です。

-- ヒント: Nat.add_assoc の逆 (←) を使います。

example : (a + b) + (c + d) = ((a + b) + c) + d := by

  rw[Nat.add_assoc]

  rw[Nat.add_assoc]

  rw[Nat.add_assoc]



-- 演習問題 68：ちょっと応用（因数分解と結合）

-- a * b * c + a * b を因数分解して a * b * (c + 1) にします。

-- ヒント: a * b をひとつのカタマリ「X」として見てください。

-- 今までの「X * c + X = X * (c + 1)」と同じパターンです。

-- 使うのは Nat.mul_assoc ではなく、分配法則 (Nat.left_distrib) です。

example : a * b * c + a * b = a * b * (c + 1) := by

  rw[Nat.left_distrib]

  rw[Nat.mul_one]



------------------------------------------------------------------------------------------------



-- 演習問題 69：掛け算の結合法則（逆）

-- a * (b * c) を (a * b) * c に戻します。

-- 左辺を変形するなら ← が必要ですが、右辺を変形するなら...？

-- いろいろ試してみてください。

example : a * (b * c) = (a * b) * c := by

  rw[Nat.mul_assoc]



-- 演習問題 70：奥の方の交換

-- a + (b + c) を a + (c + b) に変えます。

-- ヒント: カッコの中の b + c だけを入れ替えたいです。

-- 普通に rw [Nat.add_comm b c] と書けば、Leanが場所を見つけてやってくれます。

example : a + (b + c) = a + (c + b) := by

  rw[Nat.add_comm b c]



-- 演習問題 71：結合と交換のパズル

-- (a + b) + c を (a + c) + b に変形します。

-- ヒント:

-- 1. まず結合法則 (Nat.add_assoc) で a + (b + c) の形にします。

-- 2. カッコの中で bとcを入れ替えます (Nat.add_comm b c)。

-- 3. 最後に結合法則を逆向き (← Nat.add_assoc) にして戻します。

-- ※右辺を変形するアプローチでも解けます！

example : (a + b) + c = (a + c) + b := by

  rw [Nat.add_assoc]

  rw [Nat.add_comm b c]

  rw [Nat.add_assoc]



-- 演習問題 72：左側の結合（応用）

-- a * (b * c) を b * (a * c) に変形します。

-- ヒント:

-- 1. まず結合法則の逆 (← Nat.mul_assoc) で (a * b) * c にします。

-- 2. カッコの中で aとbを入れ替えます (Nat.mul_comm a b)。

-- 3. 再び結合法則 (Nat.mul_assoc) で整えます。

example : a * (b * c) = b * (a * c) := by

  rw [←Nat.mul_assoc]

  rw [Nat.mul_comm a b]

  rw [Nat.mul_assoc]



------------------------------------------------------------------------------------------------

-- 演習問題 73：掛け算のゼロ

-- シンプルな練習です。

-- 足し算のゼロ (add_zero) と掛け算のゼロ (mul_zero) を区別しましょう。

example : a * 0 + 0 * b = 0 := by

  rw [Nat.mul_zero]

  rw [Nat.zero_mul]



-- 演習問題 74：分配法則の２回掛け（準備運動）

-- (a + b) * c を展開します。

-- これは Nat.right_distrib 一発でいけますが、練習として

-- 「左から掛ける」Nat.left_distrib は使えないことに注意してください。

example : (a + b) * c = a * c + b * c := by

  rw [Nat.right_distrib]



-- 演習問題 75：【ボス問題】多項式の展開

-- (a + b) * (c + d) をバラバラにします。

-- 手順：

-- 1. まず右側の分配法則 (right_distrib) で (a + b) をそれぞれの項に配ります。

--    → a * (c + d) + b * (c + d) のような形になります。

-- 2. 次に左側の分配法則 (left_distrib) を２回使って、カッコを全部外します。

-- 3. 最後に結合法則 (add_assoc) でカッコの位置を整えれば完成です！

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by

  rw [Nat.right_distrib]

  rw [Nat.left_distrib]

  rw [Nat.left_distrib]

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]



-- 演習問題 76：２乗の展開（ボーナスステージ）

-- (a + 1) * (a + 1) を展開します。

-- a * a + a + a + 1 という形を目指します。

-- ヒント:

-- 1. まず right_distrib で分けます。

-- 2. mul_one, one_mul で 1 を消します。

-- 3. left_distrib でさらに分けます。

-- 4. 最後に add_assoc で形を整えます。

example : (a + 1) * (a + 1) = a * a + a + a + 1 := by

  rw [Nat.right_distrib]

  rw [Nat.one_mul]

  rw [Nat.left_distrib]

  rw [Nat.mul_one]

  rw [← Nat.add_assoc]



------------------------------------------------------------------------------------------------

-- 演習問題 77：足し算の奥での交換パズル

-- ヒント: add_assoc を何回か、add_comm b c を「奥」に当てる

variable (a b c d : Nat)

example : a + (b + (c + d)) = a + (c + (b + d)) := by

  rw [← Nat.add_assoc]

  rw [← Nat.add_assoc]

  rw [Nat.add_assoc a b c]

  rw [Nat.add_comm b c]

  rw [← Nat.add_assoc]

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]



-- 演習問題 78：分配法則 + 1 のお掃除

-- ヒント: right_distrib → left_distrib → mul_one

variable (a b c : Nat)

example : (a + b) * (c + 1) = a * c + a + (b * c + b) := by

  rw [Nat.right_distrib]

  rw [Nat.left_distrib]

  rw [Nat.left_distrib]

  rw [Nat.mul_one]

  rw [Nat.mul_one]



-- 演習問題 79：右因数のくくり出し

-- ヒント: ← Nat.right_distrib を使う（左因数じゃない！）

variable (a b c : Nat)

example : a * c + b * c = (a + b) * c := by

  rw [Nat.right_distrib]



-- 演習問題 80：∨ の場合分けで結論を作る

example (P Q R : Prop) : (P → R) → (Q → R) → (P ∨ Q) → R := by

  intro a

  intro b

  intro c

  cases c with

  | inl hp =>

    apply a

    exact hp

  | inr hq =>

    apply b

    exact hq



-- 演習問題 81：存在の写像（∃ の中身に関数を適用）

variable {α : Type}

example (P Q : α → Prop) : (∃ x, P x) → (∀ x, P x → Q x) → (∃ x, Q x) := by

  intro a

  intro b

  obtain ⟨c, d⟩ := a

  have e : P c → Q c := by

    intro f

    apply b

    exact d

  have g : Q c := by

    apply e

    exact d

  exists c



------------------------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- 次の5問（演習問題 82〜86）：少し難易度アップ版

--------------------------------------------------------------------------------

-- 演習問題 82：含意と「かつ」の行き来（↔）

-- 「PならQ」かつ「PならR」 ↔ 「Pなら(QかつR)」

-- ヒント:

--   - constructor で ↔ を割る

--   - → 方向は intro hp して constructor

--   - ← 方向は left/right を取り出して使う

example (P Q R : Prop) : (P → Q) ∧ (P → R) ↔ (P → Q ∧ R) := by

  constructor

  intro a

  intro b

  have c : P → Q := by

    exact a.left

  have d : P → R := by

    exact a.right

  have e : Q := by

    apply c

    exact b

  have f : R := by

    apply d

    exact b

  constructor

  exact e

  exact f

  intro g

  have h : P → Q := by

    intro i

    have j : Q ∧ R := by

      apply g

      exact i

    exact j.left

  have k : P → R := by

    intro l

    have m : Q ∧ R := by

      apply g

      exact l

    exact m.right

  constructor

  exact h

  exact k



-- 演習問題 83：対偶の逆（古典論理が必要）

-- (¬P → ¬Q) から (Q → P) を導く（直観主義では一般に無理）

-- ヒント:

--   - intro h; intro hq

--   - P を Classical.byContradiction で示す

--   - 「もし ¬P なら h から ¬Q、hq と矛盾」

example (P Q : Prop) : (¬ P → ¬ Q) → (Q → P) := by

  intro a

  intro b

  apply Classical.byContradiction

  intro c

  have d : ¬ Q := by

    apply a

    exact c

  apply d

  exact b

variable {α : Type}



-- 演習問題 84：全称量化子のド・モルガン（完全版・古典）☆☆☆☆☆☆☆☆

-- ¬(∀x, P x) ↔ ∃x, ¬P x

-- ヒント:

--   - → は古典（byContradiction が必要になりがち）

--   - ← は直観主義でOK（obtain ⟨x, hx⟩ := ... して hall x とぶつける）

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by

  constructor

  intro a                           -- (¬∀ (x : α), P x)を仮定に

  apply Classical.byContradiction   -- 背理法の導入

  intro b                           -- ∃ x, ¬P x が成り立たないを仮定に

  apply a

  intro c

  apply Classical.byContradiction

  intro d

  apply b

  exists c

  intro e

  obtain ⟨f, g⟩ := e

  intro h

  apply g

  apply h



variable (a b c d : Nat)



-- 演習問題 85：分配法則（奥が (c + d) になっている版）

-- a * (b + (c + d)) を「a*b + a*c + a*d」に展開

-- ヒント:

--   1. rw [Nat.left_distrib] で a*b + a*(c+d)

--   2. もう一回 rw [Nat.left_distrib] で a*b + (a*c + a*d)

--   3. 最後に add_assoc を ← 方向で整形

example : a * (b + (c + d)) = a * b + a * c + a * d := by

  rw [Nat.add_comm]

  rw [Nat.left_distrib]

  rw [Nat.left_distrib]

  rw [Nat.add_comm]

  rw [Nat.add_assoc]



-- 演習問題 86：4項の因数分解（結合→右分配の逆→左分配の逆）

-- a*c + b*c + a*d + b*d を (a+b)*(c+d) にまとめる

-- ヒント:

--   1. まず add_assoc で (a*c + b*c) + (a*d + b*d) の形を作る

--   2. それぞれ ← Nat.right_distrib で (a+b)*c, (a+b)*d にする

--   3. 最後に ← Nat.left_distrib でまとめる

example : a * c + b * c + a * d + b * d = (a + b) * (c + d) := by

  rw [Nat.left_distrib]

  rw [Nat.right_distrib]

  rw [Nat.right_distrib]

  rw [Nat.add_assoc]



------------------------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- 次の5問（演習問題 87〜91）：さらに難易度アップ

-- 方針：古典論理の扱い／量化子の“分配できない”部分の工夫／Natのrwパズルを強化

--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- 演習問題 87：含意の否定（古典）

-- ¬(P → Q) ↔ P ∧ ¬Q  を「なるべく tactic 少なめ」で

-- ヒント:

--   - →：P は背理法で作り、Q は「もしQなら(P→Q)が作れて矛盾」

--   - ←：⟨hp, hnq⟩ を使って (P→Q) を仮定すると矛盾

example (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q := by

  constructor

  intro a

  apply Classical.byContradiction

  intro b

  apply a

  intro c

  apply Classical.byContradiction

  intro d

  apply b

  constructor

  exact c

  exact d

  intro e

  intro f

  have g : ¬ Q := by

    exact e.right

  apply g

  have h : P := by

    exact e.left

  apply f

  exact h



--------------------------------------------------------------------------------

-- 演習問題 88：三段論法（∨ をはさむ版）

-- (P→Q) と (R→S) と (Q ∨ S → T) があり、

-- さらに (P ∨ R) が成り立つなら T が出る

-- ヒント: cases (P ∨ R) で分岐して、最後に Q ∨ S を作って当てる

example (P Q R S T : Prop) :

    (P → Q) → (R → S) → (Q ∨ S → T) → (P ∨ R) → T := by

  intro a

  intro b

  intro c

  intro d

  apply c

  cases d with

  | inl e =>

    have f : Q := by

      apply a

      exact e

    left

    exact f

  | inr g =>

    have h : S := by

      apply b

      exact g

    right

    exact h



--------------------------------------------------------------------------------

-- 演習問題 89：量化子と「または」（古典の匂い）

-- (∀x, P x) ∨ (∃x, Q x) → ∃x, (P x ∨ Q x)

-- ただし [Inhabited α] が必要（∀側のとき「誰をexistsするか」）

-- ヒント:

--   - cases h with

--     | inl hall => exists default; left; exact hall default

--     | inr hex  => obtain ⟨x,hq⟩ := hex; exists x; right; exact hq

variable {α : Type} [Inhabited α]

example (P Q : α → Prop) : (∀ x, P x) ∨ (∃ x, Q x) → ∃ x, (P x ∨ Q x) := by

  intro a

  cases a with

  | inl b =>

    exists default

    left

    apply b

  | inr c =>

    obtain ⟨d, e⟩ := c

    exists d

    right

    exact e



--------------------------------------------------------------------------------

-- 演習問題 90：量化子の“実用”版（∀ と ∧ の合わせ技）

-- (∀x, P x → Q x) と (∀x, Q x → R x) から (∀x, P x → R x)

-- ヒント: intro x; intro hp; apply ...; apply ...; exact hp

example {α : Type} (P Q R : α → Prop) :

    (∀ x, P x → Q x) → (∀ x, Q x → R x) → (∀ x, P x → R x) := by

  intro a

  intro b

  intro c

  intro d

  have e : P c → Q c := by

    apply a

  have f : Q c → R c := by

    apply b

  apply f

  apply e

  exact d



--------------------------------------------------------------------------------

-- 演習問題 91：Natの大パズル（展開→整理→因数分解）

-- (a+b)*(c+d) を展開して a*c + a*d + b*c + b*d にする、ただし

-- 右辺のカッコ位置が合うように add_assoc を何回か必要にする

-- ヒント:

--   - right_distrib で (a+b) を配る

--   - left_distrib を2回で各カッコを外す

--   - add_assoc を使って「a*c + a*d + b*c + b*d」の形に整形

variable (a b c d : Nat)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by

  rw [Nat.right_distrib]

  rw [Nat.left_distrib]

  rw [Nat.left_distrib]

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]

  rw [Nat.add_assoc]



------------------------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- 演習問題 92〜96：量化子 × 否定（18・84 強化トレーニング）

--------------------------------------------------------------------------------



variable {α : Type}



--------------------------------------------------------------------------------

-- 演習問題 92：存在否定の「使い道」（直観主義）

-- ¬(∃x, P x) を「実際にどう使うか」に焦点を当てた問題

-- ヒント:

--   intro x; intro hp; apply h; exists x

example (P : α → Prop) :

    ¬ (∃ x, P x) → (∀ x, P x → False) := by

  intro a

  intro b

  intro c

  apply a

  exists b



--------------------------------------------------------------------------------

-- 演習問題 93：∀ と ¬ の位置がズレた版（直観主義）

-- (∀x, ¬P x) → ¬(∃x, P x)

-- ※ 18の「逆向き」だが、こちらは背理法なしでいける

-- ヒント:

--   intro hex; obtain ⟨x,hp⟩ := hex; apply h x hp

example (P : α → Prop) :

    (∀ x, ¬ P x) → ¬ (∃ x, P x) := by

  intro a

  intro b

  obtain ⟨c, d⟩ := b

  have e : ¬ P c := by

    apply a

  apply e

  exact d



--------------------------------------------------------------------------------

-- 演習問題 94〜96（改）：量化子 × 否定（18・84の類似だが新パターン）

--------------------------------------------------------------------------------



variable {α : Type}



--------------------------------------------------------------------------------

-- 演習問題 94：存在否定の応用（直観主義でOK）

-- 「PかつQ を満たす人が存在しない」↔「任意のxについて、PならQではない」

-- 18（¬∃ ↔ ∀¬）を “P x ∧ Q x” に適用し、さらに ¬(P∧Q) ↔ (P→¬Q) に落とすイメージ

--

-- ヒント（→）:

--   intro h x hp hq

--   apply h; exists x; exact And.intro hp hq

-- ヒント（←）:

--   intro h; intro hex

--   obtain ⟨x, hx⟩ := hex

--   exact (h x hx.left) hx.right

example (P Q : α → Prop) : ¬ (∃ x, P x ∧ Q x) ↔ ∀ x, P x → ¬ Q x := by

  constructor

  intro a

  intro b

  intro c

  intro d

  apply a

  exists b

  intro e

  intro f

  obtain ⟨g, h⟩ := f

  have i : P g → ¬Q g := by

    apply e

  have j : Q g := by

    exact h.right

  have k : ¬ Q g := by

    apply i

    exact h.left

  apply k

  exact j



--------------------------------------------------------------------------------

-- 演習問題 95：∀ の否定（古典）＋「ならばの否定」

-- ¬(∀x, P x → Q x) ↔ ∃x, P x ∧ ¬Q x

-- 84（¬∀ ↔ ∃¬）と、12（¬(P→Q) ↔ P∧¬Q）を “xごと” に合体させる問題

--

-- ヒント（→）:

--   classical

--   1) 84 を (fun x => P x → Q x) に適用して ∃x, ¬(P x → Q x) を作る

--   2) その x に演習12を使って P x ∧ ¬Q x を得る

-- ヒント（←）:

--   obtain ⟨x, hp, hnq⟩ := ...

--   intro hall; have := hall x hp; exact hnq this

example (P Q : α → Prop) : ¬ (∀ x, P x → Q x) ↔ ∃ x, P x ∧ ¬ Q x := by

  constructor

  intro a

  apply Classical.byContradiction

  intro b

  apply a

  intro c

  intro d

  have e :∀ (x : α), ¬P x ∨ Q x := by

    intro f

    apply Classical.byContradiction

    intro g

    have h: P f ∧ ¬Q f := by

      constructor

      apply Classical.byContradiction

      intro i

      apply g

      left

      exact i

      intro j

      apply g

      right

      exact j

    apply b

    exists f

  have k : ¬P c ∨ Q c := by

    apply e

  cases k with

  | inl l =>

    apply Classical.byContradiction

    intro m

    apply l

    exact d

  | inr n =>

    exact n

  intro o

  intro p

  obtain ⟨q, r, s⟩ := o

  have t : P q → Q q := by

    apply p

  apply s

  apply t

  exact r



--------------------------------------------------------------------------------

-- 演習問題 96：84 を「結果を取り出す」ために使う（古典）

-- ¬(∀x, P x) かつ (∀x, P x ∨ A) なら A

-- 直観的には「Pが成り立たない人 x を一人見つけて、その人の (P x ∨ A) から A を確定」

--

-- ヒント:

--   classical

--   have hex : ∃ x, ¬ P x := by

--     -- 84 を使う（P をそのまま）

--   obtain ⟨x, hnp⟩ := hex

--   have hx : P x ∨ A := hall_or x

--   cases hx with

--   | inl hp => exfalso; exact hnp hp

--   | inr ha => exact ha

example (P : α → Prop) (A : Prop) : ¬ (∀ x, P x) → (∀ x, P x ∨ A) → A := by

  intro a

  intro b

  apply Classical.byContradiction

  intro c

  apply a

  intro d

  have e : P d ∨ A := by

    apply b

  cases e with

  | inl f =>

    apply f

  | inr g =>

    apply Classical.byContradiction

    intro h

    apply c

    exact g



------------------------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- 演習問題 97〜106：量化子 × 否定（18・84 系の強化・新パターン）

-- ※ import Mathlib なし（Lean4標準）でも解ける命題だけ出しています。

--------------------------------------------------------------------------------



variable {α β : Type}



--------------------------------------------------------------------------------

-- 演習問題 97：存在否定 + ド・モルガン（直観主義でOK）

-- 「PまたはQな人がいない」↔「全員、PでもQでもない」

-- ヒント:

--   (→) xを固定して、もし (P x ∨ Q x) なら ∃ を作って矛盾

--   (←) obtain ⟨x, hx⟩ := ...; cases hx with ...; で矛盾

example (P Q : α → Prop) :

    ¬ (∃ x, P x ∨ Q x) ↔ ∀ x, ¬ P x ∧ ¬ Q x := by

  constructor

  intro a

  intro b

  constructor

  intro c

  apply a

  exists b

  left

  exact c

  intro d

  apply a

  exists b

  right

  exact d

  intro e

  intro f

  obtain ⟨g, h⟩ := f

  have i : ¬P g ∧ ¬Q g := by

    apply e

  have j : ¬P g := by

    exact i.left

  have k : ¬Q g := by

    exact i.right

  cases h with

  | inl l =>

    apply j

    exact l

  | inr m =>

    apply k

    exact m



--------------------------------------------------------------------------------

-- 演習問題 98：∀ から ∃¬ を否定（直観主義でOK）

-- 「全員P」なら「¬Pな人がいる」はありえない

-- ヒント: obtain ⟨x,hnp⟩ := ...; apply hnp; apply hall

example (P : α → Prop) :

    (∀ x, P x) → ¬ (∃ x, ¬ P x) := by

  intro a

  intro b

  obtain ⟨c, d⟩ := b

  apply d

  have e : P c := by

    apply a

  exact e



--------------------------------------------------------------------------------

-- 演習問題 99：全称の含意 + 反証で全称の否定（直観主義でOK）

-- (∀x, P x → Q) と ¬Q から ∀x, ¬P x

-- ヒント: intro x hp; apply hnotQ; exact (h x hp)

example (P : α → Prop) (Q : Prop) :

    (∀ x, P x → Q) → ¬ Q → ∀ x, ¬ P x := by

  intro a

  intro b

  intro c

  intro d

  apply b

  have e : P c → Q := by

    apply a

  apply e

  exact d



--------------------------------------------------------------------------------

-- 演習問題 100：¬∀(P ∨ A) から ¬A と ∃¬P（古典が必要）

-- 「全員が (PかA) ではない」なら、Aは偽で、かつ「Pでない人」がいる

-- ヒント:

--   1) ¬A は直観主義で出せる：A を仮定すると ∀x, P x ∨ A が作れて矛盾

--   2) ¬(∀x, P x) も直観主義で出せる：∀x,Px なら ∀x, P x ∨ A が作れて矛盾

--   3) 最後に 84（¬∀→∃¬）で ∃x, ¬P x

example (P : α → Prop) (A : Prop) :

    ¬ (∀ x, P x ∨ A) → (∃ x, ¬ P x) ∧ ¬ A := by

  intro a

  constructor

  apply Classical.byContradiction

  intro b

  apply a

  intro c

  left

  apply Classical.byContradiction

  intro d

  apply b

  exists c

  intro e

  apply a

  intro f

  right

  exact e



--------------------------------------------------------------------------------

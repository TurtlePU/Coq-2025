(** * тактики: Больше тактик богу тактик! *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Lectures Require Export Lecture2.

(* ################################################################# *)
(** * Тактика [apply] *)

(** Тактика [apply] полезна, когда какая-то из гипотез либо ранее
    объявленная лемма в точности совпадает с целью: *)

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.

(** Здесь можно завершить с "[rewrite -> eq.  reflexivity.]", как мы делали
    раньше. Либо можно завершить в один шаг с помощью [apply]: *)

  apply eq.  Qed.

(** [apply] также работает с _обусловленными_ гипотезами: *)

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Обратите внимание, как Coq выбирает подходящие значения для
    переменных, захваченных в гипотезе квантором [forall]: *)

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Чтобы [apply] сработала, цель и гипотеза должны _полностью_
    совпадать: *)

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.

  (** Здесь нельзя использовать [apply] напрямую... *)

  Fail apply H.

  (** но можно сначала применить тактику [symmetry], которая обменяет левую и
      правую части равенства в цели. *)

  symmetry. apply H.  Qed.

(* ################################################################# *)
(** * Тактика [apply with] *)

(** Следующий простенький привер использует два переписывания подряд, чтобы
    перейти от [[a;b]] к [[e;f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2. Qed.

(** Так как это частый паттерн, давайте его вынесем в качестве леммы, которая
    раз и навсегда устанавливает, что равенство транзитивно. *)

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** Применение этой леммы к примеру выше требует небольшого уточнения
    при применении [apply]: *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  Check trans_eq.
  Fail apply trans_eq.

  (** Просто [apply trans_eq] не сработает!  А вот... *)
  apply trans_eq with (y:=[c;d]).
  (** поможет. *)

  apply eq1. apply eq2.   Qed.

(** [транзитивность] также доступна в качестве тактики. *)

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.   Qed.

(* ################################################################# *)
(** * Тактики [injection] и [discriminate] *)

(** Конструкторы индуктивных типов _инъективны_ и _не пересекаются_.

    Например, для [nat]...

       - Если [S n = S m], то обязательно верно, что [n = m]

       - [O] не равно [S n] ни для какого [n]
 *)

(** Мы можем _доказать_ инъективность [S] с помощью функции [pred], определённой
    в [Lecture1.v]. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  Print pred.
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

(** Для удобства, тактика [injection] позволяет нам пользоваться
    инъективностью любого конструктора (не только [S]). *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

(** А вот более интересный пример, который показывает, как [injection] можно
    использовать, чтобы получить сразу несколько новых равенств. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as Hno Hmo.
  transitivity o.
  - apply Hno.
  - symmetry. apply Hmo.
Qed.

(** Про инъективность понятно.  Что насчёт отсутствия пересечений? *)

(** Два терма, начинающиеся с применения различных конструкторов (как то
    [O] и [S] либо [true] и [false]) никогда не равны друг другу! *)

(** Тактика [discriminate] воплощает этот принцип: она применяется к гипотезе,
    содержащей равенство между различными конструкторами (например,
    [false = true]), и немедленно выполняет текущую цель.  Парочка примеров: *)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

(** Эти примеры -- конкретные проявления логического принципа, известного как
    _принцип взрыва_, который утверждает, что из противоречивого утверждения
    следует что угодно (даже очевидно ложные вещи!). *)

(** В качестве более полезного примера, рассмотрим применение [discriminate] для
    установления связи между двумя различными видами равенства ([=] и [=?]),
    которые мы определяли для натуральных чисел. *)
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.

  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.

  - (* n = S n' *)
    simpl.

    intros H. discriminate H.
Qed.

Compute (fun x => 1 + x).

(* QUIZ

    Вспомним типы [rgb] и [color]:

Inductive rgb : Type :=  red | green | blue.
Inductive color : Type :=  black | white | primary (p: rgb).

Предположим, состояние доказательства на Coq выглядит как

         x : rgb
         y : rgb
         H : primary x = primary y
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (1) "No more subgoals."

    (2) Тактика выбросит ошибку.

    (3) Гипотеза [H] произведёт [Hxy : x = y].

    (4) Ничего из вышеперечисленного.
*)
(* QUIZ

    Положим, состояние доказательства на Coq выглядит как

         x : bool
         y : bool
         H : negb x = negb y
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (1) "No more subgoals."

    (2) Тактика выбросит ошибку.

    (3) Гипотеза [H] произведёт [Hxy : x = y].

    (4) Ничего из вышеперечисленного.
*)
(* QUIZ

    Теперь положим, что состояние доказательства на Coq выглядит как

         x : nat
         y : nat
         H : x + 1 = y + 1
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (1) "No more subgoals."

    (2) Тактика выбросит ошибку.

    (3) Гипотеза [H] произведёт [Hxy : x = y].

    (4) Ничего из вышеперечисленного.
*)
(* QUIZ

    Наконец, положим, что состояние доказательства на Coq выглядит как

         x : nat
         y : nat
         H : 1 + x = 1 + y
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (1) "No more subgoals."

    (2) Тактика выбросит ошибку.

    (3) Гипотеза [H] произведёт [Hxy : x = y].

    (4) Ничего из вышеперечисленного.
*)

(** Инъективность конструкторов позволяет нам установить, что
    [forall (n m : nat), S n = S m -> n = m].  Утверждение, обратное этой
    импликации -- один из случаев более общего факта, верного как для
    конструкторов, так и для функций. Он нам очень пригодится дальше: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

(** Coq также предоставляет [f_equal] в виде тактики. *)

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

(* ################################################################# *)
(** * Применение тактик к гипотезам *)

(** У многих тактик доступна вариация вида "[... in ...]", которая
    вместо цели применяется к гипотезе. *)

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Обычный способ применения тактики [apply] -- это так называемый
    "обратный ход рассуждений."  По сути, пользуясь им, мы говорим "Мы пытаемся
    доказать [X] и мы знаем [Y -> X], так что нам достаточно доказать [Y]."

    А вот вариация [apply... in...] -- это, наоборот, "прямой ход рассуждений":
    он говорит "Мы знаем, что [Y] и что [Y -> X], так что мы знаем [X]." *)

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.  Qed.

(* ################################################################# *)
(** * Уточнение гипотезы *)

(** Другая полезная для работы с гипотезами тактика называется [specialize].
    По сути, это комбинация [assert] и [apply], но она достаточно часто
    предоставляет до приятного аккуратный способ уточнить слишком общие
    предположения.  Она работает следующим образом:

    Если [H] в текущем контексте это гипотеза с квантором, т.е. имеющая вид
    [H : forall (x:T), P], тогда [specialize H with (x := e)] изменит [H] так,
    что она теперь будет иметь тип [[x:=e]P], т.е., [P], где [x] заменили на
    [e].

    Например: *)

Theorem specialize_example: forall n,
     (forall m, m*n = 0)
  -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. Qed.

(** Используя [specialize] до [apply] даёт нам ещё один способ
    проконтролировать, где и какую работу выполняет тактика [apply]. *)
Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed.
(** Заметим:
    - Мы можем [уточнять] факты и из глобального контекста, не только локальные
      предположения.
    - Клоза [as...] в конце сообщает [specialize], как в таком случае называть
      новую гипотезу. *)

(* ################################################################# *)
(** * Варьирование предположения индукции *)

(** Вспомним функцию для удвоения натурального числа из главы
    [Lecture1]: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Пусть мы хотим показать, что [double] инъективна (т.е.,
    разные аргументы отображаются в разные значения).  _Начинаем_ это
    доказательство мы очень осторожно: *)

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.

(** В этой точке предположение индукции ([IHn']) _не_ утверждает [n' = m'] --
    мешается лишняя [S] -- так что цель нам, увы, не доказать. *)

Abort.
(** Что пошло не так? *)

(** Попытка доказать утверждение индукцией по [n], когда [m] уже в контексте,
    не работает, потому что так мы пытаемся доказать утверждение для
    _произвольного_ [n], но лишь для некоторого _конкретного_ [m]. *)

(** Успешное доказательство [double_injective] оставляет [m] под квантором
    вплоть до того момента, когда мы вызываем [индукцию] по [n]: *)

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *)
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *)
    discriminate eq.
    + (* m = S m' *)
      f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.

(** Урок, который нужно из этого вывести, следующий: при использовании индукции
    нужно аккуратно следить за тем, чтобы не доказывать излишне конкретное
    утверждение. Так, когда вы доказываете утверждение про переменные [n] и [m]
    индукцией по [n], иногда принципиально важно, чтобы [m] оставалась под
    квантором. *)

(** Следующая теорема, усиливающая связь между [=?] и [=], следует этому
    же принципу. *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  induction n.
  - destruct m.
    + reflexivity.
    + intros. discriminate H.
  - destruct m.
    + intros. discriminate H.
    + simpl. intros. f_equal. apply IHn, H.
Qed.

(** Стратегия делать меньше [intros] перед [induction] для получения более
    сильного предположения индукции работает не всегда; иногда переменные под
    кванторами нужно _поменять местами_.  Предположим, например, что мы хотим
    доказать [double_injective] индукцией не по [n], а по [m]. *)

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
        (* Здесь мы застрянем точно так же, как раньше. *)
Abort.

(** Проблема в том, что, для использования [m], мы должны сначала ввести [n].
    (А если мы скажем [induction m], ничего не вводя, Coq автоматически введёт
    [n] за нас!)  *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. *)

(** Вместо этого мы можем сначала ввести все подкванторные переменные, а
    затем _заново обобщить_ по некоторым из них.  Тактика [generalize dependent]
    делает именно это. *)

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* И [n], и [m] уже в контексте. *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(* ################################################################# *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a name that
    has been introduced by a [Definition] so that we can manipulate
    the expression it stands for.

    For example, if we define... *)

Definition square n := n * n.

(** ...and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ...we appear to be stuck: [simpl] doesn't simplify anything, and
    since we haven't proved any other facts about [square], there is
    nothing we can [apply] or [rewrite] with. *)

(** To make progress, we can manually [unfold] the definition of
    [square]: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these it is not hard
    to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** At this point, a bit deeper discussion of unfolding and
    simplification is in order.

    We already have observed that tactics like [simpl], [reflexivity],
    and [apply] will often unfold the definitions of functions
    automatically when this allows them to make progress.  For
    example, if we define [foo m] to be the constant [5]... *)

Definition foo (x: nat) := 5.

(** .... then the [simpl] in the following proof (or the
    [reflexivity], if we omit the [simpl]) will unfold [foo m] to
    [(fun x => 5) m] and further simplify this expression to just
    [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** But this automatic unfolding is somewhat conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the [match] are identical, so it gives up on
    unfolding [bar m] and leaves it alone.

    Similarly, tentatively unfolding [bar (m+1)] leaves a [match]
    whose scrutinee is a function application (that cannot itself be
    simplified, even after unfolding the definition of [+]), so
    [simpl] leaves it alone. *)

(** There are now two ways make progress.

    (1) Use [destruct m] to break the proof into two cases: *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress. *)

(** (2) Explicitly tell Coq to unfold [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [destruct] to finish the
    proof without thinking so hard. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** The [destruct] tactic can be used on expressions as well as
    variables: *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.

(** The [eqn:] part of the [destruct] tactic is optional; although
    we've chosen to include it most of the time, for the sake of
    documentation, it can often be omitted without harm.

    However, when [destruct]ing compound expressions, the information
    recorded by the [eqn:] can actually be critical: if we leave it
    out, then [destruct] can erase information we need to complete a
    proof. *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

(** Adding the [eqn:] qualifier saves this information so we
    can use it. *)

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.  Qed.

(* ################################################################# *)
(** * Micro Sermon *)

(** Mindless proof-hacking is a terrible temptation...

    Try to resist!
*)



(* ################################################################# *)
(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Require Nat.

(** So far, we have seen...

       - _propositions_: mathematical statements, so far only of 3 kinds:
             - equality propositions ([e1 = e2])
             - implications ([P -> Q])
             - quantified propositions ([forall x, P])

       - _proofs_: ways of presenting evidence for the truth of a
          proposition

    In this chapter we will introduce several more flavors of both
    propositions and proofs. *)

(** Like everything in Coq, well-formed propositions have a _type_: *)

Check (forall n m : nat, n + m = m + n) : Prop.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** So far, we've seen one primary place where propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** Propositions are first-class entities in Coq, though. For
    example, we can name them: *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(** The familiar equality operator [=] is a (binary) function that returns
    a [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Coq's standard library using the [Notation] mechanism).

    Because [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(* QUIZ

    What is the type of the following expression?

       pred (S O) = O

   (1) [Prop]

   (2) [nat->Prop]

   (3) [forall n:nat, Prop]

   (4) [nat->nat]

   (5) Not typeable

*)
Check (pred (S O) = O) : Prop.

(* QUIZ

    What is the type of the following expression?

      forall n:nat, pred (S n) = n

   (1) [Prop]

   (2) [nat->Prop]

   (3) [forall n:nat, Prop]

   (4) [nat->nat]

   (5) Not typeable

*)
Check (forall n:nat, pred (S n) = n) : Prop.

(* QUIZ

    What is the type of the following expression?

      forall n:nat, S (pred n) = n

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable

*)
Check (forall n:nat, S (pred n) = n) : Prop.

(* QUIZ

    What is the type of the following expression?

      forall n:nat, S (pred n)

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable
*)
Fail Check (forall n:nat, S (pred n)).
(* The command has indeed failed with message:
   In environment
   n : nat
   The term "(S (pred n))" has type "nat" which should be Set, Prop or Type. *)

(* QUIZ

    What is the type of the following expression?

      fun n:nat => S (pred n)

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable
*)
Check (fun n:nat => pred (S n)) : nat -> nat.

(* QUIZ

    What is the type of the following expression?

      fun n:nat => S (pred n) = n

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable

*)
Check (fun n:nat => pred (S n) = n) : nat -> Prop.

(* QUIZ

    Which of the following is _not_ a proposition?

    (1) [3 + 2 = 4]

    (2) [3 + 2 = 5]

    (3) [3 + 2 =? 5]

    (4) [((3+2) =? 4) = false]

    (5) [forall n, (((3+2) =? n) = true) -> n = 5]

    (6) All of these are propositions
*)
Check 3 + 2 =? 5 : bool.
Fail Definition bad : Prop := 3 + 2 =? 5.
(* The command has indeed failed with message: *)
(* The term "3 + 2 =? 5" has type "bool" while it is expected to have
   type "Prop". *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B] is
    written [A /\ B]; it represents the claim that both [A] and [B] are
    true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  This will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true and
    that [B] is true, we can conclude that [A /\ B] is also true.  The Coq
    library provides a function [conj] that does this. *)

Check @conj : forall A B : Prop, A -> B -> A /\ B.

(** we can [apply conj] to achieve the same effect as [split]. *)

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros * H.
  assert (HL : forall x y, x + y = 0 -> x = 0).
  { intros. destruct x. reflexivity. discriminate H0. }
  split.
  - apply HL with (y := m), H.
  - rewrite add_comm in H.
    apply HL with (y := n), H.
Qed.

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic. *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros * [Hn Hm]. rewrite Hn, Hm. reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0] and
    [m = 0] into a single conjunction, since we could also have stated the
    theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For the present example, both ways work.  But ...

    But in other situations we may wind up with a
    conjunctive hypothesis in the middle of a proof... *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros * H.
  destruct (plus_is_O _ _ H) as [Hn _].
  rewrite Hn. reflexivity.
Qed.

(** Finally, the infix notation [/\] is actually just syntactic sugar for
    [and A B].  That is, [and] is a Coq operator that takes two
    propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B] is.
    (This infix notation stands for [or A B], where
    [or : Prop -> Prop -> Prop].) *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern: *)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** Conversely, to show that a disjunction holds, it suffices to show that
    one of its sides holds. This can be done via the tactics [left] and
    [right].  As their names imply, the first one requires proving the left
    side of the disjunction, while the second requires proving the right
    side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|].
  - (* n = 0 *) left. reflexivity.
  - (* n = S n' *) right. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation

    Up to this point, we have mostly been concerned with proving "positive"
    statements -- addition is commutative, appending lists is associative,
    etc.  Of course, we are sometimes also interested in negative results,
    demonstrating that some given proposition is _not_ true. Such
    statements are expressed with the logical negation operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q]. *)

(** Coq actually makes a slightly different (but equivalent) choice,
    defining [~ P] as [P -> False], where [False] is a specific
    un-provable proposition defined in the standard library. *)

Module NotPlayground.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

End NotPlayground.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we can get [False] into the context,
    we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof. intros. destruct H. Qed.

(** Inequality is a very common form of negated statement, so there is a
    special notation for it:
*)
Notation "x <> y" := (~(x = y)) : type_scope.

(** For example: *)

Theorem zero_not_one : 0 <> 1.
Proof.
    unfold not.
    intros contra.
    discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in Coq.
    Even though _you_ can see perfectly well why a statement involving
    negation is true, it can be a little tricky at first to see how to make
    Coq understand it!

    Here are proofs of a few familiar facts to help get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros * [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof. unfold not. intros. apply H0, H. Qed.

(** Since inequality involves a negation, it also requires a
    little practice. Here is a useful trick: if you are trying to
    prove a nonsensical goal, apply [ex_falso_quodlibet] to change the
    goal to [False]. This makes it easier to use assumptions of the
    form [~P], and in particular of the form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

        forall X, forall a b : X, (a=b) /\ (a<>b) -> False.

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz1: forall X, forall a b : X, (a=b) /\ (a<>b) -> False.
Proof.
  intros X a b [Hab Hnab]. apply Hnab. apply Hab.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?

        forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz2 : forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).
Proof.
  intros P Q HPQ HnPQ. apply HnPQ in HPQ. apply HPQ.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?

         forall P Q: Prop, P -> (P \/ ~~Q).

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz3' : forall P Q: Prop, P -> (P \/ ~~Q).
Proof.
intros P Q HP. left. apply HP.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

         forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz4 : forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.
Proof.
  intros P Q [HP | HQ].
  - (* left *)
    left. intros HnP. apply HnP in HP. apply HP.
  - (* right *)
    right. intros HnQ. apply HnQ in HQ. apply HQ.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

         forall A : Prop, 1=0 -> (A \/ ~A).

    (1) [discriminate], [unfold], [left] and [right]

    (2) [discriminate] and [unfold]

    (3) only [discriminate]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz5 : forall A : Prop, 1=0 -> (A \/ ~A).
Proof.
  intros P H. discriminate H.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    constant [I : True], which is also defined in the standard
    library: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used
    relatively rarely, since it is trivial (and therefore
    uninteresting) to prove as a goal, and conversely it provides no
    interesting information when used as a hypothesis. *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications. *)

Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORK IN CLASS *) Admitted.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORK IN CLASS *) Admitted.

(** The [apply] tactic can also be used with [<->]. *)

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Setoids and Logical Equivalence *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding some
    low-level proof-state manipulation.  In particular, [rewrite] and
    [reflexivity] can be used with [iff] statements, not just equalities.
    To enable this behavior, we have to import the Coq library that
    supports it: *)

From Coq Require Import Setoids.Setoid.

(** A "setoid" is a set equipped with an equivalence relation,
    such as [=] or [<->]. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].

    First, let's prove a couple of basic iff equivalences. *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    prove a ternary version of the [mult_eq_0] fact above: *)

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** To prove a statement of the form [exists x, P], we must show that [P]
    holds for some specific choice for [x], known as the _witness_ of the
    existential.  This is done in two steps: First, we explicitly tell Coq
    which witness [t] we have in mind by invoking the tactic [exists t].
    Then we prove that [P] holds after all occurrences of [x] are replaced
    by [t]. *)

Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros * [m Hm]. exists (2 + m). apply Hm.
Qed.

(** ** Recap -- Logical connectives of Coq:

       - [and : Prop -> Prop -> Prop] (conjunction):
         - introduced with the [split] tactic
         - eliminated with [destruct H as [H1 H2]]
       - [or : Prop -> Prop -> Prop] (disjunction):
         - introduced with [left] and [right] tactics
         - eliminated with [destruct H as [H1 | H2]]
       - [False : Prop]
         - eliminated with [destruct H as []]
       - [True : Prop]
         - introduced with [apply I], but not as useful
       - [ex : forall A:Type, (A -> Prop) -> Prop] (existential)
         - introduced with [exists w]
         - eliminated with [destruct H as [x H]]
*)

(** ** More logical connectives in Coq:

    Derived connectives:
       - [not : Prop -> Prop] (negation):
         - [not P] defined as [P -> False]
       - [iff : Prop -> Prop -> Prop] (logical equivalence):
         - [iff P Q] defined as [(P -> Q) /\ (Q -> P)]

    Connectives we've been using since the beginning:
       - equality ([e1 = e2])
       - implication ([P -> Q])
       - universal quantification ([forall x, P]) *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** What does it mean to say that "an element [x] occurs in a
    list [l]"?

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or if it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORK IN CLASS *) Admitted.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORK IN CLASS *) Admitted.

(** We can also reason about more generic statements involving [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** Coq also treats _proofs_ as first-class objects! *)

(** We have seen that we can use [Check] to ask Coq to check whether
    an expression has a given type: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(** We can also use it to check the theorem a particular identifier
    refers to: *)

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

(** Coq checks the _statements_ of the [add_comm] and
    [plus_id_example] theorems in the same way that it checks the
    _type_ of any term (e.g., plus). If we leave off the colon and
    type, Coq will print these types for us.

    Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement [forall n m : nat, n + m = m + n].  The type of this object
    is the proposition that it is a proof of.

    The type of an ordinary function tells us what we can do with it.
       - If we have a term of type [nat -> nat -> nat], we can give it two
         [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use that
    theorem for.
       - If we have a term of type [forall n m, n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] and a third "argument" of type
         [n = m], we can derive [n + n = m + m]. *)

(** Coq actually allows us to _apply_ a theorem as if it were a
    function.

    This is often handy in proof scripts -- e.g., suppose we want too
    prove the following: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this by
    rewriting with [add_comm] twice to make the two sides match.  The
    problem is that the second [rewrite] will undo the effect of the
    first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We can fix this by applying [add_comm] to the arguments we want
    it be to instantiated with.  Then the [rewrite] is forced to happen
    where we want it. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** If we really wanted, we could in fact do it for both rewrites. *)

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Here's another example of using a trivial theorem about lists like
    a function. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis (causing the values of the
    other parameters to be inferred). *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Lemma quiz : forall a b : nat,
  a = b -> b = 42 ->
  (forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o) ->
  True.
Proof.
  intros a b H1 H2 trans_eq.

(* QUIZ

    Suppose we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat a b 42 H1 H2

    (1) [a = b]

    (2) [42 = a]

    (3) [a = 42]

    (4) Does not typecheck

 *)
Check trans_eq nat a b 42 H1 H2
  : a = 42.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat _ _ _ H1 H2

    (1) [a = b]

    (2) [42 = a]

    (3) [a = 42]

    (4) Does not typecheck

 *)
Check trans_eq nat _ _ _ H1 H2
  : a = 42.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat b 42 a H2

    (1) [b = a]

    (2) [b = a -> 42 = a]

    (3) [42 = a -> b = a]

    (4) Does not typecheck

 *)
Check trans_eq nat b 42 a H2
    : 42 = a -> b = a.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq _ 42 a b

    (1) [a = b -> b = 42 -> a = 42]

    (2) [42 = a -> a = b -> 42 = b]

    (3) [a = 42 -> 42 = b -> a = b]

    (4) Does not typecheck

 *)
Check trans_eq _ 42 a b
    : 42 = a -> a = b -> 42 = b.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq _ _ _ _ H2 H1

    (1) [b = a]

    (2) [42 = a]

    (3) [a = 42]

    (4) Does not typecheck

 *)
Fail Check trans_eq _ _ _ _ H2 H1.

Abort.

(* ################################################################# *)
(** * Working with Decidable Properties *)

(** We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes
*)

(** Since every function terminates on all inputs in Coq, a function
    of type [nat -> bool] is a _decision procedure_ -- i.e., it yields
    [true] or [false] on all inputs.

      - For example, [even : nat -> bool] is a decision procedure for the
        property "is even". *)

(** It follows that there are some properties of numbers that we _cannot_
    express as functions of type [nat -> bool].

      - For example, the property "is the code of a halting Turing machine"
        is undecidable, so there is no way to write it as a function of
        type [nat -> bool].

    On the other hand, [nat->Prop] is the type of _all_ properties of
    numbers that can be expressed in Coq's logic, including both decidable
    and undecidable ones.

      - For example, "is the code of a halting Turing machine" is a
        perfectly legitimate mathematical property, and we can absolutely
        represent it as a Coq expression of type [nat -> Prop].
*)

(** Since [Prop] includes _both_ decidable and undecidable properties, we
    have two options when we want to formalize a property that happens to
    be decidable: we can express it either as a boolean computation or as a
    function into [Prop]. *)

(** For instance, to claim that a number [n] is even, we can say
    either that [even n] evaluates to [true]... *)
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we can say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent: *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** Even when the boolean and propositional formulations of a claim are
    interchangeable from a purely logical perspective, it can be more
    convenient to use one over the other. *)

(** For example, there is no effective way to _test_ whether or not a
    [Prop] is true in a function definition; thus the
    following definition is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Rather, we have to state this definition using a boolean equality
    test. *)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** More generally, stating facts using booleans can often enable
    effective proof automation through computation with Coq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is simpler, because we
    don't have to invent the witness [500]: Coq's computation mechanism
    does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** Now, the useful observation is that, since the two notions are
    equivalent, we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    line count in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Coq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another advantage of booleans is that the negation of a "boolean fact"
    is straightforward to state and prove: simply flip the expected boolean
    result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** In contrast, propositional negation can be difficult to work with
    directly.

    For example, suppose we state the non-evenness of [1001]
    propositionally: *)

Example not_even_1001' : ~(Even 1001).

(** Proving this directly -- by assuming that there is some [n] such that
    [1001 = double n] and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean [even] function, we
    can let Coq do the work for us. *)

Proof.
  (* WORK IN CLASS *) Admitted.

(** Conversely, there are complementary situations where it can be easier
    to work with propositions rather than booleans.

    In particular, knowing that [(n =? m) = true] is generally of little
    direct help in the middle of a proof involving [n] and [m], but if we
    convert the statement to the equivalent form [n = m], we can rewrite
    with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Being able to cross back and forth between the boolean and
    propositional worlds will often be convenient in later chapters. *)

(* ################################################################# *)
(** * The Logic of Coq *)

(** Coq's logical core, the _Calculus of Inductive Constructions_,
    is a "metalanguage for mathematics" in the same sense as familiar
    foundations for paper-and-pencil math, like Zermelo-Fraenkel Set
    Theory (ZFC).

    Mostly, the differences are not too important, but a few points are
    useful to understand. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Coq's logic is quite minimalistic.  This means that one occasionally
    encounters cases where translating standard mathematical reasoning into
    Coq is cumbersome -- or even impossible -- unless we enrich its core
    logic with additional axioms. *)

(** A first instance has to do with equality of functions.

    In certain cases Coq can successfully prove equality propositions stating
    that two _functions_ are equal to each other: **)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** This works when Coq can simplify the functions to the same expression,
    but this doesn't always happen. **)

(** These two functions are equal just by simplification, but in general
    functions can be equal for more interesting reasons.

    In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** However, functional extensionality is not part of Coq's built-in logic.
    This means that some intuitively obvious propositions are not
    provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(** However, if we like, we can add functional extensionality to Coq
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we need to be quite careful when adding new axioms into
    Coq's logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False], [2+2=5],
    etc.!

    In general, there is no simple way of telling whether an axiom is safe
    to add: hard work by highly trained mathematicians is often required to
    establish the consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:

      Print Assumptions function_equality_ex2
*)
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(* QUIZ

    Is the following statement provable by just [reflexivity], without
    [functional_extensionality]?

      [(fun xs => 1 :: xs) = (fun xs => [1] ++ xs)]

    (1) Yes

    (2) No

 *)
Example cons_1_eq_ex : (fun xs => 1 :: xs) = (fun xs => [1] ++ xs).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** The following reasoning principle is _not_ derivable in
    Coq (though, again, it can consistently be added as an axiom): *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)


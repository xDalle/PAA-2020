From Coq Require Import List Arith.
Open Scope nat_scope.

(* Universidade de Bras�lia
    Instituto de Ci�ncias Exatas 
    Departamento de Ci�ncia da Computa��o
    Projeto e An�lise de Algoritmos - turma B - 2020/2 
    Professor: Fl�vio L. C. de Moura *)

(*
  Nome: Lucas Dalle Rocha
  Matr�cula: 17/0016641
  Nome: Matheus Breder Branquinho
  Matr�cula: 17/0018997
*)

(** * A corre��o do algoritmo mergesort *)

(** O algoritmo mergesort � um algoritmo de ordena��o que utiliza a t�cnica de divis�o e conquista, que consiste das seguintes etapas:
%\begin{enumerate}
   \item {\bf Divis�o}: O algoritmo divide a lista $l$ recebida como argumento ao meio, obtendo as listas $l_1$ e $l_2$. 
   \item {\bf Conquista}: O algoritmo � aplicado recursivamente �s listas $l_1$ e $l_2$ gerando, respectivamente, as listas ordenadas $l_1'$ e $l_2'$.
   \item {\bf Combina��o}: O algoritmo combina as listas $l_1'$ e $l_2'$ atrav�s da fun��o merge que ent�o gera a sa�da do algoritmo.
 \end{enumerate}%
Por exemplo, ao receber a lista (4 :: 2 :: 1 :: 3 :: nil), este algoritmo inicialmente divide esta lista em duas sublistas, a saber (4 :: 2 :: nil) e (1 :: 3 :: nil). O algoritmo � aplicado recursivamente �s duas sublistas para orden�-las, e ao final deste processo, teremos duas listas ordenadas (2 :: 4 :: nil) e (1 :: 3 :: nil). Estas listas s�o, ent�o, combinadas para gerar a lista de sa�da (1 :: 2 :: 3 :: 4 :: nil). *)

(** * Descri��o do projeto *)

(** A prova da corre��o de um algoritmo de ordena��o consiste de duas etapas. Inicialmente, provaremos que o algoritmo efetivamente ordena os elementos da lista dada como argumento, e em seguida mostraremos que a lista de sa�da � uma permuta��o da lista de entrada. Neste projeto trabalharemos com listas de n�meros naturais. *)

(* begin hide *)
Require Import Arith List Recdef.
Require Import Coq.Program.Wf.
Require Import Permutation.
(* end hide *)


(** ** Primeira parte: *)

(** Nesta primeira etapa do projeto, apresentaremos as defini��es e lemas relacionados � no��o de ordena��o de listas de n�meros naturais. Para isto, precisamos inicialmente definir formalmente o que entendemos por "lista ordenada". O predicado [sorted] a seguir consiste na defini��o formal de ordena��o que utilizaremos neste projeto. Note que este predicado � definido indutivamente e que possui tr�s construtores, ou tr�s regras como veremos a seguir: *)

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

(** O predicado [sorted] possui tr�s construtores, a saber [nil_sorted], [one_sorted] and [all_sorted]. Os dois primeiros construtores s�o axiomas que afirmam que a lista vazia e que listas unit�rias est�o ordenadas: 
 %\begin{mathpar} \inferrule*[Right={$(nil\_sorted)$}]{~}{sorted\ nil} \and
  \inferrule*[Right={$(one\_sorted)$}]{~}{\forall n, sorted (n :: nil)} \end{mathpar}%
O terceiro construtor, i.e. [all_sorted] estabelece as condi��es para que uma lista com pelo menos dois elementos esteja ordenada. Assim, quaisquer que sejam os elementos $x$ e $y$, e a lista $l$, temos:
%\begin{mathpar} \inferrule*[Right={$(all\_sorted)$}]{sorted (y :: l) \and x \leq y}{sorted (x :: y :: l)}\end{mathpar}%
Ou seja, para provarmos que a lista $x :: y :: l$ est� ordenada, precisamos provar que $x \leq y$ e que a lista $y :: l$ tamb�m est� ordenada.
 *)

(** Agora que temos um defini��o formal da no��o de ordena��o, vamos explorar algumas no��es auxiliares que ser�o utilizadas na formaliza��o. A primeira delas � o predicado [le_all] que recebe um natural [x] e uma lista [l] como argumentos, e a f�rmula [le_all x l] possui uma prova quando [x] � menor ou igual a todos os elementos de [l]. *)

Definition le_all x l := forall y, In y l -> x <= y.

(** printing <=* $\leq *$ *)
(** Escreveremos  [x <=* l] ao inv�s de [le_all x l]. *)
(* begin hide *)
Infix "<=*" := le_all (at level 70, no associativity).
(* end hide *)

(** Lemas s�o resultados auxiliares que podem ser usados em outras provas. � importante se lembrar dos lemas que ficaram para tr�s porque eles podem ser �teis em diversas provas. O primeiro lema auxiliar que veremos afirma que se a lista (a :: l) est� ordenada ent�o a sua cauda (tail) tamb�m est� ordenada. A prova � feita por an�lise de casos. *)

Lemma tail_sorted: forall l a, sorted (a :: l) -> sorted l.
(* begin hide *)
Proof.
  intro l.
  case l.
  - intros a H.  
    apply nil_sorted.  
  - intros n l' a H.  
    inversion H; subst.
    assumption.  
Qed.  

(** OBS: Seguem alguns exemplos de busca de teoremas com o comando [Search]: *)
(** Search (_ > _ -> _ <= _). *)
(** Search (~ _ <= _ -> _). *)
(** Search "lt_sub_lt_add". *)
(** Search ( ( _ / _) < _). *)
(** Search ( ( _ / _) <= _). *)
(** Search (0 < ( _ / _) ).*)
(** Search (1 < 2). *)
(** Search (0 < 2). *)
(** Search ( _ - _ < _). *)
(** Search (S _ + _ = S _).*)
(* end hide *)

(** *** Quest�o 1: *)
(** A primeira quest�o consiste em provar que se [a] � menor ou igual a todo elemento de [l], e [l] � uma lista ordenada ent�o a lista (a :: l) tamb�m est� ordenada: *)

Lemma le_all_sorted: forall l a, a <=* l -> sorted l -> sorted (a :: l).
Proof.
  intros l a H H0.
  induction l.
  - apply one_sorted.
  - apply all_sorted.
    + exact H0.
    + destruct H with (y := a0).
      * simpl.
        left.
        apply eq_refl.
      * apply Nat.le_refl.
      * apply le_S.
        exact l0.
Qed.
      
(** O lema a seguir � bem parecido com o lema [tail_sorted] visto anteriormente, mas ao inv�s de remover o primeiro elemento de uma lista ordenada, este lema remove o segundo elemento de uma lista ordenada (com pelo menos dois elementos), e ap�s esta remo��o a lista resultante ainda est� ordenada. Veja que a prova � por an�lise de casos. *)

Lemma remove_sorted: forall l a1 a2, sorted (a1 :: a2 :: l) -> sorted (a1 :: l).
(* begin hide *)
Proof.
  intro l; case l.
  - intros a1 a2 H.
    apply one_sorted.
  - intros n l' a1 a2 H.
    inversion H; subst.
    inversion H2; subst.
    apply all_sorted.
    + assumption.
    + apply Nat.le_trans with a2; assumption.
Qed.
(* end hide *)

(** *** Quest�o 2 *)
(** A segunda quest�o consiste em provar que, se a lista [(a :: l)] est� ordenada ent�o [a] � menor ou igual a todo elemento de [l]. A dica � fazer indu��o na estrutura da lista [l]. *)

Lemma sorted_le_all: forall l a, sorted(a :: l) -> a <=* l.
Proof.
  induction l.
  - intros a H y H0.
    destruct H0.
  - intros a0 H y H0.
    destruct H0.
    + inversion H; subst.
      exact H5.
    + apply remove_sorted in H.
      apply IHl in H.
      unfold "<=*" in H.
      apply H in H0.
      exact H0.
Qed.

(** ** Segunda parte: *)
(** Agora definiremos a no��o de permuta��o e apresentaremos alguns lemas relacionados. A no��o de permuta��o que ser� utilizada neste projeto � baseada no n�mero de ocorr�ncias de um elemento. A fun��o recursiva [num_oc n l] retorna o n�mero de ocorr�ncias do natural [n] na lista [l]. A palavra reservada [Fixpoint] � usada para definir fun��es recursivas, enquanto que [Definition] � usada para fun��es n�o-recursivas como foi o caso do predicado [le_all] visto anteriormente. *)

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

(** Dizemos ent�o que duas listas [l] e [l'] s�o permuta��es uma da outra se qualquer natural [n] possui o mesmo n�mero de ocorr�ncias em ambas as listas. *)

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

(** A reflexividade � uma propriedade que pode ser obtida a partir desta defini��o: uma lista � sempre permuta��o dela mesma. *)

Lemma perm_refl: forall l, perm l l.
(* begin hide *)
Proof.
intro l. unfold perm. intro. reflexivity.
Qed.
(* end hide *)

(** O lema a seguir � um resultado t�cnico, mas que pode ser utilizado em provas futuras. Ele diz que o n�mero de ocorr�ncias de um natural [n] no append das listas [l1] e [l2] (nota��o [l1 ++ l2]) � igual � soma das ocorr�ncias de [n] em [l1] com as ocorr�ncias de [n] em [l2]: *)

Lemma num_oc_append: forall n l1 l2, num_oc n l1 + num_oc n l2 = num_oc n (l1 ++ l2).
(* begin hide *)
Proof.
  intros. induction l1.
  - simpl num_oc. trivial.
  - simpl. destruct (n =? a).
    + rewrite <- IHl1. apply Peano.plus_Sn_m.
    + assumption.
Qed.
(* end hide *)

(** *** Terceira parte: *)
(** Nesta parte definiremos o algoritmo mergesort. Iniciaremos pela fun��o [merge] que faz a etapa de combina��o descrita anteriormente. A fun��o [merge] recebe como argumento um par de listas de naturais ordenadas e gera uma nova lista ordenada contendo exatamente os elementos das duas listas recebidas como argumento. Iniciamos ent�o com a defini��o do predicado [sorted_pair_lst] que recebe um par de listas e retorna a conjun��o expressando o fato de que cada lista que comp�e o par est� ordenada: *)

Definition sorted_pair_lst (p: list nat * list nat) :=
sorted (fst p) /\ sorted (snd p).

(** Agora necessitamos de uma m�trica para definirmos a fun��o [merge]. Esta m�trica consiste no tamanho do par que cont�m duas listas e � definido como sendo a soma do comprimento de cada uma das listas: *)

Definition len (p: list nat * list nat) :=
   length (fst p) + length (snd p).

(** Agora podemos definir a fun��o recursiva [merge]. Dado um par [p] de listas de naturais, se alguma das listas que comp�em este par � a lista vazia ent�o a fun��o simplesmente retorna o outro elemento do par. Quando ambas as listas que comp�em o par s�o n�o-vazias ent�o os primeiros elementos de cada lista s�o comparados e o menor deles ser� o colocado na lista final, e o processo se repete recursivamente para o par sem este menor elemento. Para garantirmos que esta fun��o est� bem definida, precisamos que as chamadas recursivas se aproximem do ponto de parada (chamadas sem recurs�o) que ocorre quando alguma das listas do par � a lista vazia. Esta garantia � dada pelo medida (ou m�trica) definida anteriormente: o comprimento do par que [merge] recebe como argumento: *)
(* printing *)
(** printing <=? $\leq ?$ *)

Function merge (p: list nat * list nat) {measure len p} :=
match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
      else hd2 :: merge (l1, tl2)
   end.

(** A palavra reservada [Function] � utilizada para definir fun��es recursivas mais sofisticadas, ou seja, para fun��es recursivas cuja boa defini��o n�o pode ser inferida automaticamente pelo Coq. Neste caso, precisamos provar que nossa medida realmente decresce nas chamadas recursivas. *)
(* begin hide *)
Proof.
  - intros. unfold len. unfold fst. unfold snd. simpl length.
    apply plus_lt_compat_r. auto.
  - intros. unfold len. unfold fst. unfold snd. simpl length.
    apply plus_lt_compat_l. auto.  
Qed.
(* end hide *)

(** O lema [merge_in] a seguir ser� bastante �til em provas futuras. Ele estabelece que se [y] � um elemento da lista [merge p] ent�o [y] est� em alguma das listas que comp�em o par [p]. *)

Lemma merge_in: forall y p, In y (merge p) -> In y (fst p) \/ In y (snd p).
(* begin hide *)
Proof.
intros. functional induction (merge p).
  - right. unfold snd. assumption.
    - left. unfold fst. assumption.
    - simpl in H. destruct H as [H1 | H2].
    + left. unfold fst. unfold In. left. assumption.
        + destruct IHl.
        * assumption.
          * left. unfold fst. unfold fst in H. simpl In. right. assumption.
          * right. simpl. simpl in H. assumption.
    - simpl in H. destruct H as [H1 | H2].
    + right. simpl snd. simpl In. left. assumption.
        + destruct IHl.
        * assumption.
          * left. unfold fst. unfold fst in H. assumption.
          * right. simpl. simpl in H. right. assumption.
Qed.
(* end hide *)

(** *** Quest�o 3 *)
(** Esta quest�o � a mais importante do projeto. Ela estabelece que se as listas que comp�em o par [p] est�o ordenadas ent�o [merge p] tamb�m est� ordenada. Como [merge] � uma fun��o recursiva mais sofisticada, as propriedades envolvendo esta fun��o tamb�m ter�o provas mais complexas. Como voc� pode ver, esta prova � composta de quatro casos, dos quais dois est�o provados, e dois fazem parte do exerc�cio. Cada caso deixado como exerc�cio � semelhante ao caso anterior, ent�o use estas subprovas que est�o feitas como ideias para completar a prova deste teorema. Os lemas anteriores tamb�m podem ser �teis! *)

Theorem merge_sorts: forall p, sorted_pair_lst p -> sorted (merge p).
(* begin hide *)
Proof.
  intro p. functional induction (merge p).
  - unfold sorted_pair_lst. intro. destruct H.
    unfold snd in H0. assumption.
  - unfold sorted_pair_lst. intro. destruct H.
    unfold fst in H. assumption.
  - intro. apply le_all_sorted.
    + unfold le_all. intro. intro. apply merge_in in H0.
      destruct H0 as [H1 | H2].
      * simpl fst in H1. unfold sorted_pair_lst in H. destruct H as [H2 H3].
        simpl fst in H2. apply sorted_le_all in H2. unfold le_all in H2.
        apply H2. assumption.    
      * simpl snd in H2. apply Nat.le_trans with hd2.
        -- apply Nat.leb_le. assumption.
        -- unfold sorted_pair_lst in H. destruct H as [H3 H4]. simpl snd in H4.
           apply sorted_le_all in H4. simpl In in H2. destruct H2 as [H5 | H6].
           ** rewrite H5. trivial.
           ** unfold le_all in H4. apply H4. assumption.
    + apply IHl. unfold sorted_pair_lst. split.
      * simpl fst. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl fst in H1. apply tail_sorted in H1. assumption.
      * simpl snd. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl snd in H2. assumption.  
  - intro. apply le_all_sorted.
    + unfold le_all. intro. intro. apply merge_in in H0.
      destruct H0 as [H1 | H2].
      * simpl fst in H1. unfold sorted_pair_lst in H. destruct H as [H2 H3].
        simpl fst in H2. apply sorted_le_all in H2. unfold le_all in H2.
        simpl in H1. destruct H1 as [H4 | H5].
        ** rewrite <- H4. apply leb_complete_conv in e0. apply Nat.lt_le_incl in e0. assumption.
        ** apply H2 in H5. apply leb_complete_conv in e0. apply Nat.lt_le_incl in e0. rewrite <- H5. assumption.
      * simpl snd in H2. apply Nat.le_trans with hd2.
        -- trivial.
        -- unfold sorted_pair_lst in H. destruct H as [H3 H4]. simpl snd in H4.
           apply sorted_le_all in H4. unfold le_all in H4. apply H4 in H2. assumption.
    + apply IHl. unfold sorted_pair_lst. split.
      * simpl fst. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl fst in H1. assumption.
      * simpl snd. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl snd in H2. apply tail_sorted in H2. assumption.  
Qed.

(* end hide *)

(** Agora vamos definir a fun��o [mergesort] que recebe uma lista [l] como argumento. Se esta lista for vazia ou unit�ria, o algoritmo n�o faz nada. Caso contr�rio, a lista � dividida ao meio, cada sublista � ordenada recursivamente, e no final as sublistas ordenadas s�o fundidas com a fun��o [merge]. *)

Function mergesort (l: list nat) {measure length l}:=
  match l with
  | nil => nil
  | hd :: nil => l
  | hd :: tail =>
     let n := length(l) / 2 in
     let l1 := firstn n l in
     let l2 := skipn n l in
     let sorted_l1 := mergesort(l1) in
     let sorted_l2 := mergesort(l2) in
     merge (sorted_l1, sorted_l2)
  end.

(** Analogamente � defini��o da fun��o [merge], precisamos provar que [mergesort] est� bem definida. *)
(* begin hide *)
Proof.
- intros. rewrite skipn_length. apply Nat.sub_lt.
  + apply Nat.lt_le_incl. apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
    + apply Nat.div_str_pos. simpl. split.
    * apply Nat.lt_0_2.
      * apply Peano.le_n_S. apply Peano.le_n_S. apply Peano.le_0_n.  
  - intros. rewrite firstn_length. rewrite min_l.
  + apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.  
Defined.
(* end hide *)

(** *** Quest�o 4 *)
(** Agora prove que a fun��o [mergesort] realmente ordena a lista recebida como argumento. *)

Theorem mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  induction l.
  - apply nil_sorted.
  - functional induction (mergesort (a :: l)).
    + apply nil_sorted.
    + apply one_sorted.
    + apply merge_sorts.
      unfold sorted_pair_lst.
      split.
      * unfold fst.
        assumption.
      * unfold snd.
        assumption.
Qed.

(** O lema a seguir � um lema t�cnico que pode ser usado nas quest�es seguintes. Este lema estabelece que o n�mero de ocorr�ncias de um elemento [n] no par de listas [p] � igual � soma das ocorr�ncias de [n] em cada lista do par. *)

Lemma merge_num_oc: forall n p, num_oc n (merge p) = num_oc n (fst p) + num_oc n (snd p).
(* begin hide *)
Proof.
intros. functional induction (merge p).
  - simpl fst. simpl snd. simpl num_oc. trivial.
  - simpl fst. simpl snd. simpl num_oc. trivial.
  - simpl fst. simpl snd. simpl num_oc at 1 2. destruct (n =? hd1).
    + rewrite IHl. apply Peano.plus_Sn_m.
    + rewrite IHl. simpl fst. simpl snd. trivial.
  - simpl fst. simpl snd. simpl num_oc at 1 3. (destruct (n =? hd2)).
      + rewrite IHl. simpl fst. simpl snd. apply Peano.plus_n_Sm.
      + rewrite IHl. simpl fst. simpl snd. trivial.
Qed.
(* end hide *)

(** *** Quest�o 5 *)
(** Prove que [mergesort] gera uma permuta��o da lista recebida como argumento. *)

Theorem mergesort_is_perm: forall l, perm l (mergesort l).
Proof.
  intros. functional induction (mergesort l).
  - apply perm_refl.
  - apply perm_refl.
  - unfold perm. intros. rewrite merge_num_oc.
    unfold fst, snd.
    replace (num_oc n (mergesort (firstn (length (hd :: tail) / 2) (hd :: tail)))) with (num_oc n (firstn (length (hd :: tail) / 2) (hd :: tail))) .
    replace (num_oc n (mergesort (skipn (length (hd :: tail) / 2) (hd :: tail)))) with (num_oc n (skipn (length (hd :: tail) / 2) (hd :: tail))) .
    + rewrite num_oc_append at 1. rewrite firstn_skipn. trivial.
    + destruct mergesort.
      * unfold perm in *. rewrite -> IHl1. trivial.
      * unfold perm in *. rewrite -> IHl1. trivial.
    + unfold perm in *. rewrite -> IHl0. trivial.
Qed.

(** *** Quest�o 6 *)
(** Por fim, prove que [mergesort] � correto. *)

Theorem mergesort_is_correct: forall l, perm l (mergesort l) /\ sorted (mergesort l).
Proof.
  split.
  - apply mergesort_is_perm.
  - apply mergesort_sorts.
Qed.

(** ** Extra��o de c�digo *)
(** Uma das vantagens de formalizar um algoritmo � que voc� pode extrair o c�digo certificado do algoritmo. O algoritmo de extra��o garante que o c�digo extra�do satisfaz todas as propriedades provadas. Vamos extrair automaticamente o c�digo do algoritmo mergesort? *)

Require Extraction.

(** As op��es de linguagens fornecidas pelo Coq s�o: OCaml, Haskell, Scheme e JSON. *)

Extraction Language OCaml.

(** Extra��o apenas da fun��o [mergesort]: *)

Extraction mergesort.

(** Extra��o do programa inteiro: *)

Recursive Extraction mergesort.

(** Extra��o para um arquivo: *)

Extraction "mergesort" mergesort.

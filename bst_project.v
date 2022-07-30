(** * Formaliza��o da estrutura de �rvores bin�rias de busca%\footnote{Este documento foi adaptado de \url{https://softwarefoundations.cis.upenn.edu/}}% *)
(** Estudaremos as �rvores bin�rias de busca em um contexto mais formal. Inicialmente revise o tema fazendo a leitura e os exerc�cios do cap�tulo 12 do livro _Introduction to Algorithms, 3rd Edition_, Cormen, Leiserson, and Rivest, MIT Press 2009. *)

(* begin hide *)
From Coq Require Import String.
From Coq Require Export Arith.
From Coq Require Export Lia.

Notation  "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70) : nat_scope.
(* end hide *)

(** Utilizaremos n�meros naturais para representar as chaves em cada n� de nossas �rvores bin�rias de busca porque os naturais possuem uma ordem total [<=?] com diversos teoremas j� provados. *)

Definition key := nat.

(** Adicionalmente, os n�s armazenar�o pares chave/valor, onde o valor associado a uma chave ter� um tipo [V] qualquer. Definiremos indutivamente a estrutura [tree] para representar �rvores bin�rias cujos n�s cont�m uma chave [k] e um valor [v]. As �rvores possuem dois construtores, [E] que representa a �rvore vazia, e [T] que recebe os seguintes argumentos: 
- [l]: a sub�rvore � esquerda do n� atual;
- [k]: a chave ligada ao n� atual;
- [v]: o valor associado � chave [k], e;
- [r]: a sub�rvore � direita do n� atual.
Nesta constru��o, cada chave se liga a apenas um valor. *)

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

(* begin hide *)
Arguments E {V}.
Arguments T {V}.
(* end hide *)

(** Exemplo: a �rvore bin�ria contendo valores do tipo [string]
<<
      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five"
>>
� representada a seguir: *)

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

(** A �rvore vazia [empty_tree] n�o cont�m chaves: *)

Definition empty_tree {V : Type} : tree V := E. 

(** Uma �rvore bin�ria de busca  � caracterizada pela seguinte invariante: dado qualquer n� n�o-vazio com chave [k], todas as chaves da sub�rvore � esquerda s�o menores do que [k], e todas as chaves da sub�rvore � direita s�o maiores do que [k]. *)

(** A primeira opera��o importante relacionada �s �rvores bin�rias de busca �  certamente a busca que pode ser implementada de forma muito eficiente. Por exemplo, a fun��o [bound k t] retorna [true] quando [k] � uma chave de [t], e [false] caso contr�rio. *)

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

(** Analogamente, a fun��o [lookup d k t] retorna o valor ligado � chave [k] em [t], ou retorna o valor _default_ [d] quando [k] n�o � uma chave de [t]. *)

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

(** Observe que se [t] n�o � uma �rvore bin�ria de busca ent�o as fun��es [bound] e [lookup] podem retornar respostas erradas: *)

Module NotBst.
  Open Scope string_scope.

  (** De fato, considere a seguinte �rvore que n�o � uma �rvore bin�ria de busca: *)
  
  Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).

  (** Ela possui uma ocorr�ncia da chave 2, mas em uma posi��o n�o esperada pelas fun��es [bound] e [lookup]: *)
  
  Example not_bst_bound_wrong :
    bound 2 t = false.
  Proof.
    reflexivity.
  Qed.

  Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
  Proof.
    simpl. unfold not. intros contra. discriminate.
  Qed.
End NotBst.

(** A segunda opera��o fundamental de �rvores bin�rias de busca que estudaremos neste trabalho � a inser��o. A fun��o [insert k v t] insere a chave [k] e o valor [v] na �rvore bin�ria de busca [t], de forma a preservar a invariante de uma �rvore bin�ria de busca. *)

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                 else if x >? y then T l y v' (insert x v r)
                      else T l x v r
  end.

(** Nossa primeira tarefa ser� mostrar que a fun��o [insert] de fato preserva esta invariante. Vamos ent�o formalizar a invariante de uma �rvore bin�ria de busca. Faremos isto com a ajuda da fun��o [ForallT]: *)

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(** Esta fun��o expressa as condi��es para que uma �rvore satisfa�a uma dada propriedade [P]: Se a �rvore for vazia ent�o a propriedade � satisfeita por vacuidade, e portanto retorna [True]. Quando a �rvore n�o � vazia, e portanto tem a forma [T l k v r], ent�o precisamos que o n� que tem chave [k] e valor [v] satisfa�a a propriedade [P], assim como as sub�rvores � esquerda e � direita.
Agora vamos definir a invariante [BST], que � composta de dois construtores:
    - O primeiro construtor, denotado por [BST_E], consiste em um axioma que estabelece que uma �rvore vazia � uma �rvore bin�ria de busca.
    - O segundo construtor, denotado por [BST_T], consiste na regra que diz que para que uma �rvore n�o vazia [T l x v r] seja uma �rvore bin�ria de busca � necess�rio que todas as chaves da sub�rvore � esquerda sejam menores do que [x], todas a chaves da sub�rvore � direita sejam maiores do que [x], e que as sub�rvores � esquerda e � direita sejam tamb�m �rvores bin�rias de busca: *)

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

(* begin hide *)
Hint Constructors BST.
Ltac inv H := inversion H; clear H; subst.

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H; split.
  - intro H'.
    inv H.
    + reflexivity.
    + contradiction.
  - intro H'; subst.
    inv H; assumption.
Qed.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].
(* end hide *)

(** Vejamos que o predicado [BST] classifica correta alguns exemplos: *)

Example is_BST_ex :
  BST ex_tree.
Proof.
  unfold ex_tree.
  repeat (constructor; try lia).
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  unfold NotBst.t. intros contra.
  inv contra. inv H3. lia.
Qed.

(** ** Quest�o 1: *)
(** A primeira quest�o consiste em provar que uma �rvore vazia (de qualquer tipo) � uma �rvore bin�ria de busca. *)

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
  intro V.
  unfold empty_tree.
  constructor.
Qed.
  
(** ** Quest�o 2:  *)
(** A seguir, provaremos que a fun��o [insert] produz uma �rvore bin�ria de busca, mas antes prove que a fun��o [insert] preserva qualquer propriedade dos n�s: *)

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert k v t).
Proof.
  induction t.
  - intros H1 k v H2.
    simpl.
    auto.
  - intros H1 k' v' H2.
    simpl in H1.
    destruct H1 as [H1 [Ht1 Ht2]].
    simpl.
    bdestruct (k >? k').
    + simpl.
      split.
      * assumption.
      * split.
        ** apply IHt1; assumption.
        ** assumption.
    + bdestruct (k' >? k).
      * simpl.
        split.
        ** assumption.
        ** split.
           *** assumption.
           *** apply IHt2; assumption.
      * simpl.
        auto.
Qed.

(** ** Quest�o 3:  *)
(** Prove que ao receber uma �rvore bin�ria de busca como argumento, a fun��o [insert] gera outra �rvore bin�ria de busca. *)

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
  induction t.
  - intro H.
    simpl.
    apply BST_T.
    + simpl; auto.
    + simpl; auto.
    + apply BST_E.
    + apply BST_E.
  - intro H.
    inv H.
    simpl.
    bdestruct (k0 >? k).
    + apply BST_T.
      * apply ForallT_insert; assumption.
      * assumption.
      * apply IHt1; assumption.
      * assumption.
    + bdestruct (k >? k0).
      * apply BST_T.
        ** assumption.
        ** apply ForallT_insert; assumption.
        ** assumption.
        ** apply IHt2; assumption.
      * unfold ge in H, H0.
        assert (Heq: k0 = k).
        {
          apply Nat.le_antisymm; assumption.
        }
        clear H H0.
        subst.
        apply BST_T; assumption.
Qed.
        
(** * A corre��o das fun��es de busca [lookup] e [bound] *)

(** Qual o comportamento esperado para as fun��es [lookup] e [bound]? Ao procurarmos uma chave na �rvore bin�ria de busca vazia com a fun��o [lookup], devemos obter o valor default [d]: *)

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

(** Se inserirmos a chave [k] e valor [v] na �rvore bin�ria de busca [t], ent�o a busca em [insert k v t] com a fun��o [lookup] retorna [v]: *)

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V), lookup d k (insert k v t) = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); try lia;auto.
  - bdestruct (k <? k0); bdestruct (k0 <? k); simpl; try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k0 <? k0); try lia; auto.
Qed.

(** A t�tica [bdall] a seguir, simplifica esta prova evitando os passos repetitivos *)
Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

(** ** Quest�o 4: *)
(** Prove que a busca de uma chave [k'], via a fun��o [lookup], na �rvore bin�ria de busca [insert k v t], com [k] e [k'] distintos, retorna o resultado de buscar [k'] em [t]:  *)

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
  induction t; intros; bdall.
Qed.

(** ** Quest�o 5:  *)
(** Enuncie e prove os tr�s teoremas an�logos para a fun��o [bound]. *)

Theorem bound_empty : forall (V: Type) (k : key),
    bound k (@empty_tree V) = false.
Proof.
  auto.
Qed.

Theorem bound_insert_eq :
  forall (V : Type) (t : tree V) (k : key) (v : V),
    bound k (insert k v t) = true.
Proof.
  induction t.
  - intros k v.
    simpl insert.
    simpl bound.
    bdall.
  - intros k' v'.
    simpl.
    bdall.
Qed.

Theorem bound_insert_neq :
  forall (V : Type) (t : tree V) (k k' : key) (v : V),
   k <> k' -> bound k' (insert k v t) = bound k' t.
Proof.
  induction t.
  - intros k k' v H.
    simpl.
    bdall.
  - intros k' k'' v' H.
    simpl.
    bdall.
Qed.
 
(** ** Quest�o 6:  *)
(** A rela��o esperada entre as fun��es [bound] e [lookup] � que, se [bound k t] retorna [false] ent�o [lookup d k t] retorna o valor default [d]. Prove este fato dado pelo seguinte teorema: *)

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
  induction t.
  - intro H.
    simpl.
    reflexivity.
  - intro H.
    inv H.
    bdall.
    inversion H1.
Qed.
    
(** * Convertendo �rvores bin�rias de busca em listas *)

(* begin hide *)
From Coq Require Export Lists.List.
Export ListNotations.
(* end hide *)

(** Uma representa��o alternativa para as �rvores bin�rias de busca � via listas ligadas. Neste caso, os elementos s�o pares [(k,v)] contendo a chave [k] e o valor [v]. Se a lista estiver ordenada pelas chaves, ent�o duas �rvores representando a mesma �rvore bin�ria de busca s�o convertidas na mesma lista pela fun��o [elements]: *)

Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

Example elements_ex :
    elements ex_tree = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

Definition ex_tree' : tree string :=
  (T E 2 "two" (T E 4 "four" (T E 5 "five" E)))%string.

Example elements_ex' :
    elements ex_tree' = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

(** Agora vamos provar que esta transforma��o possui algumas propriedades interessantes. Por exemplo, dada uma �rvore bin�ria de busca [t], uma chave [k] associada a um valor [v] ocorre em [t] se, e somente se o par [(k,v)] � um elemento de [elements t]. Dividiremos esta prova em duas partes: *)

(** ** Quest�o 7:  *)
(** Prove que a transforma��o via [elements] � completa, i.e. se uma chave [k] associada a um valor [v] ocorre em [t] ent�o o par [(k,v)] � um elemento de [elements t]: *)

Theorem elements_complete : forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    bound k t = true ->
    lookup d k t = v ->
    In (k, v) (elements t).
Proof.
  induction t.
  - intros H H0 H1.
    simpl.
    discriminate.
  - intros H H0 H1.
    simpl.
    apply in_app_iff.
    simpl in *.
    inv H0.   
    inv H.
    bdall.
    destruct H.
    + right.
      left.
      reflexivity.
    + (** k0 <= m e k0 >= S m *) 
      try lia.
Qed.

(** Agora vamos provar que a transforma��o via [elements] � correta, i.e. se o par [(k,v)] � um elemento de [elements t] ent�o a chave [k] ocorre associada ao valor [v] em [t]. 
A prova da corre��o exige um pouco mais de trabalho porque enquanto o predicado [BST] utiliza o predicado [ForallT] para garantir que todos os n�s da �rvore satisfazem uma determinada propriedade, listas utilizam o predicado [Forall] para isto. Assim, precisamos estabelecer uma rela��o entre estes predicados. *)

Lemma Forall_app : forall (A: Type) (P : A -> Prop) (l1 l2 : list A),
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros; simpl; auto; inv H; constructor; auto.
Qed.

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.

Hint Transparent uncurry.

(** ** Quest�o 8:  *)
Lemma elements_preserves_forall : forall (V : Type) (P : key -> V -> Prop) (t : tree V), ForallT P t -> Forall (uncurry P) (elements t).
Proof.
  induction t.
  - intro H.
    simpl.
    apply Forall_nil.
  - intro H.
    inversion H; subst.
    destruct H1 as [Ht1 Ht2].
    clear H.
    simpl.
    apply Forall_app.
    + apply IHt1; assumption.
    + apply Forall_cons.
      * unfold uncurry.
        assumption.
      * apply IHt2; assumption.
Qed.

(** ** Quest�o 9:  *)

(** Lema auxiliar, utilizei para provar elements_correct. *)
(** Recomendado pelo original: https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html *)

(** Prove that if all the keys in t are in a relation R with a distinguished key k',
then any key k in elements t is also related by R to k'. For example, R could be <, 
in which case the lemma says that if all the keys in t are less than k', 
then all the keys in elements t are also less than k'. *)

Lemma elements_preserves_relation :
  forall (V : Type) (k k' : key) (v : V) (t : tree V) (R : key -> key -> Prop),
    ForallT (fun y _ => R y k') t
    -> In (k, v) (elements t)
    -> R k k'.
Proof.
  intros.
  apply elements_preserves_forall in H.
  rewrite Forall_forall in H.
  apply H in H0.
  simpl in H0.
  assumption.
Qed.

Theorem elements_correct : forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
  intros.
  induction t.
  - simpl in *.
    contradiction.
  - simpl in *.
    apply in_app_iff in H0.
    simpl in H0.
    inv H.
    rename H5 into Ht1.
    rename H6 into Ht2.
    bdall.
    + destruct H0.
      * apply IHt1; assumption.
      * apply elements_preserves_relation with (k := k) (v := v) in Ht2.
        ** try lia.
        ** destruct H0.
           *** inversion H0.
               try lia.
           *** assumption. 
    + inv H0.
      * apply elements_preserves_relation with (k := k) (v := v) in Ht1.
        ** try lia.
        ** assumption.
      * apply IHt2.
        ** assumption.
        ** destruct H2.
           *** inv H0.
               try lia.
           *** assumption.
    + split. 
      * auto.
      * inv H0.
        ** apply elements_preserves_relation with (k := k) (v := v) in Ht1.
           *** try lia.
           *** assumption.
        ** inv H2.
           *** inv H0.
               reflexivity.
           *** apply elements_preserves_relation with (k := k) (v := v) in Ht2.
               **** try lia.
               **** assumption. 
Qed.

(** * Uma implementa��o mais eficiente de [elements] *)

(** ** Quest�o 10: *)
(** A implementa��o de [elements] � eficiente? Qual � a complexidade assint�tica [elements t] quando [t] � uma �rvore balanceada? E quando [t] � desbalanceada? Esta quest�o deve ser respondida textualmente em detalhes. *)

(** Uma outra forma de transformar uma �rvore bin�ria de busca em uma lista � dada pela fun��o [elements_tr]: *)

Fixpoint elements_aux {V : Type} (t : tree V)
         (acc : list (key * V)) : list (key * V) :=
  match t with
  | E => acc
  | T l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.

Definition elements_tr {V : Type} (t : tree V) : list (key * V) :=
  elements_aux t [].

(** ** Quest�o 11:  *)
(** Prove que [elements_tr] e [elements] fazem a mesma transforma��o. *)

(** Lema auxiliar para provar elements_correct *)
(** Recomendado pelo original: https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html *)
Lemma elements_tr_elements_aux : forall (V : Type) (t : tree V) (acc : list (key * V)),
    elements_aux t acc = elements t ++ acc.
Proof.
  induction t.
  - intro acc.
    simpl.
    reflexivity.
  - intro acc.
    simpl.
    rewrite <- app_assoc.
    rewrite IHt2.
    rewrite IHt1.
    simpl.
    reflexivity.
Qed.

Lemma elements_tr_elements : forall (V : Type) (t : tree V),
    elements_tr t = elements t.
Proof.
  intros V t.
  unfold elements_tr.
  rewrite elements_tr_elements_aux.
  rewrite <- app_nil_r.
  reflexivity.
Qed.

(** ** Quest�o 12:  *)
(** Prove que a transforma��o [elements_tr] � correta utilizando a corre��o de [elements]. *)

Corollary elements_tr_correct :
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements_tr t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
  induction t.
  - intros H H0.
    simpl.
    contradiction.
  - intros H H0.
    rewrite elements_tr_elements in H0.
    apply elements_correct; assumption.
Qed.

(** ** Quest�o 13:  *)
(** Qual a complexidade assint�tica de [elements_tr]? Esta quest�o deve ser respondida textualmente em detalhes. *)

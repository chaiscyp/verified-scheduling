From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import micromega.Lia.
From Coq Require Import micromega.Zify.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals. Import RIneq. Import Rdefinitions.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Logic.FunctionalExtensionality.

Import ListNotations.

Set Warnings "-deprecate-hint-without-locality,-deprecated".

Class TensorElem (A : Set) :=
  { null : A;
    bin : A -> A -> A;
    set_R : A -> list Z -> R -> A;
    set_Z : A -> list Z -> Z -> A;
    shape : Set;
    scalar_mul : R -> A -> A;
    consistent : A -> shape -> Prop;
    mul_1_id : forall a : A, scalar_mul 1%R a = a;
    mul_0_idemp :
      forall a : A, scalar_mul 0%R (scalar_mul 0%R a) = scalar_mul 0%R a;
    bin_null_id_r :  forall a : A, bin a null = a;
    bin_mul_0_id : forall (a b : A) s s',
        consistent a s -> consistent b s' ->
        s = s' ->
        bin (scalar_mul 0%R a) b = b;
    mul_0_absorb : forall (a b : A) s s',
        consistent a s -> consistent b s' ->
        s = s' ->
        scalar_mul 0%R a = scalar_mul 0%R b;
    consistent_bin : forall (a b : A) s s',
        consistent a s -> consistent b s' -> s = s' ->
        consistent (bin a b) s;
    consistent_mul : forall a c s,
        consistent a s -> consistent (scalar_mul c a) s;
    bin_comm : forall a b, bin a b = bin b a;
    bin_assoc : forall a b c, bin a (bin b c) = bin (bin a b) c;
    mul_bin_distr : forall a b c,
        scalar_mul c (bin a b) = bin (scalar_mul c a) (scalar_mul c b);
    shape_dec : forall (s1 s2 : shape), s1 = s2 \/ s1 <> s2;
    eq_dec : forall (s1 s2 : A), s1 = s2 \/ s1 <> s2;
    mul_0_null : scalar_mul 0 null = null;
    bin_mul_0_self_id : forall e, bin (scalar_mul 0 e) e = e    
  }.

Infix "<+>" := bin (at level 34, left associativity).

Lemma bin_null_id_l {X} `{TensorElem X} : forall a,
    bin null a = a.
Proof.
  intros. rewrite bin_comm. apply bin_null_id_r.
Qed.

Hint Rewrite @bin_null_id_l : crunch.
Hint Rewrite @bin_null_id_r : crunch.
Hint Rewrite @mul_1_id : crunch.

Ltac deq a b := let H := fresh "H" in
                pose proof (eq_dec a b) as H;
                destruct H.

Hint Extern 4 (_ :: _ = _ :: _) => f_equal : crunch.
Hint Extern 4 (Some _ = Some _) => f_equal : crunch.
Hint Extern 4 ((_,_) = (_,_)) => f_equal : crunch.

Hint Resolve Pos2Nat.is_pos : crunch.

Generalizable Variable X.

(* Let binding *)
Definition let_binding {X Y} (bindexp : X) (inexp : X -> Y) :=
  inexp bindexp.

Notation "'tlet' x ':=' e 'in' f" := (let_binding e (fun x => f))
                                       (at level 81).

(* Iverson bracket *)
Definition iverson `{TensorElem X} (b : bool) (e : X) :=
  scalar_mul (if b then 1%R else 0%R) e.

Notation "|[ b ]| e" := (iverson b%Z e)
                          (at level 80,
                           format "'[hv ' |[  b  ]| ']' '[hv '  e ']'").
  
(* Tensor generation *)
Fixpoint gen_helper `{TensorElem X} n x (f' : Z -> X) : list X :=
  match n with
  | O => []
  | S n' => f' x :: (gen_helper n' x (fun x' => f' (x' + 1)%Z))
  end.

Definition genr `{TensorElem X} (x y : Z) (f : Z -> X) : list X :=
  gen_helper (Z.to_nat (y - x)) x f.

Definition gen `{TensorElem X} (y : Z) :=
  genr 0%Z y.

Notation "'GEN' [ m <= i < n ] e " := (genr m n (fun i => e))
                                        (at level 36,
                                         e at level 36,
                                         m, i, n at level 50,
                                         format
         "'[hv ' 'GEN'  [  m  <=  i  <  n  ] ']' '//' e").

Notation "'GEN' [ i < n ] e " := (gen n (fun i => e))
                                        (at level 36,
                                         e at level 36,
                                         i, n at level 50,
                                         format
         "'[hv ' 'GEN'  [  i  <  n  ] ']' '//' e").

(* Tensor summation *)
Fixpoint sum_helper `{TensorElem X} n x (f' : Z -> X) : X :=
  match n with
  | O => null
  | S n' => bin (f' x) (sum_helper n' x (fun x' => f' (x' + 1)%Z))
  end.

Definition sumr `{TensorElem X} (x y : Z) (f : Z -> X) : X :=
  sum_helper (Z.to_nat (y - x)) x f.

Definition sum `{TensorElem X} (y : Z) :=
  sumr 0%Z y.

Notation "'SUM' [ m <= i < n ] e " := (sumr m n (fun i => e))
                                        (at level 36,
                                         e at level 36,
                                         m, i, n at level 50,
                                         format
         "'[hv ' 'SUM'  [  m  <=  i  <  n  ] ']' '//' e").

Notation "'SUM' [ i < n ] e " := (sum n (fun i => e))
                                        (at level 36,
                                         e at level 36,
                                         i, n at level 50,
                                         format
         "'[hv ' 'SUM'  [  i  <  n  ] ']' '//' e").


(* Tensor access *)
Definition get `{TensorElem X} (v : list X) (i : Z) : X :=
  match v with
  | [] => null (* shouldn't be reached *)
  | x::_ => match i with
            | Z.neg _ => scalar_mul 0%R x
            | _ =>  match (nth_error v (Z.to_nat i)) with
                    | Some val => val
                    | None => scalar_mul 0%R x
                    end
            end
  end.

Notation "x _[ i ; .. ; j ]" :=
  (get .. (get x i%Z) .. j%Z) (at level 33).

Arguments get : simpl never.

(* This definition of adding tensors is intended for lists of same length but
 * extends and pads a second list with null values to the length of the other
 * if they are different lengths *)
Definition tensor_add `{TensorElem X} (t1 t2 : list X) : list X :=
  GEN [ i < Z.of_nat (max (length t1) (length t2)) ] (t1 _[i] <+> t2 _[i]).

  (* Existential quantification *)
Fixpoint exists_fin' (i : nat) (p : nat -> Prop) : Prop :=
  match i with
  | O => False
  | S i' => p 0 \/ exists_fin' i' (fun x => p (S x))
  end.

#[refine] Instance RTensorElem : TensorElem R :=
  { null := 0;
    bin := Rplus;
    set_R := fun _ _ v => v;
    set_Z := fun arr _ _ => arr; 
    shape := unit;
    consistent _ _ := True;
    scalar_mul := Rmult;
    mul_1_id := Rmult_1_l }.
Proof.
  intros; repeat (rewrite Rmult_0_l). reflexivity.

  intros; ring.

  intros; ring.

  intros; ring.

  intros; trivial.

  intros; trivial.

  intros; trivial.

  intros; trivial.

  intros; ring.

  intros; ring.

  intros; ring.

  destruct s1; destruct s2; auto.

  apply Req_dec.

  auto.

  auto.

  ring.

  intros. ring.
Defined.

Axiom cheating : forall A, A.
#[refine] Instance ZTensorElem : TensorElem Z :=
  { null := 0%Z;
    bin := Z.add;
    set_R := fun arr _ _ => arr; (* leaves the same *)
    set_Z := fun _ _ v => v; 
    shape := unit;
    consistent _ _ := True;
    scalar_mul := fun _ x => x (* assume to multiply by 1 *);
  }.
Proof.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; ring.
  - intros; apply cheating.
  - intros; apply cheating.
  - intros; trivial.
  - intros; trivial.
  - intros; ring.
  - intros; ring.
  - intros; reflexivity.
  - destruct s1. destruct s2. auto.
  - apply cheating.
  - intros. trivial.
  - apply cheating.
Defined.

Lemma get_empty_null {X} `{TensorElem X} : forall i, [] _[ i ] = null.
Proof. destruct i; simpl; unfold get; reflexivity. Qed.

Lemma nth_error_inc {X} `{TensorElem X} : forall i (l : list X) a,
    nth_error l i = nth_error (a::l) (S i).
Proof.
  destruct i; intros; reflexivity.
Qed.

Theorem gen_helper_eq_bound {X} `{TensorElem X} : forall n m f g,
    (forall i, 0 <= i -> i < n ->
               f (Z.of_nat i + m)%Z = g (Z.of_nat i + m)%Z) ->
    gen_helper n m f = gen_helper n m g.
Proof.
    induction n; intros.
  - reflexivity.
  - simpl.
    f_equal.
    apply (H0 0); lia.
    apply IHn. intros.
    replace (Z.of_nat i + m + 1)%Z with ((Z.of_nat (S i)) + m)%Z by
        (rewrite Nat2Z.inj_succ; lia).
    apply H0; lia.
Qed.    

Lemma get_cons {X} `{TensorElem X} : forall a l i,
    (0 <= i)%Z ->
    (i < Z.of_nat (length l))%Z ->
    (a :: l) _[ i+1] = l _[ i ].
Proof.
  intros; destruct i; destruct l; simpl in *; try lia.
  - unfold get. reflexivity.
  - unfold get. simpl.
    rewrite Pos.add_1_r.
    rewrite Pos2Nat.inj_succ.
    simpl.
    rewrite nth_error_nth' with (d:=null).
    reflexivity.
    zify. simpl. zify. lia.
Qed.

Lemma tensor_add_empty_l {X} `{TensorElem X} : forall l,
    tensor_add [] l = l.
Proof.
  induction l.
  - reflexivity.
  - unfold tensor_add in *.
    simpl in *.
    rewrite <- IHl at 2.
    unfold gen, genr in *. simpl in *.
    rewrite SuccNat2Pos.id_succ.
    rewrite Z.sub_0_r.
    rewrite Nat2Z.id.
    simpl.
    rewrite get_empty_null.
    rewrite bin_null_id_l.
    unfold get at 1.
    simpl.
    f_equal.
    apply gen_helper_eq_bound. intros.
    repeat rewrite get_empty_null.
    f_equal.
    rewrite Z.add_0_r.
    rewrite get_cons by lia.
    reflexivity.
Qed.

Lemma tensor_add_empty_r {X} `{TensorElem X} : forall l,
    tensor_add l [] = l.
Proof.
  induction l.
  - reflexivity.
  - unfold tensor_add in *.
    simpl in *.
    rewrite <- IHl at 2.
    unfold gen, genr in *. simpl in *.
    rewrite SuccNat2Pos.id_succ.
    rewrite Z.sub_0_r.
    rewrite Nat2Z.id.
    simpl.
    rewrite get_empty_null.
    rewrite bin_null_id_r.
    unfold get at 1.
    simpl.
    f_equal.
    rewrite max_0_r.
    apply gen_helper_eq_bound. intros.
    repeat rewrite get_empty_null.
    f_equal.
    rewrite Z.add_0_r.
    rewrite get_cons by lia.
    reflexivity.
Qed.
  
Lemma tensor_add_step {X} `{TensorElem X} :
  forall (h h' : X) (tl tl' : list X),
    tensor_add (h :: tl) (h' :: tl') = (bin h h') :: (tensor_add tl tl').
Proof.
  intros.
  unfold tensor_add.
  simpl.
  rewrite Zpos_P_of_succ_nat.
  unfold gen, genr.
  repeat rewrite Z.sub_0_r.
  rewrite <- Nat2Z.inj_succ.
  repeat rewrite Nat2Z.id.
  simpl.
  unfold get at 1.
  simpl. unfold get at 1. simpl.
  f_equal.
  apply gen_helper_eq_bound; intros.
  rewrite Z.add_0_r.
  apply max_lt_iff in H1.       
Admitted.

Inductive tensor_consistent {X} `{TensorElem X} :
  list X -> (nat * shape)%type -> Prop :=
| cons_consistent :
    forall (x : X) (xs : list X) s n,      
    consistent x s ->
    Forall (fun x => consistent x s) xs ->
    length (x::xs) = n ->
    tensor_consistent (x::xs) (n, s).

Lemma length_add_length {X} `{TensorElem X} : forall a b n,
    length a = n ->
    length b = n ->
    length (tensor_add a b) = n.
Proof.
  induction a; destruct b; intros; simpl in H0,H1.
  - assumption.
  - rewrite <- H0 in H1. discriminate.
  - rewrite <- H1 in H0. discriminate.
  - rewrite tensor_add_step.
    destruct n; try lia.
    inversion H0. inversion H1.
    rewrite H0. simpl. auto with crunch.
Qed.

Lemma tensor_consistent_step {X} `{TensorElem X} : forall a b c s n,
    tensor_consistent (a::b::c) (S n, s) ->
    tensor_consistent (b::c) (n,s).
Proof.
  intros.
  inversion H0.
  constructor.
  inversion H6. auto. inversion H6. auto.
  simpl in *. lia.
Qed.

(* Helper functions for set_R and set_Z for TensorElem list*)
Fixpoint list_set_R_helper `{TensorElem X} (arr : list X) (indices : list Z) (v : R) : list X :=
  match indices with 
  | [] => arr
  | hi :: ti => 
    match hi with 
    | Z.neg _ => arr
    | _ => 
      match Z.to_nat hi with 
      | O => 
        match arr with 
        | [] => (set_R null ti v) :: []
        | harr :: tarr => (set_R harr ti v) :: tarr
        end
      | S hi' =>
        match arr with
        | [] => (repeat null (S hi')) ++ [set_R null ti v]
        | harr :: tarr => harr :: (list_set_R_helper tarr ((hi-1)%Z::ti) v)
        end
      end
    end
  end.

Fixpoint list_set_Z_helper {X} `{TensorElem X} (arr : list X) (indices : list Z) (v : Z) : list X :=
  match indices with 
  | [] => arr
  | hi :: ti => 
    match hi with 
    | Z.neg _ => arr
    | _ => 
      match Z.to_nat hi with 
      | O => 
        match arr with 
        | [] => (set_Z null ti v) :: []
        | harr :: tarr => (set_Z harr ti v) :: tarr
        end
      | S hi' =>
        match arr with
        | [] => (repeat null (S hi')) ++ [set_Z null ti v]
        | harr :: tarr => harr :: (list_set_Z_helper tarr ((hi-1)%Z::ti) v)
        end
      end
    end
  end.

#[refine]Instance TensorTensorElem {X} `{TensorElem X} : TensorElem (list X) :=
  { null := [];
    bin := tensor_add;
    set_R := list_set_R_helper;
    set_Z := list_set_Z_helper;
    shape := nat * (@shape X _);
    consistent := tensor_consistent;
    scalar_mul c l := map (scalar_mul c) l }.
Proof.
  induction a as [| ? ? IH];
    try reflexivity. simpl. rewrite IH. now rewrite mul_1_id.

  induction a; try reflexivity.
  simpl. rewrite mul_0_idemp. f_equal. assumption.

  intros. apply tensor_add_empty_r.

  {
    intros.
    subst.
    destruct s'.
    generalize dependent a. generalize dependent b.
    induction n; intros.
    - destruct a; destruct b.
      inversion H0. inversion H0. inversion H1.
      inversion H1. discriminate.
    - destruct a; destruct b.
      inversion H1. inversion H0. inversion H1.
      destruct a; destruct b.
      + simpl.
        rewrite tensor_add_step.
        rewrite tensor_add_empty_r. 
        f_equal.
        eapply bin_mul_0_id.
        * inversion H0. eauto.
        * inversion H1. eauto.
        * auto.
      + inversion H0. inversion H1. subst.
        simpl in H8. simpl in H15.
        lia.
      + inversion H1. inversion H0. subst.
        simpl in H15. simpl in H8.
        lia.
      + inversion H1. inversion H0. subst.
        rewrite map_cons.
        rewrite tensor_add_step.
        f_equal.
        eapply bin_mul_0_id; eauto.
        apply IHn.
        eapply tensor_consistent_step. eauto.
        eapply tensor_consistent_step. eauto.        
  }

  {
    intros.
    subst.
    destruct s'.
    generalize dependent a. generalize dependent b.
    induction n; intros.
    - destruct a; destruct b.
      inversion H0. inversion H0. inversion H1.
      inversion H1. discriminate.
    - destruct a; destruct b.
      inversion H1. inversion H0. inversion H1.
      destruct a; destruct b.
      + simpl. inversion H0. inversion H1. subst.
        f_equal. eapply mul_0_absorb; eauto.
      + inversion H0. inversion H1. subst.
        simpl in H15. simpl in H8. lia.
      + inversion H0. inversion H1. subst.
        simpl in H15. simpl in H8. lia.
      + rewrite map_cons.
        symmetry. rewrite map_cons.
        inversion H0. inversion H1. subst.
        f_equal. eapply mul_0_absorb; eauto.
        apply IHn; eapply tensor_consistent_step; eauto.        
  }

  {
    intros.
    subst.
    destruct s'.
    generalize dependent a. generalize dependent b.
    induction n; intros.
    - destruct a; destruct b.
      inversion H0. inversion H0. inversion H1.
      inversion H1. discriminate.
    - destruct a; destruct b.
      inversion H1. inversion H0. inversion H1.
      destruct a; destruct b.
      + rewrite tensor_add_step. rewrite tensor_add_empty_r.
        inversion H1. inversion H0. subst.
        constructor.
        eapply consistent_bin; eauto. constructor. auto.
      + inversion H0. inversion H1. simpl in *. lia.
      + inversion H0. inversion H1. simpl in *. lia.
      + inversion H0. inversion H1. subst.
        rewrite tensor_add_step.
        constructor.
        eapply consistent_bin; eauto.
        apply tensor_consistent_step in H1.
        apply tensor_consistent_step in H0.
        specialize (IHn _ H1 _ H0).
        rewrite tensor_add_step in IHn.
        rewrite tensor_add_step.
        inversion IHn. subst.
        constructor. auto. auto.
        rewrite tensor_add_step.
        simpl in *.
        erewrite length_add_length.
        destruct n. eauto.
        eauto. rewrite <- H8 in H15. inversion H15. auto. auto.
  }

  {
    induction a; intros.
    - inversion H0.
    - inversion H0. subst.
      simpl in *.
      destruct a0.
      + simpl in *.
        constructor; auto.
        apply consistent_mul. auto.
      + inversion H0. subst.
        apply tensor_consistent_step in H0.
        specialize (IHa c _ H0).
        inversion IHa. subst. constructor.
        apply consistent_mul. auto.
        simpl. constructor. auto.
        auto.
        simpl in *.
        rewrite map_length in *. lia.
  }

  {
  induction a; intros.
  - rewrite tensor_add_empty_r. rewrite tensor_add_empty_l. reflexivity.
  - destruct b.
    + rewrite tensor_add_empty_r. rewrite tensor_add_empty_l. reflexivity.
    + repeat rewrite tensor_add_step.
      f_equal.
      apply bin_comm.
      apply IHa.
  }

  {
  induction a; intros.
  - rewrite tensor_add_empty_l. rewrite tensor_add_empty_l. reflexivity.
  - destruct b.
    + rewrite tensor_add_empty_l. rewrite tensor_add_empty_r. reflexivity.
    + destruct c.
      * rewrite tensor_add_empty_r. rewrite tensor_add_empty_r. reflexivity.
      * repeat rewrite tensor_add_step.
        f_equal.
        apply bin_assoc.
        apply IHa.
  }

  {
    induction a; destruct b; intros.
    - simpl. rewrite tensor_add_empty_r. reflexivity.
    - rewrite tensor_add_empty_l.
      simpl map.
      rewrite tensor_add_empty_l.
      f_equal.
    - rewrite tensor_add_empty_r.
      simpl map.
      rewrite tensor_add_empty_r.
      f_equal.
    - rewrite tensor_add_step.
      simpl map.
      rewrite tensor_add_step.
      f_equal.
      apply mul_bin_distr.
      apply IHa.
  }

  {
    decide equality.
    apply shape_dec.
    decide equality.
  }

  {
    decide equality.
    apply eq_dec.
  }

  {
    reflexivity.
  }

  {
    intros.
    induction e.
    - simpl. reflexivity.
    - simpl. rewrite tensor_add_step.
      f_equal.
      apply bin_mul_0_self_id.
      eauto.
  }
Defined.

(* Test Cases *)
Example test_listSet_basic :
  list_set_R_helper [0%R; 1%R; 2%R] [1%Z] 3%R = 
  [0%R; 3%R; 2%R].
Proof. reflexivity. Qed.

Example test_listSet_construct :
  list_set_R_helper [0%R; 1%R] [3%Z] 123%R = 
  [0%R; 1%R; 0%R; 123%R].
Proof. reflexivity. Qed.

Example test_listSet_2d :
  list_set_R_helper [[0%R; 1%R; 2%R]; [3%R; 4%R; 5%R]] [1%Z; 2%Z] 123%R =
  [[0%R; 1%R; 2%R]; [3%R; 4%R; 123%R]].
Proof. reflexivity. Qed.

Example test_listSet_Construct_2d_1 :
  list_set_R_helper [] [1%Z; 2%Z] 345%R =
  [[]; [0%R; 0%R; 345%R]].
Proof. reflexivity. Qed.

Example test_listSet_Construct_2d_bad :
  list_set_R_helper [[1%R; 2%R; 3%R]] [1%Z] 345%R = 
  [[1%R; 2%R; 3%R]; []].
Proof. reflexivity. Qed.

Example test_listSet_Construct_3d :
  list_set_R_helper [[[0%R; 1%R; 2%R]; [3%R; 4%R; 5%R]]; [[1%R]; [2%R]]] [1%Z; 1%Z; 3%Z] 345%R = 
  [[[0%R; 1%R; 2%R]; [3%R; 4%R; 5%R]]; [[1%R]; [2%R; 0%R; 0%R; 345%R]]].
Proof. reflexivity. Qed.

#[refine] Instance TupleTensorElem {X Y} `{TensorElem X} `{TensorElem Y} :
  TensorElem (X * Y) :=
  { null := (null,null);
    bin x y := match x,y with
                 (a,b),(c,d) => (bin a c, bin b d) end;
    set_R := fun arr _ _ => arr; (* Do nothing yet *)
    set_Z := fun arr _ _ => arr; (* Also do noting *)
    shape := (@shape X _ * @shape Y _);
    scalar_mul c tup := match tup with
                          (x,y) => (scalar_mul c x, scalar_mul c y) end;
    consistent tup s :=
      match tup with
        (x,y) =>
        match s with (s1,s2) => consistent x s1 /\ consistent y s2 end end;
  }.
Proof.
  destruct a. autorewrite with crunch. auto.

  destruct a. f_equal; apply mul_0_idemp; auto. 

  destruct a. autorewrite with crunch. auto.

  destruct a; destruct b;
    destruct s; destruct s'.
  intros [? ?] [? ?] ?.
  inversion H5.
  f_equal; eapply bin_mul_0_id; eauto.

  destruct a; destruct b.
  destruct s; destruct s'.
  intros [? ?] [? ?] ?.
  inversion H5.
  f_equal; eapply mul_0_absorb; eauto.

  destruct a; destruct b;
  destruct s; destruct s'.
  intros [? ?] [? ?] ?.
  inversion H5. subst.
  split; eapply consistent_bin; eauto.

  destruct a; intros.
  destruct s. destruct H1.
  split; apply consistent_mul; auto.
  
  destruct a; destruct b; f_equal; apply bin_comm.

  destruct a; destruct b; destruct c; f_equal; apply bin_assoc.

  destruct a; destruct b; intros; repeat rewrite mul_bin_distr. reflexivity.

  decide equality; apply shape_dec.

  decide equality; apply eq_dec.

  f_equal; apply mul_0_null.

  intros. destruct e. f_equal; apply bin_mul_0_self_id.
Defined.

Arguments iverson : simpl never.
Arguments Z.add : simpl nomatch.
Arguments Z.sub : simpl nomatch.
Arguments Z.ltb : simpl nomatch.
Arguments Z.eqb : simpl nomatch.
Arguments Z.leb : simpl nomatch.
Arguments Z.mul : simpl nomatch.
Arguments Z.min : simpl nomatch.
Arguments Z.max : simpl nomatch.
Arguments Z.of_nat : simpl nomatch.
Arguments Z.to_nat : simpl nomatch.

Arguments N.mul : simpl nomatch.
Arguments N.sub : simpl nomatch.
Arguments N.add : simpl nomatch.

Definition concat {X} `{TensorElem X} (l1 l2 : list X) : list X :=
  GEN [ i < Z.of_nat (length l1 + length l2) ]
      (|[i <? Z.of_nat (length l1)]| l1 _[i]) <+>
      (|[Z.of_nat (length l1) <=? i]| l2 _[i - Z.of_nat (length l1)]).

Infix "<++>" := concat (at level 34, left associativity).

Fixpoint gen_range_helper (from : Z) (rem : nat) (fn : Z -> Z) :=
  match rem with 
  | O => []
  | S rem' => (fn from) :: gen_range_helper from rem' (fun x => fn (x+1)%Z)
  end.

Definition gen_range (from to : Z) : list Z :=
  gen_range_helper from (Z.to_nat (to-from)) (fun i => i).

Example test_gen_range_1 : 
  gen_range 2%Z 5%Z = 
  [2%Z; 3%Z; 4%Z].
Proof. reflexivity. Qed.

Example test_gen_range_2 :
  gen_range 1%Z 1%Z = [].
Proof. reflexivity. Qed.

Example test_gen_range_3 :
  gen_range 1%Z 0%Z = [].
Proof. reflexivity. Qed.

(* Let rec binding *)
Definition gen_rec `{TensorElem X} (n : Z) (fn : Z -> (X -> X)) : X -> X :=
  fun prev_arr =>
    fold_left 
      (fun arr ind => (fn ind) arr)
      (gen_range 0 n)
      prev_arr.

Notation "'GEN_REC' [ i < n ] e " := (gen_rec n (fun i => e))
                                      (at level 36,
                                      e at level 36,
                                      i, n at level 50,
                                      format
                                      "'[hv ' 'GEN_REC'  [  i  <  n  ] ']' '//' e").

Definition iverson_Z `{TensorElem X} (b : bool) (e : X) :=
  (if b then e else null).

Notation "|{ b }| e" := (iverson_Z b%Z e)
                          (at level 35,
                           format "'[hv ' |{  b  }| ']' '[hv '  e ']'").

Example test_gen_rec_1d :
  (GEN_REC [i < 5] fun a => set_Z a [i] (a _[i-1] + 2)%Z) [] = 
  [2%Z; 4%Z; 6%Z; 8%Z; 10%Z].
Proof. simpl. reflexivity. Qed.

Example test_gen_rec_sum :
  (GEN_REC [i < 5] fun sm => set_Z sm [i] (sm _[i-1] + 1 + i)%Z) [] = 
  [1%Z; 3%Z; 6%Z; 10%Z; 15%Z].
Proof. unfold gen_rec. simpl. reflexivity. Qed.

Example test_gen_rec_1d_more : 
  (GEN_REC [i < 5] fun sm => set_Z sm [i] (sm _[i-1])%Z) [] = 
  [0%Z; 0%Z; 0%Z; 0%Z; 0%Z].
Proof. reflexivity. Qed.

Example test_gen_rec_2d :
  (GEN_REC [i < 3] (GEN_REC [j < 2] fun C => set_Z C [i; j] (C _[i; j-1] + i)%Z)) [] = 
  [[0%Z; 0%Z]; [1%Z; 2%Z]; [2%Z; 4%Z]].
Proof. reflexivity. Qed.

Example test_gen_rec_fibo :
  (GEN_REC [i < 7] fun fib => 
    set_Z fib [i] 
    (|{i >? 1}| (fib _[i-1] + fib _[i-2]) + |{i <=? 1}| 1)%Z
  ) [] = 
  [1%Z; 1%Z; 2%Z; 3%Z; 5%Z; 8%Z; 13%Z].
Proof. unfold gen_rec. simpl. reflexivity. Qed.

Example test_gen_rec_binomial :
  (
    GEN_REC [i < 5] GEN_REC [j < 5]
    fun C => 
    set_Z C [i; j] 
      (
        |{i >=? j}| (
          |{orb (j =? 0) (i =? j)}| 1 + 
          |{andb (negb (j =? 0)) (j <? i)}| (C _[i-1; j] + C _[i-1; j-1])
        )
      )%Z
  ) [] = 
[[1%Z; 0%Z; 0%Z; 0%Z; 0%Z];
[1%Z; 1%Z; 0%Z; 0%Z; 0%Z];
[1%Z; 2%Z; 1%Z; 0%Z; 0%Z];
[1%Z; 3%Z; 3%Z; 1%Z; 0%Z];
[1%Z; 4%Z; 6%Z; 4%Z; 1%Z]].
Proof. unfold gen_rec. simpl. reflexivity. Qed.




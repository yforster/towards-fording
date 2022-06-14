Require Export MetaCoq.Template.All.
Require Export MetaCoq.Template.Checker.
Require Export List.
Export ListNotations MCMonadNotation.

Existing Instance config.default_checker_flags.
Existing Instance default_fuel.

Open Scope bs.

From MetaCoq.Template Require Import Checker.
Import MCMonadNotation ListNotations.

Definition try_infer `{config.checker_flags} `{Fuel} (Σ : global_env_ext) Γ t :=
  match infer' Σ Γ t with Checked res => res | TypeError _ => tApp (tVar "error") [t] end.

Fixpoint ford_arith
  (n : nat)            (* index for lifting *)
  (args : list term) (* the list of arguments *)
  (tys : list term)  (* the types of the arguments *)
  (t : term)         (* head of the return type *)
  : term 
(*
   for args = [a_1, ..., a_n], tys = [ty_1, ..., ty_n]
   returns
   ```
   forall x_1 : ty_1, x_1 = ty_1 ->
   ... ->
   forall x_n : ty_n, x_n = ty_n ->
   t x_1 ... x_n
   ```
   properly lifted using n
*)
  :=
  match args, tys with
    a :: args, ty :: tys =>
      tProd (mkBindAnn nAnon Relevant)
        (lift n 0 ty)
        (tProd (mkBindAnn nAnon Relevant)
                 (tApp <% @eq %> [ty ; (tRel 0) ; (lift (1 + 2 * n) 0 a)])
                 (ford_arith (S n) args tys t))
  | nil, nil => tApp (lift (2 * n) 0 t) (map (fun i => tRel (2 * i + 1)) (rev (seq 0 n)))
  | _, _ => tVar "error"%bs
  end.

Fixpoint ford_forward
  (n : nat)            (* index for lifting "old" things *)
  (gen : list nat)     (* the new information generated, in this case the variables x_1 ... x_n for the result *)
  (args : list term) (* the list of arguments *)
  (tys : list term)  (* the types of the arguments *)
  (t : term)         (* head of the return type *)
  : term 
(*
   for args = [a_1, ..., a_n], tys = [ty_1, ..., ty_n]
   returns
   ```
   forall x_1 : ty_1, x_1 = ty_1 ->
   ... ->
   forall x_n : ty_n, x_n = ty_n ->
   t x_1 ... x_n
   ```
   properly lifted using n
*)
  :=
  match args, tys with
    a :: args, ty :: tys =>
      tProd (mkBindAnn nAnon Relevant)
        (lift n 0 ty)
        (tProd (mkBindAnn nAnon Relevant)
                 (tApp <% @eq %> [ty ; (tRel 0) ; (lift (1 + n) 0 a)]) (* 1 + n because we introduced one binder *)
                 (ford_forward (S (S n)) (1 :: map (S ∘ S) gen) args tys (lift 2 0 t))) (* S (S n) because we introduced two binders, same for lift 2 0 t *)
  | nil, nil => tApp t (map tRel (rev gen)) (* we could also do lift n 0 t here, and not update t in recursive calls *)
  | _, _ => tVar "error"%bs
  end.

(** In the style of ford_forward
   it should be easy to write two functions ford_forward1 and ford_forward2 which if composed
   for args = [a_1, ..., a_n], tys = [ty_1, ..., ty_n]
   return
   ```
   forall x_1 : ty_1, ..., forall x_n : ty_n,
   x_1 = ty_1 -> ... -> x_n = ty_n ->
   t x_1 ... x_n
   ```
   ford_forward1 returns
   - the term t properly lifted
   - a list [ ty_1, .., ty_n ] properly lifted
   - and a list [x_1, ..., x_n ]
   then ford_forward2 does recursion on the first list and generates
   x_1 = ty_1 -> ... -> x_n = ty_n ->
   t x_1 ... x_n
   ( while always updating the second list and lifting t properly)
 *)

Fixpoint ford_type ford Σ Γ (t : term) :=
  match t with
  | tProd na A B =>
      tProd na A (ford_type ford Σ (Γ ,, vass na A) B)
  | tApp t args =>
      ford args (map (try_infer Σ Γ) args) t
  | _ => tVar "error"
  end.

Definition run_fording ford (A : Type) :=
  p <- tmQuoteRec A ;;
  let (Σ, sA) := (p : program) in
  r <- tmEval cbv (ford_type ford (Σ, Monomorphic_ctx) [] sA) ;;
  (* tmPrint r ;; ret r. *)
  res <- tmUnquote r ;;
  tmPrint res ;;
  ret res.

Inductive test : nat -> Type -> nat -> Prop := .

MetaCoq Run (run_fording (ford_arith 0) (forall n m, test n nat m)).
MetaCoq Run (run_fording (ford_arith 0) (forall (T : nat -> Type -> nat -> Prop) n m, T n nat m)).
MetaCoq Run (run_fording (ford_forward 0 []) (forall n m, test n nat m)).
MetaCoq Run (run_fording (ford_forward 0 []) (forall (T : nat -> Type -> nat -> Prop) n m, T n nat m)).





(** Version with general renamings, a bit more complicated but necessary in general  *)

Section map_predicate_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (finst : Instance.t -> Instance.t).
  Context (f : nat -> T).

  Definition map_predicate_shift (p : predicate term) :=
    {| pparams := map (fn f) p.(pparams);
        puinst := finst p.(puinst);
        pcontext := p.(pcontext);
        preturn := fn (shift #|p.(pcontext)| f) p.(preturn) |}.

  Lemma map_shift_pparams (p : predicate term) :
    map (fn f) (pparams p) = pparams (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_preturn (p : predicate term) :
    fn (shift #|p.(pcontext)| f) (preturn p) = preturn (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_pcontext (p : predicate term) :
    (pcontext p) =
    pcontext (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.

  Lemma map_shift_puinst (p : predicate term) :
    finst (puinst p) = puinst (map_predicate_shift p).
  Proof using Type. reflexivity. Qed.
  
End map_predicate_shift.

Section map_branch_shift.
  Context {T : Type}.
  Context (fn : (nat -> T) -> term -> term).
  Context (shift : nat -> (nat -> T) -> nat -> T).
  Context (f : nat -> T).

  Definition map_branch_shift (b : branch term) :=
  {| bcontext := b.(bcontext);
      bbody := fn (shift #|b.(bcontext)| f) b.(bbody) |}.

  Lemma map_shift_bbody (b : branch term) :
    fn (shift #|b.(bcontext)| f) (bbody b) = bbody (map_branch_shift b).
  Proof using Type. reflexivity. Qed.
  
  Lemma map_shift_bcontext (b : branch term) :
    (bcontext b) = bcontext (map_branch_shift b).
  Proof using Type. reflexivity. Qed.
End map_branch_shift.

(** Shift a renaming [f] by [k]. *)
Definition shiftn k f :=
  fun n => if Nat.ltb n k then n else k + (f (n - k)).

Notation map_branches_shift ren f :=
  (map (map_branch_shift ren shiftn f)).
  
Fixpoint rename f t : term :=
  match t with
  | tRel i => tRel (f i)
  | tEvar ev args => tEvar ev (List.map (rename f) args)
  | tLambda na T M => tLambda na (rename f T) (rename (shiftn 1 f) M)
  | tApp u v => tApp (rename f u) (map (rename f) v)
  | tProd na A B => tProd na (rename f A) (rename (shiftn 1 f) B)
  | tLetIn na b t b' => tLetIn na (rename f b) (rename f t) (rename (shiftn 1 f) b')
  | tCase ind p c brs =>
    let p' := map_predicate_shift rename shiftn id f p in
    let brs' := map_branches_shift rename f brs in
    tCase ind p' (rename f c) brs'
  | tProj p c => tProj p (rename f c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Fixpoint ford_ren
  (ren : nat -> nat)     (* the renamings to apply to "old" parts of the term *)
  (gen : list nat)    (* the new information generated, in this case the variables x_1 ... x_n for the result *)
  (args : list term) (* the list of arguments *)
  (tys : list term)  (* the types of the arguments *)
  (t : term)         (* head of the return type *)
  : term 
(*
   for args = [a_1, ..., a_n], tys = [ty_1, ..., ty_n]
   returns
   ```
   forall x_1 : ty_1, x_1 = ty_1 ->
   ... ->
   forall x_n : ty_n, x_n = ty_n ->
   t x_1 ... x_n
   ```
   properly lifted using n
*)
  :=
  match args, tys with
    a :: args, ty :: tys =>
      tProd (mkBindAnn nAnon Relevant)
        (rename ren ty)
        (tProd (mkBindAnn nAnon Relevant)
                 (tApp <% @eq %> [ty ; (tRel 0) ; (rename (S ∘ ren) a)])
                 (ford_ren (S ∘ S ∘ ren) (1 :: map (S ∘ S) gen) args tys t))
  | nil, nil => tApp (rename ren t) (map tRel (rev gen))
  | _, _ => tVar "error"%bs
  end.

MetaCoq Run (run_fording (ford_ren (fun i => i) []) (forall n m, test n nat m)).
MetaCoq Run (run_fording (ford_ren (fun i => i) []) (forall (T : nat -> Type -> nat -> Prop) n m, T n nat m)).

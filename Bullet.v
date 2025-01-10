(* Coq encoding of Bulletproof but I haven't proved it correct. *)

From Coq Require Import Utf8 Vector.

Import VectorNotations.

Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Section VectorUtil. 


  Definition zip_with {P T U : Type} : 
    forall {n : nat}, (P -> T -> U) ->  
    Vector.t P n -> Vector.t T n -> Vector.t U n.
  Proof.
    refine(
      fix zip_with n f u {struct u} :=
      match u as u' in Vector.t _ n'  
        return
          forall (pf : n' = n), 
            u = eq_rect n' _ u' n pf -> 
            Vector.t T n' -> Vector.t U n'  
      with 
      | nil _ => 
          fun pf H v => @nil _ 
      | cons _ hu m tu => 
          fun pf H v => 
          match v as v' in Vector.t _ (S m')
            return 
              forall (pf : m' = m),
                v = eq_rect m' (fun w => Vector.t T (S w)) v' m pf ->
                Vector.t U (S m') 
          with 
          | nil _ => idProp
          | cons _ hv n tv => 
              fun pfv Hv => 
                cons _ 
                  (f hu hv) _ 
                  _ 
          end eq_refl eq_refl 
      end eq_refl eq_refl
    ).
    subst.
    exact (zip_with _ f tu tv).
  Defined.


  Definition Matrix {U : Type} (n m : nat) : Type := 
    Vector.t (Vector.t U m) n.


  
  Definition vector_inv {U : Type} : 
    forall {n : nat} (v : Vector.t U n), 
    match n return Vector.t U n -> Type
    with 
    | 0 => fun v => v = @nil U
    | S n' => fun v => {'(vh, vt) & vh :: vt = v}
    end v.
  Proof.
    intros n v.
    destruct v as [ | vh n' vt];
    [exact eq_refl | ].
    exists (vh, vt);
    exact eq_refl.
  Defined.

  Definition vector_inv_nil {U : Type} : 
    forall (v : Vector.t U 0), v = @nil U.
  Proof.
    intro v.
    destruct (vector_inv v).
    exact eq_refl.
  Defined. 

  Definition vector_inv_cons {U : Type} : 
    forall {n : nat} (v : Vector.t U (S n)), 
    {'(vh, vt) & vh :: vt = v}.
  Proof.
    intros *.
    destruct (vector_inv v) as ((va & vb) & Ha).
    exists (va, vb); exact Ha.
  Defined.
  
End VectorUtil.
Section Bullet. 

  Context 
    {F : Type} 
    {eqf : ∀ (u v : F), {u = v} + {u <> v}}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.

  Context 
    {V : Type} 
    {eqv : ∀ (u v : F), {u = v} + {u <> v}}
    {vid : V} {vopp : V -> V}
    {vadd : V -> V -> V} 
    {smul : F -> V -> V}.


  Definition pedersen_commitment (g h : V) (m r : F) : V := 
    vadd (smul m g) (smul r h). 

  Definition pedersen_vector_commitment {n : nat} 
    (gs : Vector.t V n)  (h : V) (ms : Vector.t F n) (r : F) : V := 
    vadd (smul r h) (Vector.fold_left (fun (u : V) 
    '(mi, gi) => vadd u (smul mi gi)) vid (zip_with (fun x y => (x, y)) ms gs)).

  Definition inner_product_scalor {n : nat} (us vs : Vector.t F n) : F := 
    Vector.fold_left (fun u '(ui, vi) => add u (mul ui vi)) zero 
      (zip_with (fun x y => (x, y)) us vs).

  Definition inner_product_vector {n : nat} (gs : Vector.t V n) (ms : Vector.t F n) : V := 
     Vector.fold_left (fun u '(mi, gi) => vadd u (smul mi gi)) vid 
      (zip_with (fun x y => (x, y)) ms gs).


  Definition pointwise_product_scalor {n : nat} 
    (us vs : Vector.t F n) : Vector.t F n := 
    zip_with (fun x y => mul x y) us vs.

  Definition pointwise_product_vector {n : nat} 
    (us vs : Vector.t V n) : Vector.t V n := 
    zip_with (fun x y => vadd x y) us vs.

  Definition map_scalor_vector {n : nat}
    (r : F) (us : Vector.t V n) : Vector.t V n :=
    Vector.map (fun x => smul r x) us.
  
  Definition map_scalor_scalor {n : nat}
    (r : F) (us : Vector.t F n) : Vector.t F n :=
    Vector.map (fun x => mul r x) us.

  Definition pointwise_add_scalor {n : nat} 
    (us vs : Vector.t F n) : Vector.t F n := 
    zip_with (fun x y => add x y) us vs.

  Definition hadamard_product {n : nat} 
    (us vs : @Matrix F n n) : Vector.t F n := 
    zip_with (fun x y => inner_product_scalor x y) us vs.





  Definition inner_product_proof : forall {n : nat},
    Vector.t V (Nat.pow 2 n) -> Vector.t V (Nat.pow 2 n) -> V -> V -> 
    Vector.t F (Nat.pow 2 n) -> Vector.t F (Nat.pow 2 n) -> 
    Vector.t F n -> 
    Vector.t V (1 + n) * Vector.t V (1 + n) * V * V * F * F .
  Proof.
    refine(fix inner_product_proof (n : nat) := 
      match n with 
      | 0 => fun gs hs u P a b _ => _
      | S n' => fun gs hs u P a b xs => _ 
      end).
    +
      cbn in * |- *.
      exact (gs, hs, u, P, hd a, hd b).
    +
      cbn in * |- *.
      rewrite PeanoNat.Nat.add_0_r in gs, hs, a, b.
      destruct (Vector.splitat (Nat.pow 2 n') a) as (al & ar).
      destruct (Vector.splitat (Nat.pow 2 n') b) as (bl & br).
      destruct (Vector.splitat (Nat.pow 2 n') gs) as (gsl & gsr).
      destruct (Vector.splitat (Nat.pow 2 n') hs) as (hsl & hsr).
      destruct (vector_inv_cons xs) as ((xh & xss) & _).
      remember (inner_product_scalor al br) as cL.
      remember (inner_product_scalor ar bl) as cR.
      remember (vadd (inner_product_vector gsr al) 
        (vadd (inner_product_vector hsl br) (smul cL u))) as L. 
      remember (vadd (inner_product_vector gsl ar) 
        (vadd (inner_product_vector hsr bl) (smul cR u))) as R.
      (* This L and R need to be send to the Verifier *)
      remember (pointwise_product_vector 
        (map_scalor_vector (inv xh) gsl) 
        (map_scalor_vector xh gsr)) as g'.
      remember (pointwise_product_vector
        (map_scalor_vector xh hsl) 
        (map_scalor_vector (inv xh) hsr)) as h'.
      remember (vadd (smul (mul xh xh) L)
        (vadd P (smul (mul (inv xh) (inv xh)) R))) as P'.
      remember (pointwise_add_scalor 
        (map_scalor_scalor xh al)
        (map_scalor_scalor (inv xh) ar)) as a'.
      remember (pointwise_add_scalor
        (map_scalor_scalor (inv xh) bl)
        (map_scalor_scalor xh br)) as b'.
      destruct (inner_product_proof _ g' h' u P' a' b' xss) as 
        (((((L'' & R'') & u'') & P'') & a'') & b'').
      exact (L :: L'', R :: R'', u'', P'', a'', b''). 
  Defined.


  
  

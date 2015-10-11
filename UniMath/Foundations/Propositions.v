(** * Generalities on hProp.  Vladimir Voevodsky . May - Sep. 2011 . 

In this file we introduce the hProp - an analog of Prop defined based on the univalent semantics. We further introduce the hProp version of the "inhabited" construction - i.e. for any [ T ] in [ UU0 ] we construct an object  [ ishinh T ] and a function [ hinhpr : T -> ishinh T ] which plays the role of [ inhabits ] from the Coq standard library.  The semantic meaning of  [ hinhpr ] is that it is universal among functions from [ T ]  to objects of hProp. Proving that [ ishinh  T ] is in [ hProp ] requires a resizing rule which can be written in the putative notation for such rules as follows :

Resizing Rule RR1 ( U1 U2 : Univ ) ( X : U1 ) ( is : isaprop X ) |- X : U2 .

Further in the file we introduce the univalence axiom for hProp and a proof of the fact that it is equivalent to a simplier and better known axiom [ uahp ]. We prove that this axiom implies that [ hProp ] satisfies [ isaset ] i.e. it is a type of h-level 2 . This requires another resizing rule :

Resizing Rule RR2 ( U1 U2 : Univ ) |- @hProp U1 : U2 . 

Since resizing rules are not currently implemented in Coq the file does not compile without a patch provided by Hugo Herbelin which turns off the universe consistency verification. We do however keep track of universes in our development "by hand" to ensure that when the resizing rules will become available the current proofs will verify correctly. To point out which results require resizing rules in a substantial way we mark the first few of such reults by (** RR1 *) or (** RR2 *) comment . 

One can achieve similar results with a combination of usual axioms which imitate the resizing rules.  However unlike the usual axioms the resizing rules do not affect the computation/normalization abilities of Coq which makes them the prefrred choice in this situation.


*)



(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** Imports *)

Require Export UniMath.Foundations.Basics.All.

(** Universe structure *)

(* Definition UU0 := UU . *)

(* end of " Preamble " . *)


(** ** To upstream files *)



(** ** The type [ hProp ] of types of h-level 1 *)

 
Definition hProp := total2 ( fun X : UU => isaprop X ) .
Definition hProppair ( X : UU ) ( is : isaprop X ) : hProp := tpair (fun X : UU => isaprop X ) X is .
Definition hProptoType := @pr1 _ _ : hProp -> UU .
Coercion hProptoType: hProp >-> UU.

Definition propproperty (P:hProp) := pr2 P : isaprop (pr1 P).

(** ** The type [ tildehProp ] of pairs ( P , p : P ) where [ P : hProp ] *)

Definition tildehProp := total2 ( fun P : hProp => P ) .
Definition tildehProppair { P : hProp } ( p : P ) : tildehProp := tpair _ P p . 


(** The following re-definitions should make proofs easier in the future when the unification algorithms in Coq are improved . At the moment they create more complications than they eliminate ( e.g. try to prove [ isapropishinh ] with [ isaprop ] in [ hProp ] ) so for the time being they are commented out .


(** *** Re-definitions of some of the standard constructions of uu0.v which lift these contructions from UU to hProp . *)


Definition iscontr ( X : UU ) : hProp := hProppair _ ( isapropiscontr X ) . 

Definition isweq { X Y : UU } ( f : X -> Y ) : hProp := hProppair _ ( isapropisweq f ) . 

Definition isofhlevel ( n : nat ) ( X : UU ) : hProp := hProppair _ ( isapropisofhlevel n X ) .

Definition isaprop ( X : UU ) : hProp := hProppair ( isaprop X ) ( isapropisaprop X ) .

Definition isaset ( X : UU ) : hProp := hProppair _ ( isapropisaset X ) .

Definition isisolated ( X : UU ) ( x : X ) : hProp := hProppair _ ( isapropisisolated X x ) .

Definition isdecEq ( X : UU ) : hProp := hProppair _ ( isapropisdeceq X ) .   

*)


(** ** Intuitionistic logic on [ hProp ] *)


(** *** The [ hProp ] version of the "inhabited" construction. *)



Definition ishinh_UU ( X : UU ) := forall P: hProp, ( ( X -> P ) -> P ). 

Lemma isapropishinh ( X : UU ) : isaprop ( ishinh_UU X ). 
Proof. intro. apply impred . intro P . apply impred.  intro. apply ( pr2 P ) .  Defined . 

Definition ishinh ( X : UU ) : hProp := hProppair ( ishinh_UU X ) ( isapropishinh X ) .

Notation nonempty := ishinh (only parsing).

Notation "∥ A ∥" := (ishinh A) (at level 200) : type_scope.
(* written \|| *)

Definition hinhpr ( X : UU ) : X -> ishinh X := fun x : X => fun P : hProp  => fun f : X -> P => f x .

Definition hinhfun { X Y : UU } ( f : X -> Y ) : ishinh_UU X -> ishinh_UU Y := fun isx : ishinh X => fun P : _ =>  fun yp : Y -> P => isx P ( fun x : X => yp ( f x ) ) .

(** Note that the previous definitions do not require RR1 in an essential way ( except for the placing of [ ishinh ] in [ hProp UU ] - without RR1 it would be placed in [ hProp UU1 ] ) . The first place where RR1 is essentially required is in application of [ hinhuniv ] to a function [ X -> ishinh Y ] *)

Definition hinhuniv { X : UU } { P : hProp } ( f : X -> P ) ( wit : ishinh_UU X ) : P :=  wit P f .


Definition hinhand { X Y : UU } ( inx1 : ishinh_UU X ) ( iny1 : ishinh_UU Y) : ishinh ( dirprod X Y ) := fun P:_  => ddualand (inx1 P) (iny1 P).

Definition hinhuniv2 { X Y : UU } { P : hProp } ( f : X -> Y -> P ) ( isx : ishinh_UU X ) ( isy : ishinh_UU Y ) : P := hinhuniv ( fun xy : dirprod X Y => f ( pr1 xy ) ( pr2 xy ) ) ( hinhand isx isy ) . 

Definition hinhfun2 { X Y Z : UU } ( f : X -> Y -> Z ) ( isx : ishinh_UU X ) ( isy : ishinh_UU Y ) : ishinh Z := hinhfun ( fun xy: dirprod X Y => f ( pr1 xy ) ( pr2 xy ) ) ( hinhand isx isy ) .

Definition hinhunivcor1 ( P : hProp ) : ishinh_UU P -> P := hinhuniv ( idfun P ).
Notation hinhprinv := hinhunivcor1 .


(** *** [ ishinh ] and negation [ neg ] *)


Lemma weqishinhnegtoneg ( X : UU ) : weq ( ishinh ( neg X ) ) ( neg X ) .
Proof . intro . assert ( lg : logeq ( ishinh ( neg X ) ) ( neg X ) ) . split . simpl . apply ( @hinhuniv _ ( hProppair _ ( isapropneg X ) ) ) .    simpl . intro nx . apply nx . apply hinhpr . apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 ( ishinh _ ) ) ( isapropneg X ) ) .  Defined . 

Lemma weqnegtonegishinh ( X : UU ) : weq ( neg X ) ( neg ( ishinh X ) ) .
Proof . intro .  assert ( lg : logeq ( neg ( ishinh X ) ) ( neg X ) ) . split . apply ( negf ( hinhpr X ) ) .  intro nx .  unfold neg .  simpl . apply ( @hinhuniv _ ( hProppair _ isapropempty ) ) .  apply nx . apply ( weqimplimpl ( pr2 lg ) ( pr1 lg ) ( isapropneg _ ) ( isapropneg _ ) ) .   Defined . 

 
(** *** [ ishinh ] and [ coprod ] *)


Lemma hinhcoprod ( X Y : UU ) ( is : ishinh ( coprod ( ishinh X ) ( ishinh Y ) ) )  : ishinh ( coprod X Y ) .
Proof. intros . unfold ishinh. intro P .  intro CP.  set (CPX := fun x : X => CP ( ii1 x ) ) . set (CPY := fun y : Y => CP (ii2 y) ).  set (is1P := is P).
       assert ( f : coprod ( ishinh X ) ( ishinh Y ) -> P ) .  apply ( sumofmaps ( hinhuniv CPX ) ( hinhuniv CPY ) ).   apply (is1P f ) . Defined.


(** ** Images and surjectivity for functions between types 
(both depend only on the behavior of the corresponding function between the sets of 
connected components) **)

Definition image { X Y : UU } ( f : X -> Y ) := total2 ( fun y : Y => ishinh ( hfiber f y ) ) .
Definition imagepair { X Y : UU } (f: X -> Y) := tpair ( fun y : Y => ishinh ( hfiber f y ) ) .
Definition pr1image { X Y : UU } ( f : X -> Y ) := @pr1 _  ( fun y : Y => ishinh ( hfiber f y ) ) .


Definition prtoimage { X Y : UU } (f : X -> Y) : X -> image f.
Proof. intros X Y f X0. apply (imagepair _ (f X0) (hinhpr _ (hfiberpair f X0 (idpath _ )))). Defined. 

Definition issurjective { X Y : UU } (f : X -> Y ) := forall y:Y, ishinh (hfiber f y). 

Lemma isapropissurjective { X Y : UU } ( f : X -> Y) : isaprop (issurjective f).
Proof. intros.  apply impred. intro t. apply  (pr2 (ishinh (hfiber f t))). Defined. 

Lemma isinclpr1image { X Y : UU } (f:X -> Y): isincl (pr1image f).
Proof. intros. apply isofhlevelfpr1. intro. apply ( pr2 ( ishinh ( hfiber f x ) ) ) . Defined.

Lemma issurjprtoimage { X Y : UU } ( f : X -> Y) : issurjective (prtoimage f ).
Proof. intros. intro z.  set (f' := prtoimage f ). set (g:= pr1image f ). set (gf':= fun x:_ => g ( f' x )).
assert (e: paths f gf'). apply etacorrection .  
assert (ff: hfiber gf' (pr1 z) -> hfiber f' z).   apply ( invweq ( samehfibers _ _ ( isinclpr1image f ) z ) ) .  
assert (is2: ishinh (hfiber gf' (pr1 z))). destruct e.  apply (pr2 z). 
apply (hinhfun ff is2). Defined. 




(** *** The two-out-of-three properties of surjections *)

Lemma issurjcomp { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isf : issurjective f ) ( isg : issurjective g ) : issurjective ( funcomp f g ) .
Proof . intros . unfold issurjective .  intro z . apply ( fun ff => hinhuniv ff ( isg z ) ) . intro ye .  apply ( hinhfun ( hfibersftogf f g z ye ) ) .  apply ( isf ) .   Defined . 

Notation issurjtwooutof3c := issurjcomp . 

Lemma issurjtwooutof3b { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isgf : issurjective ( funcomp f g ) ) : issurjective g .  
Proof . intros . unfold issurjective .  intro z .  apply ( hinhfun ( hfibersgftog f g z ) ( isgf z ) ) .  Defined . 

(** *** A function between types which is an inclusion and a surjection is a weak equivalence *)

Lemma isweqinclandsurj { X Y : UU } ( f : X -> Y ) : isincl f -> issurjective f -> isweq f .
Proof .
  intros X Y f Hincl Hsurj.
  intro y.
  set (H := hProppair (iscontr (hfiber f y)) (isapropiscontr _ )).
  apply (Hsurj y H).
  intro x.
  simpl.
  apply iscontraprop1.
  - apply Hincl.
  - apply x.
Defined.

(** On the other hand, a weak equivalence is surjective *)

Lemma issurjectiveweq (X Y : UU) (f : X -> Y) : isweq f -> issurjective f.
Proof.
  intros X Y f H y.
  apply hinhpr.
  apply (pr1 (H y)).
Defined.


 

(** *** Intuitionistic logic on [ hProp ]. *)


Definition htrue : hProp := hProppair unit isapropunit.

Definition hfalse : hProp := hProppair empty isapropempty.

Definition hconj ( P Q : hProp ) : hProp := hProppair ( dirprod P Q ) ( isapropdirprod _ _ ( pr2 P ) ( pr2 Q ) ). 

Definition hdisj ( P Q : UU ) : hProp :=  ishinh ( coprod P Q ) . 

Definition hneg ( P : UU ) : hProp := hProppair ( neg P ) ( isapropneg P ) . 

Definition himpl ( P : UU ) ( Q : hProp ) : hProp.
Proof. intros. split with ( P -> Q ) . apply impred. intro. apply (pr2  Q). Defined. 

Definition hexists { X : UU } ( P : X -> UU ) := ishinh ( total2 P ) .

Definition wittohexists { X : UU } ( P : X -> UU ) ( x : X ) ( is : P x ) : hexists P := hinhpr ( total2 P ) (tpair _ x is ) .

Definition total2tohexists { X : UU } ( P : X -> UU ) : total2 P -> hexists P := hinhpr _ . 

Definition weqneghexistsnegtotal2   { X : UU } ( P : X -> UU ) : weq ( neg ( hexists P ) ) ( neg ( total2 P ) ) .
Proof . intros . assert ( lg : ( neg ( hexists P ) ) <-> ( neg ( total2 P ) )  ) . split . apply ( negf ( total2tohexists P ) ) . intro nt2 . unfold neg . change ( ishinh_UU ( total2 P ) -> hfalse ) . apply ( hinhuniv ) .  apply nt2 . apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( isapropneg _ ) ( isapropneg _ ) ) .  Defined . 


(** *** Associativity and commutativity of [ hdisj ] and [ hconj ] up to logical equivalence *)

Lemma islogeqcommhdisj { P Q : hProp } : hdisj P Q <-> hdisj Q P .
Proof . intros . split . simpl .  apply hinhfun .  apply coprodcomm .  simpl .  apply hinhfun .  apply coprodcomm . Defined . 
 


(** *** Proof of the only non-trivial axiom of intuitionistic logic for our constructions. For the full list of axioms see e.g.  http://plato.stanford.edu/entries/logic-intuitionistic/ *)


Lemma hconjtohdisj ( P Q : UU ) ( R : hProp ) :  hconj ( himpl P R ) ( himpl Q R ) -> himpl ( hdisj P Q ) R .
Proof.  intros P Q R X0. 
assert (s1: hdisj P Q -> R) . intro X1.  
assert (s2: coprod P Q -> R ) . intro X2. destruct X2 as [ XP | XQ ].  apply X0. apply XP . apply ( pr2 X0 ). apply XQ . 
apply ( hinhuniv s2 ). apply X1 .   unfold himpl. simpl . apply s1 .  Defined.




(** *** Negation and quantification.

There are four standard implications in classical logic which can be summarized as ( neg ( forall P ) ) <-> ( exists ( neg P ) ) and ( neg ( exists P ) ) <-> ( forall ( neg P ) ) . Of these four implications three are provable in the intuitionistic logic.  The remaining implication ( neg ( forall P ) ) -> ( exists ( neg P ) ) is not provable in general . For a proof in the case of bounded quantification of decidable predicates on natural numbers see hnat.v . For some other cases when these implications hold see ??? . *)

Lemma hexistsnegtonegforall { X : UU } ( F : X -> UU ) : hexists ( fun x : X => neg ( F x ) ) -> neg ( forall x : X , F x ) .
Proof . intros X F . simpl . apply ( @hinhuniv _ ( hProppair _ ( isapropneg (forall x : X , F x ) ) ) ) .  simpl . intros t2 f2 . destruct t2 as [ x d2 ] .  apply ( d2 ( f2 x ) ) . Defined .

Lemma forallnegtoneghexists { X : UU } ( F : X -> UU ) : ( forall x : X , neg ( F x ) ) -> neg ( hexists F ) .
Proof. intros X F nf . change ( ( ishinh_UU ( total2 F ) ) -> hfalse ) . apply hinhuniv .   intro t2 . destruct t2 as [ x f ] .  apply ( nf x f ) . Defined . 

Lemma neghexisttoforallneg { X : UU } ( F : X -> UU ) : neg ( hexists F ) -> forall x : X , neg ( F x ) .
Proof . intros X F nhe x . intro fx .  apply ( nhe ( hinhpr _ ( tpair F x fx ) ) ) . Defined . 

Definition weqforallnegtonegexists { X : UU } ( F : X -> UU ) : weq ( forall x : X , neg ( F x ) ) ( neg ( hexists F ) ) .
Proof . intros . apply ( weqimplimpl ( forallnegtoneghexists F ) ( neghexisttoforallneg F ) ) . apply impred .   intro x . apply isapropneg . apply isapropneg . Defined . 



(** *** Negation and conjunction ( "and" ) and disjunction ( "or" ) . 

There are four implications in classical logic ( ( neg X ) and ( neg Y ) ) <-> ( neg ( X or Y ) ) and ( ( neg X ) or ( neg Y ) ) <-> ( neg ( X and Y ) ) . Of these four, three are provable unconditionally in the intuitionistic logic and the remaining one ( neg ( X and Y ) ) -> ( ( neg X ) or ( neg Y ) ) is provable only if one of the propositions is deidable. These two cases are proved in uu0.v under the names [ fromneganddecx ] and [ fromneganddecy ] .  *)

Lemma tonegdirprod { X Y : UU } ( is : hdisj ( neg X ) ( neg Y ) ) : neg ( dirprod X Y ) .
Proof. intros X Y . simpl .  apply ( @hinhuniv _ ( hProppair _ ( isapropneg ( dirprod X Y ) ) ) ) . intro c . destruct c as [ nx | ny ] . simpl .  intro xy .  apply ( nx ( pr1 xy ) ) .  simpl . intro xy . apply ( ny ( pr2 xy ) ) .  Defined .

Lemma tonegcoprod { X Y : UU } ( is : dirprod ( neg X ) ( neg Y ) ) : neg ( coprod X Y ) . 
Proof . intros. intro c . destruct c as [ x | y ] . apply ( pr1 is x ) . apply ( pr2 is y ) . Defined . 

Lemma toneghdisj { X Y : UU } ( is : dirprod ( neg X ) ( neg Y ) ) : neg ( hdisj X Y ) .
Proof . intros . unfold hdisj.  apply ( weqnegtonegishinh ) . apply tonegcoprod .  apply is .  Defined . 

Lemma fromnegcoprod { X Y : UU } ( is : neg ( coprod X Y ) ) : dirprod ( neg X ) ( neg Y ) .
Proof .  intros . split .  exact ( fun x => is ( ii1 x ) ) . exact ( fun y => is ( ii2 y ) ) . Defined .

Lemma hdisjtoimpl { P : UU } { Q : hProp } : hdisj P Q -> ( neg P -> Q ) .
Proof . intros P Q . assert ( int : isaprop ( neg P -> Q ) ) . apply impred . intro . apply ( pr2 Q ) .  simpl .  apply ( @hinhuniv _ ( hProppair _ int ) ) .  simpl .  intro pq . destruct pq as [ p | q ] . intro np . destruct ( np p ) .  intro np . apply q . Defined . 



(** *** Property of being decidable and [ hdisj ] ( "or" ) .

For being deidable [ hconj ] see [ isdecpropdirprod ] in uu0.v  *)

Lemma isdecprophdisj { X Y : UU } ( isx : isdecprop X ) ( isy : isdecprop Y ) : isdecprop ( hdisj X Y ) .
Proof . intros . apply isdecpropif . apply ( pr2 ( hdisj X Y ) ) . destruct ( pr1 isx ) as [ x | nx ] . apply ( ii1 ( hinhpr _ ( ii1 x ) ) ) . destruct ( pr1 isy ) as [ y | ny ] . apply ( ii1 ( hinhpr _ ( ii2 y ) ) ) .  apply ( ii2 ( toneghdisj ( dirprodpair nx ny ) ) ) .  Defined .    



 

(** *** The double negation version of [ hinhabited ] ( does not require RR1 ) . *)


Definition isinhdneg ( X : UU ) : hProp := hProppair ( dneg X ) ( isapropdneg X ) .

Definition inhdnegpr (X:UU): X -> isinhdneg X := todneg X.

Definition inhdnegfun { X Y : UU } (f:X -> Y): isinhdneg X -> isinhdneg Y := dnegf  f.

Definition inhdneguniv (X: UU)(P:UU)(is:isweq  (todneg P)): (X -> P) -> ((isinhdneg X) -> P) := fun xp:_ => fun inx0:_ => (invmap ( weqpair _ is ) (dnegf  xp inx0)).

Definition inhdnegand (X Y:UU)(inx0: isinhdneg X)(iny0: isinhdneg Y) : isinhdneg (dirprod X Y) := dneganddnegimpldneg  inx0 iny0.

Definition hinhimplinhdneg (X:UU)(inx1: ishinh X): isinhdneg X := inx1 hfalse.


(** ** Univalence axiom for hProp 

We introduce here the weakest form of the univalence axiom - the univalence axiom for hProp which is equivalent to the second part of the extensionality axiom in Church simple type theory.  This axiom is easily shown to be equivalent to its version with [P = P'] as a target and to [ weqtopathshProp ] (see below) as well as to the version of [ weqtopathshProp ] with [P = P'] as a target. 

The proof of theorem [ univfromtwoaxiomshProp ] is modeled on the proof of [ univfromtwoaxioms ] from univ01.v 


*)


Axiom uahp : forall P P':hProp,  (P -> P') -> (P' -> P) -> @paths hProp P P'.

Definition eqweqmaphProp { P P': hProp }  ( e: @paths hProp P P' ) : weq P P'.
Proof. intros . destruct e . apply idweq.  Defined.

Definition  weqtopathshProp { P P' : hProp } (w: weq P P' ): @paths hProp P P' := uahp P P' w ( invweq w ) .

Definition weqpathsweqhProp { P P' : hProp } (w : weq P P'): eqweqmaphProp (weqtopathshProp w) = w.
Proof. intros. apply proofirrelevance . apply (isapropweqtoprop P P' (pr2 P')). Defined.


Theorem univfromtwoaxiomshProp (P P':hProp): isweq (@eqweqmaphProp P P').
Proof. intros. 

set (P1:= fun XY: dirprod hProp hProp => paths ( pr1 XY ) ( pr2 XY ) ) . 
set (P2:= fun XY: dirprod hProp hProp => weq ( pr1 XY ) ( pr2 XY ) ) . 
set (Z1:=  total2 P1). 
set (Z2:=  total2 P2). 
set (f:= ( totalfun _ _ (fun XY: dirprod hProp hProp => 
                           @eqweqmaphProp ( pr1 XY ) ( pr2 XY )): Z1 -> Z2)). 
set (g:= ( totalfun _ _ (fun XY: dirprod hProp hProp =>                         
                           @weqtopathshProp ( pr1 XY ) ( pr2 XY )): Z2 -> Z1)). 
assert (efg : forall z2 : Z2 , paths ( f ( g z2 ) ) z2 ). intros. induction z2 as [ XY w] .  
exact ( maponpaths (fun w: weq (pr1 XY) (pr2 XY) => tpair P2 XY w) (@weqpathsweqhProp (pr1 XY) (pr2 XY) w)). 

set (h:= fun a1:Z1 => (pr1 ( pr1 a1))).
assert (egf0: forall a1:Z1,  paths ( pr1 (g (f a1))) ( pr1 a1)). intro. apply  idpath.  
assert (egf1: forall a1 a1':Z1,  paths ( pr1 a1') ( pr1 a1) -> paths a1' a1). intros ? ? X .  
set (X':=  maponpaths ( @pr1 _ _ )  X). 
assert (is:  isweq h). apply ( isweqpr1pr1 hProp ). apply ( invmaponpathsweq ( weqpair h is ) _ _ X').
set (egf:= fun a1:_ => (egf1 _ _ (egf0 a1))). 
set (is2:= gradth _ _ egf efg). 
apply ( isweqtotaltofib P1 P2  (fun XY: dirprod hProp hProp => 
                                  @eqweqmaphProp (pr1 XY) (pr2 XY)) is2 ( dirprodpair P P')).
Defined. 

Definition weqeqweqhProp ( P P' : hProp ) := weqpair _ ( univfromtwoaxiomshProp P P' ) .

Corollary isasethProp : isaset hProp.
Proof. unfold isaset.  simpl. intros x x'. apply (isofhlevelweqb (S O) ( weqeqweqhProp x x' ) (isapropweqtoprop x x' (pr2 x'))). Defined.


Lemma iscontrtildehProp : iscontr tildehProp .
Proof . split with ( tpair _ htrue tt )  .   intro tP .  destruct tP as [ P p ] . apply ( invmaponpathsincl _ ( isinclpr1 ( fun P : hProp => P ) ( fun P => pr2 P ) ) ) .   simpl . apply uahp . apply ( fun x => tt ) .  intro t.  apply p . Defined .

Lemma isaproptildehProp : isaprop tildehProp .
Proof . apply ( isapropifcontr iscontrtildehProp ) .  Defined .

Lemma isasettildehProp : isaset tildehProp .
Proof . apply ( isasetifcontr iscontrtildehProp ) . Defined .  


(* ** Logical equivalence yields weak equivalence *)

Definition logeqweq ( P Q : hProp ) : ( P -> Q ) -> ( Q -> P ) -> weq P Q := 
  fun f g => weqimplimpl f g (pr2 P) (pr2 Q).

(* ** A variant of a lemma proved in uu0b.v *)
Theorem total2_paths_hProp_equiv {A : UU} (B : A -> hProp)
   (x y : total2 (fun x => B x)): weq (x = y) (pr1 x = pr1 y).
Proof.
  intros.
  apply total2_paths_isaprop_equiv.
  intro a. apply (pr2 (B a)).
Defined.

(* End of the file hProp.v *)
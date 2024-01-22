Require Import String.
Require Import Ascii.
Require Import List.
Require Import ssreflect ssrbool.

(* --------------------------------------------------------------------- *)
(* 
  The goal of this project is to implement a helper for crosswords that takes
  as input an incomplete word (i.e., a word with some unknown letters)
  and returns the list of matching complete words together with their 
  definitions. For example, given as input t-b-, the helper returns the words
  tube, tuba, tabu, along with their definitions.

  The first challenge consists in defining a data structure that can represent
  efficiently the dictionary.

*)

Definition char := ascii.


(*

A string is esentially a list of characters: it is a datatype with two
constructors: one denoting the empty list, and the other appending a character
to an existing string.
 *)
Print string.
(*
   Inductive string : Set :=
    EmptyString : string
|   String : ascii -> string -> string.
*)


Open Scope string_scope.

(*

Double quotes denote strings, unless they are postfixed with %char, in
which case they denote single characters.

 *)
Check ("f"%char : char).
Check ("string example" : string).

(* Equality of chars *)
Infix "=c" := Ascii.eqb (at level 70).

(* false *)
Eval compute in ("c"%char =c "d"%char).
(* true *)
Eval compute in ("c"%char =c "c"%char).

(*

A dictionary is a tree whose nodes are possibly labelled by a string,
and edges are labelled by characters.

Each node represents a list of characters obtained by concatenating the labels along the
path from the root to itself. If this list of characters is actually a word,
the node is labelled with its definition.


 *)
Inductive Dictionary := 
     Entry : option string -> ListDictionary -> Dictionary
with ListDictionary :=
     Empty : ListDictionary
   | Cons : ListDictionary -> char -> Dictionary -> ListDictionary.

(*

For example, the dictionary containing the words "that", "the", "then" is represented by
the tree (unlabelled nodes are denoted by -)
                   -
                   |t
                   -
                   |h
                   -
                  / \
               a /   \ e
                /     \
               -      "denoting person(s) or thing(s) already mentioned"
              /          \ 
             /            \ n 
          t /              \
           /            "next; after that."
          /
  "1 person or thing indicated, named, or understood"

 *)
(*
---------
Exercise 
---------
Define the empty dictionary

 *)
Definition empty : Dictionary := Entry None Empty.

(*
---------
Exercise 
---------

Define the dictionary containing "that", "the", "then", as drawn above

*)
Definition that_the_then : Dictionary :=
  Entry None
    (Cons Empty "t"%char
      (Entry None
        (Cons Empty "h"%char
          (Entry None
            (Cons 
              (Cons Empty "a"%char
                (Entry None
                  (Cons Empty "t"%char (Entry (Some "used to point forward to a following qualifying or defining clause or phrase.") Empty))
                )
              )
              "e"%char
              (Entry (Some "denoting person(s) or thing(s) already mentioned")
                (Cons Empty "n"%char (Entry (Some "next; after that.") Empty)))
            )
          )
        )
      )
    ).

(*

---------
Exercise 
---------

Define a 'find' function  that takes as input a word, a dictionary, and
return the associated definition in the dictionary, or None
if the word does not exist.


*)

Fixpoint find (word : string) (dictionary : Dictionary) : option string :=
  match dictionary with
  | Entry definition listDictionary =>
    match word with
    | EmptyString => definition
    | String c rest => find_list c rest listDictionary
    end
  end
with find_list (c : char) (word : string) (listDictionary : ListDictionary) : option string :=
  match listDictionary with
  | Empty => None
  | Cons restListDictionary char' nextDictionary =>
    if char' =c c then
      find word nextDictionary
    else
      find_list c word restListDictionary
  end.

(* Your function should return the definitions  *)
Eval compute in find "that" that_the_then .
Eval compute in find "the" that_the_then .
Eval compute in find "then" that_the_then .
(* Your function should return None *)
Eval compute in find "them" that_the_then .

(*

---------
Exercise 
---------

Define a 'new' function that takes as input a word, a definition, 
and returns dictionary containing this single word with its definition.

Test your function with the 'find' function and the 'Eval compute'
command as above.
*)
Fixpoint new word def : Dictionary :=
  match word with
  | EmptyString => Entry (Some def) Empty
  | String c rest => Entry None (Cons Empty c (new rest def))
  end.

Definition new_dict := new "example" "a representative form or pattern".
Eval compute in new_dict.

Eval compute in find "example" new_dict.
Eval compute in find "ex" new_dict. 

(*
---------
Exercise 
---------

Define an 'insert' function that takes as input a word, a definition, 
a dictionary, and returns a dictionary extending the previous one with the
new definition given as input.

*)

Fixpoint insert word def dictionary : Dictionary :=
  match word with
  | EmptyString => 
      match dictionary with
      | Entry _ listDict => Entry (Some def) listDict
      end
  | String c rest =>
      match dictionary with
      | Entry _ listDict => Entry None (insert_list c rest def listDict)
      end
  end
with insert_list c word def listDict : ListDictionary :=
  match listDict with
  | Empty => Cons Empty c (new word def)
  | Cons nextDict char' subDict =>
    if Ascii.eqb c char' then
      Cons nextDict char' (insert word def subDict)
    else
      Cons (insert_list c word def nextDict) char' subDict
  end.

Eval compute in new_dict.

Eval compute in  (insert "exotic" "unusual; far; warm" new_dict).

Eval compute in find "exotic" (insert "exotic" "unusual; far; warm" new_dict).

(* **************

Now we are going to prove that these functions are correct.

************  *)

(*
--------
Exercise
--------
*)
Lemma find_empty word :
  find word empty = None.
Proof.
  destruct word.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*
--------
Exercise
--------
*)
Lemma find_create def word :
  find word (new word def) = Some def.
Proof.
  induction word as [| c rest IH] => //=.
  - assert (H: c =c c = true).
    + unfold "=c". apply Ascii.eqb_eq. reflexivity.
    + rewrite H. rewrite <- IH. reflexivity.
Qed.


(*
--------
Exercise
--------
*)
Lemma find_create_unique def def' word word' :
  find word' (new word def) = Some def' ->
  def = def' /\ word = word'.
Proof.
move: word'.
induction word.
move => b a.
simpl in a.
destruct b.
split.
case: a.
exact.
reflexivity.
discriminate a.
simpl.
move => word' d.
destruct word'.
discriminate d.
move:d.
case: eqb_spec.
move => p k.
specialize (IHword _ k).
split.
by case: IHword.
rewrite p.
case: IHword.
move => u i.
rewrite i.
reflexivity.
move => u i.
discriminate i.
Qed.

(*
--------
Exercise
--------
*)
Corollary find_create_none def word word' : word <> word' ->
   find word' (new word def) = None.
Proof.
move => a.
destruct (find word' (new word def)) eqn:b.
specialize (find_create_unique _ _ _ _ b).
move => c.
case: c.
move => c d.
contradiction.
reflexivity.
Qed.


Scheme Dictionary_List_rec := Induction for Dictionary Sort Prop
  with ListDictionary_Dictionary_rec := Induction for ListDictionary Sort Prop.

Combined Scheme CombinedDictionary_rec from Dictionary_List_rec, ListDictionary_Dictionary_rec.
(*

The dictionary data structure comes with an induction principle called
Dictionary_List_rec.
When you want to prove a property P about dictionaries, you first need to define
a similar property P0 about list of dictionaries (ListDictionary) that you
will show by induction.

*)
Check Dictionary_List_rec.


Lemma find_add : forall dictionary def word,
   find word (insert word def dictionary) = Some def.
Proof. 
induction dictionary using Dictionary_List_rec with (P0 := fun l => l = l).
intros def word.
induction word.
simpl.
reflexivity.
simpl. (*Up to here its 98% good *)
induction l.
simpl.
rewrite (eqb_refl a).
apply find_create.
simpl.



(*
--------
Exercise
--------
*)
Lemma find_add' : forall dictionary def word word', word <> word' ->
   find word' (insert word def dictionary) = 
     find word' dictionary.
Proof.      
(* Again you will need to perform a mutual induction here  *)
Abort.



  
(* 

For some proofs, we will need to make explicit that the dictionnaries built
only through add have some canonicity: namely that in a ListDictionnary, a 
letter occurs at most once.

In other words, the following Dictionnary is not canonical because there are
two entries for the letter t at the same level

Definition twice_t : Dictionary :=
  Entry None
  (Cons  (Cons Empty "t"%char
               (Entry None (Cons Empty "h"%char 
                                 (Entry None
                                        (Cons Empty "e"%char
                                              (Entry (Some "definition of the")
                                                     Empty))))
               )
         ) "t"%char
         (Entry None
                (Cons Empty "o"%char
                      (Entry (Some "definition of to") Empty)))
  ).



*)


Fixpoint notoccur c l :=
  match l with
  | Empty => True
  | Cons l c' _ => ~(c =c c') /\ notoccur c l
  end.


(*
--------
Exercise
--------
*)
(* Possibly using notoccur, define the predicate specifying that such a situation like 
twice_t does not happen in a Dictionary (resp. a DictionaryList *)

(*Fixpoint canonical_l l :=
  match l with
    | Empty => True
    | Cons l c' d => notoccur c' l /\ canonical_l l
  end.

Definition canonical d :=
  match d with
    | Entry None listDict => canonical_l listDict
    | Entry (Some def) listDict => canonical_l listDict
  end.*)
 
Fixpoint canonical d : Prop :=
  match d with
    | Entry _ listDict => (canonical_l listDict)
  end
with
canonical_l (l : ListDictionary) : Prop :=
  match l with
    | Empty => True
    | Cons listDict c' d => notoccur c' listDict /\ (canonical_l listDict) /\ (canonical d)
  end.


(* Show a dictionary built by new is always canonical *)

Lemma new_canonical : forall w d, canonical (new w d).
Proof.
  - induction w.
    + simpl. reflexivity.
    + simpl. split. reflexivity.
      * split. reflexivity. apply IHw.
Qed.



(*
--------
Exercise
--------
*)
(* Now show that the canonical property is preserved by insert *)

Lemma insert_canonical : forall d w def, canonical d -> canonical (insert w def d).
Proof.
  induction d using 
Abort.


(*
--------
Exercise
--------
 *)
(* translate a list of definitions into a Dictionary *)
Fixpoint dict_from_list (l : list (string * string)) : Dictionary :=
  match l with
    | nil => empty
    | cons (w, d) l' => insert w d (dict_from_list l')
  end.


(* A quiz corresponds to a situation in the Hangman game, that is
a word of whom some letters are known, as well as its length. For instance 
  "hang_a_" of "h_n_m_a" *)
Definition quiz := list (option char).



(*
--------
Exercise
--------
*)
Definition string_to_quiz (s : string) : list (option char) :=
  List.map (fun c => if c =c "-" then None else Some c) 
  (list_ascii_of_string s).

Eval compute in (string_to_quiz "ab-").


(*
--------
Exercise
--------
*)

(* Define the property that a string (like "hagnman")
   fits a quiz (like h_ngman) *)

Fixpoint fits (s:string) (q:quiz) :=
  match s, q with
    | EmptyString, nil => True
    | String c s', nil => False
    | EmptyString, List.cons _ _ => False
    | String c s', List.cons None q' => fits s' q'
    | String c s', List.cons (Some c') q' => c =c c' /\ fits s' q'
  end.


Definition appString s c :=
  String.append s (String c "").

(*
--------
Exercise
--------
*)

(* Define a fuction enumerating all the words of a Dictionary which fit a given quiz *)

Definition enum (q : quiz)(d : Dictionary) : list string := ...

(* Important: you will not be able to define enum directly as a Fixpoint. 
   Instead, the recursive function will probably need some additional arguments. 
   You will then define enum as a particular case of the Fixpoint.

   One possibility may be to start with a recursive function of the following type:


Fixpoint enum_aux (q : quiz)(d : Dictionary)(found : list string)(cur : string) : list string :=
 ...
with
enum_l_aux  q o l found cur :=
  ...
.
*)

(* Test your function *)
Definition d1 :=
  insert "abo" "o" 
         (insert "aba" "a" (Entry None Empty)) .

Eval compute in (enum (cons None (cons (Some "c"%char) (cons (Some "o"%char) nil)))
                      d1).

Eval compute in (enum (cons None (cons (None) (cons (Some "a"%char) nil)))
                      d1).
Eval compute in (enum (cons (Some "a"%char) (cons (Some "b"%char) (cons None nil)))
                      d1).


Lemma string_app_nil :
  forall w, w++"" = w.
by elim => [//=| c w /= ->]. Qed.


Lemma string_app_app : forall a b c, appString a c ++ b = a ++ String c b.
elim => [//=|d a ha]//= b c.
by rewrite ha.
Qed.


Lemma notoccur_None :  forall l c w, notoccur c l -> find_list c w l = None.
induction l; simpl.
  done.
by move => c' w  ; case: eqb; simpl; case; auto. 
Qed.

(*
--------
Exercise
--------
*)
(* The two following lemmas state that the enum function is correct *)
(* The important step for you will be to state the generalized correction
   properties verified by your recursive functions (the enum_aux and 
   enum_l_aux functions; these will be the properties that can be shown
   by mutual induction *)

Lemma dic_enum_fit : forall d q w, canonical d -> 
    In w (enum q d) ->
    exists def, find w d = Some def /\ fits w q.
Proof.
Abort.

Lemma enum_complete : forall d q w, fits w q ->
                                    (exists def, find w d = Some def) ->
                                    In w (enum q d nil "").
Proof.
Abort.

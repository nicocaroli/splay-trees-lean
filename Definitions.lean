import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Aesop

universe u 

/--
  Inductive type for a splay tree, for this part it should be modeled as binary tree
  A tree can either be empty, or have two children (which may also be empty)
  A tree node contains a key and a node value
-/
inductive SplayTree (α : Type)
| empty: SplayTree α
| node (left : SplayTree α) (key : Nat) (value : α) (right : SplayTree α) : SplayTree α

namespace SplayTree

variable {α : Type}

/--
 Definition for size of a tree, the number of node
-/

def splay_tree_size : SplayTree α → Nat
| empty => 0
| (node A _ _ B) => 1 + splay_tree_size A + splay_tree_size B

/--
 Definition for size of a tree, the number of node
-/

def all_keys_set : SplayTree α → Set Nat
| empty => {}
| (node l k _ r) => Set.union (Set.insert k (all_keys_set l)) (all_keys_set r)

/-
  Checking if a key exists in a tree. This search does not change the data structure
-/
def is_key_in (x : Nat) : SplayTree α → Bool -- change name to element
| empty => false
| (node l k _ r) =>
  x = k ∨ is_key_in x l ∨ is_key_in x r

/--
  For all keys k in a tree, proposition p k k' is valid
-/
def forall_keys (p : Nat → Nat → Prop) (k : Nat) (t : SplayTree α) : Prop :=
  ∀ (k': Nat), is_key_in k' t → p k k'

/--
  Check if binary search property is fullfilled:
  For any node in a tree, its key must be smaller than all of the keys on the left subtree and
  larger than all of the keys on the right subtree.
-/
def bst_property : SplayTree α → Prop
| empty => True
| (node l k _ r) =>
  bst_property l ∧ bst_property r ∧ (forall_keys (. > .) k l) ∧ (forall_keys (. < .) k r)


/--
 Splaying: Termination is proved automatically by Lean 
-/
def splay (key : Nat) : SplayTree α → SplayTree α
| empty => empty
| t@(node AB k v CD) =>
  if  key = k then t
  else if key < k then
    match AB with
    | empty => t --key is not present, return t
    | (node A ab_key ab_value B) => 
      if key = ab_key then node A ab_key ab_value (node B k v CD) --right Rotation
      else if key < ab_key then 
      -- key should be in A, use recursively splay in A to get the key to the root of A
        match splay key A with
        | empty => node A ab_key ab_value (node B k v CD)
        | node Al a_key a_value Ar =>
        --The tree with A splayed looks like : (node (node (node Al a_key a_value Ar) ab_key ab_value B) k v CD)
        -- since key is now on the root of A: A_key is = key
        --Now rotate the tree to get the key to the root
        node Al a_key a_value (node Ar ab_key ab_value (node B k v CD))
      else --key > ab_key, meaning that the key should be in B, use recursively splay in B to get the key to the root of B
         match splay key B with
        | empty => node A ab_key ab_value (node B k v CD)
        | node Bl b_key b_value Br =>
        --The tree with B splayed looks like : (node (node A ab_key ab_value (Bl b_key b_value Br)) k v CD)
        node (node A ab_key ab_value Bl) b_key b_value (node Br k v CD)
  else
    match CD with
    | empty =>  t
    | (node C cd_key cd_value D) =>
     if key = cd_key then node (node AB k v C) cd_key cd_value D 
      else if key > cd_key then
        match splay key D with
        | empty => node (node AB k v C) cd_key cd_value D 
        | node D_l d_key d_value D_r =>
        --The tree with D splayed looks like : (node AB k v (node C cd_key cd_value (node D_l d_key d_value D_r)))
          node (node AB k v (node C cd_key cd_value  D_l)) d_key d_value D_r
      else
        match splay key C with
        | empty => node (node AB k v C) cd_key cd_value D 
        | node C_l c_key c_value C_r =>
        --The tree with C splayed looks like : (node AB k v (node (node C_l c_key c_value C_r) cd_key cd_value D))
          node (node AB k v  C_l) c_key c_value (node C_r cd_key cd_value D)


lemma splay_code : ∀ ( t : SplayTree α ) key , splay key t =
match t with
| empty => empty
| t@(node (node A ab_key ab_value B) k v empty) =>
   if key = k then t
    else
      if key < k then
        if key = ab_key then node A ab_key ab_value (node B k v empty)
        else
          if key < ab_key then
            match splay key A with
            | empty => node A ab_key ab_value (node B k v empty)
            | node Al a_key a_value Ar =>
              node Al a_key a_value (node Ar ab_key ab_value (node B k v empty))
          else 
            match splay key B with
            | empty => node A ab_key ab_value (node B k v empty)
            | node Bl b_key b_value Br =>
              node (node A ab_key ab_value Bl) b_key b_value (node Br k v empty)
      else node (node A ab_key ab_value B) k v empty
| t@(node AB@(node A ab_key ab_value B) k v CD@(node C cd_key cd_value D)) =>
    if key = k then t
    else
      if key < k then
        if key = ab_key then node A ab_key ab_value (node B k v CD)
        else
          if key < ab_key then 
          match splay key A with
          | empty => node A ab_key ab_value (node B k v CD)
          | node Al a_key a_value Ar =>
          node Al a_key a_value (node Ar ab_key ab_value (node B k v CD))
        else 
          match splay key B with
          | empty => node A ab_key ab_value (node B k v CD)
          | node Bl b_key b_value Br =>
          node (node A ab_key ab_value Bl) b_key b_value (node Br k v CD)
      else
        if key = cd_key then node (node (node A ab_key ab_value B) k v C) cd_key cd_value D
         else 
        if key > cd_key then
          match splay key D with --(node AB k v  C cd_key cd_value D_l) d_key d_value D_r
          | empty => node (node AB k v C) cd_key cd_value D 
          | node D_l d_key d_value D_r =>
            node (node AB k v (node C cd_key cd_value  D_l)) d_key d_value D_r
        else
          match splay key C with
          | empty => node (node AB k v C) cd_key cd_value D 
          | node C_l c_key c_value C_r =>
            node (node AB k v  C_l) c_key c_value (node C_r cd_key cd_value D)
| t@(node empty k v CD) =>
  if  key = k then t
  else if key < k then t
  else
    match CD with
    | empty => t
    | (node C cd_key cd_value D) =>
      if key = cd_key then node (node empty k v C) cd_key cd_value D 
      else 
        if key > cd_key then
          match splay key D with
          | empty => node (node empty k v C) cd_key cd_value D 
          | node D_l d_key d_value D_r =>
            node (node empty k v (node C cd_key cd_value  D_l)) d_key d_value D_r
        else
          match splay key C with
          | empty => node (node empty k v C) cd_key cd_value D 
          | node C_l c_key c_value C_r =>
            node (node empty k v  C_l) c_key c_value (node C_r cd_key cd_value D)
:= by 
  intros t key
  split; any_goals constructor
  rename_i CD; cases CD; all_goals constructor

/--
 Check if a key is in the root of a tree 
-/
def is_root (key : Nat) : SplayTree α → Bool 
| empty => false
| (node _ k _ _) => k = key

/--
 Check if a key is contained by the tree using splay
-/
def splayed_is_in (key : Nat) (t : SplayTree α) := is_root key (splay key t)

/--
  Lookup a value in a tree with splay
-/
def lookup (key : Nat) (t : SplayTree α) : Option α :=
match splay key t with
| empty => none
| (node _ k a _) =>
  if key = k then some a
  else none

/--
 Check if a tree is empty
-/ 
def isEmpty : SplayTree α → Bool
| empty => true
| _ => false

/--
 Insert a key and value in a splay Tree
-/ 
def insert (key : Nat) (value : α)(t: SplayTree α) : SplayTree α :=
  match splay key t with
  | empty => node empty key value empty
  | (node l k v r) =>
    if key = k then node l k v r 
    else if key < k then node l key value (node empty k v r)
    else node (node l k v empty) key value r

/--
 Definition for splaying a tree so that the right subtree is empty
-/
def splay_max: SplayTree α → SplayTree α
| empty => empty
| node l k v empty => node l k v empty
| node AB k v (node C cdk cdv D) =>
  match splay_max D with
  | empty => node (node AB k v C) cdk cdv empty
  | node Dr dk dv Dl => node (node (node AB k v C) cdk cdv Dr) dk dv Dl
/--
 Theorem to prove that using the funtion splay_max in an non empty tree cannot be empty
-/
theorem splay_max_code : ∀ ( t :SplayTree α ), splay_max t = 
  match t with
    | empty => t
    | (node al a av ar) =>
      match ar with
      | empty => t
      | (node lb b bv rb) =>
      if rb matches empty then node (node al a av lb) b  bv rb
      else
          match splay_max rb with
          | empty => node (node al a av lb) b  bv rb
          | node lc c cv  rc => node (node (node al a av lb) b bv lc) c cv rc 
  := by
    intros t
    have splay_max_emty_iff : ∀ ( t :SplayTree α ), splay_max  t = empty ↔ t = empty  := by unfold splay_max; aesop 
    repeat any_goals split
    any_goals constructor
    all_goals unfold splay_max; aesop (add norm simp splay_max)
/--
 Definition for joining two BST-trees t1 and t2 on a tree, assuming that x < y for all x in t1 and y in t2.
-/
def join (t1 : SplayTree α) (t2 : SplayTree α): SplayTree α :=
   match splay_max t1 with
    | empty => t2 -- l is empty
    | node l k v _ => node l k v t2 -- the right subtree is empty and therefore can r replace it


/--
 Definition for deleting a key on a tree
-/
def delete (key : Nat) (t : SplayTree α) : SplayTree α :=
  match splay key t with
  | empty => empty
  | node l k v r =>
    if key ≠ k  then node l k v r -- t does not contain key
    else join l r

/--
 Definition for spliting a BST-tree in two trees by the node key
-/
def split (key: Nat) (t : SplayTree α) : SplayTree α × SplayTree α :=
   match splay key t with
  | empty => (empty, empty)
  | node l k v r =>
    if k > key then (l, node empty k v r) else (node l k v empty, r)

end SplayTree
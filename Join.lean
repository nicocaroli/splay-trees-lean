import Splay

namespace JoinVerification

open ForallKeys
open SplayTree
open SplayVerification

@[simp] lemma splay_max_Leaf_iff : ∀ (t : SplayTree α), (splay_max t = empty) ↔ (t = empty) := by
  unfold splay_max
  aesop

lemma splay_max_forall_keys (x : Nat) (t : SplayTree α) (p : Nat → Nat → Prop) :
  forall_keys p x t → forall_keys p x (splay_max t) := by
    intros h
    unfold splay_max
    split
    . simp
    . assumption
    case h_3 A a av B b bv CD =>
      have h1 := splay_max_forall_keys x CD p
      aesop

lemma splay_max_bst_property (t : SplayTree α) (bst_property_t : bst_property t):
splay_max t = node ls ks vs rs →
(∀ k', is_key_in k' t ↔ (is_key_in k' ls ∨ k'= ks)) ∧ (bst_property ls ∧ forall_keys (.>.) ks ls) ∧ rs = empty := by
  unfold splay_max
  intros splay_match
  repeat any_goals split at splay_match
  . aesop
  . aesop (add norm simp [is_key_in, bst_property])
  . rename_i splay_empty ; simp at splay_empty; aesop (add norm simp [is_key_in, bst_property])
  . cases splay_match; rename_i AB k v B b bv CD _ _ splay_node;
    simp [bst_property] at bst_property_t
    have splay_max_bst_property_subtree := splay_max_bst_property CD bst_property_t.2.1.2.1 splay_node
    have splay_max_forall_keys_subtree := splay_max_forall_keys b CD (.<.)
    aesop (add norm simp [is_key_in, bst_property])


lemma join_bst_property (t1 t2 : SplayTree α) (bst_property_t1 : bst_property t1) (bst_property_t2 : bst_property t2)
 (t1_lt_t2:  ∀ (x y: Nat), (is_key_in x t1) ∧ (is_key_in y t2) →  x < y) :
  bst_property (join t1 t2) := by
  unfold join
  split
  . assumption
  . rename_i splay_max_node
    have h := splay_max_bst_property t1 bst_property_t1 splay_max_node
    simp_all [bst_property,forall_keys]

lemma join_keys (t1 t2 : SplayTree α) (bst_property_t1 : bst_property t1) (bst_property_t2 : bst_property t2) (key: Nat)
 (t1_lt_t2:  ∀ (x y: Nat),  (is_key_in x t1) ∧ (is_key_in y t2) →  x < y):
  is_key_in key (join t1 t2) ↔ (is_key_in key t1) ∨ (is_key_in key t2) := by
  unfold join
  split
  . rename_i splay_empty; rw [splay_max_Leaf_iff] at splay_empty; simp[splay_empty,is_key_in] 
  . rename_i splay_max_node
    have h := splay_max_bst_property t1 bst_property_t1 splay_max_node
    aesop (add norm [bst_property,forall_keys,is_key_in])
    
end JoinVerification
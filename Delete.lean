import Join

namespace DeleteVerification

open ForallKeys
open SplayTree
open SplayVerification
open JoinVerification

lemma join_assumption_proof :
forall_keys (fun x x_1 => x_1 < x) key ls ∧ forall_keys (fun x x_1 => x < x_1) key rs
→ ∀ (x y : ℕ), is_key_in x ls = true ∧ is_key_in y rs = true → x < y := by
    intros h x y is; simp_all[forall_keys]
    have h1:= h.1 x is.1
    have h2:= h.2 y is.2
    linarith

lemma delete_bst_property : ∀ (t : SplayTree α) key,
bst_property t → bst_property (delete key t)  := by
  intros t key bst_property_t
  unfold delete
  have splay_bst_property_t := splay_bst_property t key bst_property_t
  split
  . constructor
  . rename_i splay_node
    simp [splay_node] at splay_bst_property_t
    split
    . assumption
    . rename_i ls ks vs rs key_is; simp at key_is; cases key_is
      simp [bst_property] at splay_bst_property_t
      apply join_bst_property ls rs splay_bst_property_t.1 splay_bst_property_t.2.1 
      apply join_assumption_proof splay_bst_property_t.2.2
   
lemma delete_keys_presence : ∀ (t : SplayTree α) key,
bst_property t → ∀ k, (is_key_in k t → is_key_in k (delete key t) ∨ k = key) := by
  intros t key bst_property_t k'
  unfold delete
  have is_key_in_iff_splay_t := is_key_in_iff_splay k' key t
  have splay_bst_property_t := splay_bst_property t key bst_property_t
  split
  . aesop (add norm simp [is_key_in, bst_property])
  . rename_i splay_node
    simp [splay_node] at splay_bst_property_t
    split
    . aesop (add norm simp [is_key_in, bst_property])
    . rename_i ls ks vs rs key_is; simp at key_is; cases key_is
      have h:= join_keys ls rs splay_bst_property_t.1 splay_bst_property_t.2.1 k' (join_assumption_proof splay_bst_property_t.2.2)
      aesop (add norm simp [is_key_in, bst_property])

lemma delete_function : ∀ (t : SplayTree α) key,
bst_property t → is_key_in key (delete key t) = false := by
  intros t key bst_property_t
  unfold delete
  have splay_bst_property_t := splay_bst_property t key bst_property_t
  have is_in_splay_t := is_in_splay key t bst_property_t
  have is_key_in_iff_splay_t := is_key_in_iff_splay key key t
  split
  . constructor
  . rename_i l k v r splay_node
    simp [splayed_is_in, splay_node, is_root] at is_in_splay_t splay_bst_property_t is_key_in_iff_splay_t 
    split
    . by_contra; aesop
    . rename_i key_is; simp at key_is; cases key_is
      simp at is_in_splay_t
      simp [is_in_splay_t] at is_key_in_iff_splay_t
      simp [bst_property] at splay_bst_property_t
      have h:= join_keys l r splay_bst_property_t.1 splay_bst_property_t.2.1 key (join_assumption_proof splay_bst_property_t.2.2)
      by_contra c; simp_all [forall_keys];
      cases c
      . have h1 := splay_bst_property_t.2.2.1 key ; simp_all 
      . have h2 := splay_bst_property_t.2.2.2 key ; simp_all 
   
end DeleteVerification

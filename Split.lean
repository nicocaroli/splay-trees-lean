import Insert

namespace SplitVerification

open SplayVerification
open ForallKeys
open SplayTree
open InsertVerification

lemma split_bst_key_separation (t : SplayTree α) (key:Nat) (bst_property_t : bst_property t):
split key t = (t1, t2) → forall_keys (.>=.) key t1 ∧ forall_keys (.<=.) key t2 := by
  unfold split
  split
  . intros h; cases h; simp[bst_property]
  case h_2 ls ks vs rs splay_node =>
    have splay_left_rigth_t := splay_left_lt_right_gt t key bst_property_t splay_node
    split
    all_goals
      intros h'; cases h'
      simp [forall_keys, is_key_in] at splay_left_rigth_t ⊢;
    repeat any_goals constructor
    all_goals first
      | linarith
      | intros k' t1_is_in_key; have k'_lt_key_1 := splay_left_rigth_t.1 k' t1_is_in_key
        linarith
      | intros k' t1_is_in_key; have k'_lt_key_2 := splay_left_rigth_t.2 k' t1_is_in_key
        linarith

lemma split_bst_property (t : SplayTree α) (key:Nat) (bst_property_t : bst_property t) :
  split key t = (t1, t2) → bst_property t1 ∧ bst_property t2 := by
    unfold split 
    have h := splay_bst_property t key bst_property_t
    split <;> aesop (add norm bst_property)


lemma split_keys (t : SplayTree α) (key:Nat) (bst_property_t : bst_property t):
 split key t = (t1, t2) → (is_key_in key t ↔ (is_key_in key t1) ∨ (is_key_in key t2)) := by
  unfold split
  have h := is_key_in_iff_splay key key t
  aesop (add norm is_key_in)

end SplitVerification
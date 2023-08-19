import Splay

namespace LookupVerification

open SplayTree
open ForallKeys
open SplayVerification

/- If we lookup empty btree then return none -/
lemma lookup_empty (k : Nat) :
  lookup k (@SplayTree.empty α) = none := by rfl

lemma lookup_function (t : SplayTree α) (bst_property_t: bst_property t) :
 ∀ key, is_key_in key t = false ↔ lookup key t = none := by
  intro key
  have is_in_splay_t := is_in_splay key t bst_property_t
  unfold lookup
  split
  . rename_i splay_empty; simp [←splay_empty_iff] at splay_empty; cases splay_empty; simp [is_key_in]
  . rename_i splay_node; simp [splayed_is_in, splay_node, is_root] at is_in_splay_t; split
    . aesop
    . by_contra; aesop

end LookupVerification

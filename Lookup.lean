import Insert

namespace LookupVerification

open SplayTree
open ForallKeys
open SplayVerification
open InsertVerification

lemma lookup_empty (k : Nat) :
  lookup k (@SplayTree.empty α) = none := by rfl

lemma lookup_function (t : SplayTree α) (bst_property_t: bst_property t) :
 ∀ key, is_key_in key t = false ↔ lookup key t = none := by
  intro key
  have is_in_splay_t := is_in_splay key t bst_property_t
  unfold lookup
  by_contra ; aesop (add norm simp[splayed_is_in, is_root])

end LookupVerification

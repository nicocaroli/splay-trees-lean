import Definitions

namespace ForallKeys

open SplayTree

/- Lemma to prove the correctnes of is_key_in with Sets  -/
lemma is_key_in_correctness (t : SplayTree α)  (key : Nat) :
 key ∈ (all_keys_set t) ↔ is_key_in key t := by
  induction t
  . simp[is_key_in, all_keys_set]
  . simp [is_key_in, all_keys_set, Set.insert, Set.union]; aesop

@[simp] lemma is_key_in_empty (key : Nat) :
 is_key_in key (@SplayTree.empty α) = false := by rfl
@[simp] lemma forall_keys_empty (key : Nat)  (p : Nat → Nat → Prop):
 forall_keys p key (@SplayTree.empty α) = True := by simp [forall_keys]

/- Helper lemma to unfold forall_keys into two different children  -/
@[simp] lemma forall_keys_char (l r : SplayTree α) (k x : Nat) (v : α) (p : Nat → Nat → Prop) :
  forall_keys p k (node l x v r) ↔ (forall_keys p k l ∧ p k x ∧ forall_keys p k r):= by
  simp [forall_keys, is_key_in];
  aesop
/- Transivitity property for keys in a binary search tree -/
@[aesop unsafe 50% apply]
lemma forall_keys_trans (t : SplayTree α) (p : Nat → Nat → Prop) [p_trans : IsTrans Nat p ] (z x : Nat) (h₁ : p x z) :
  forall_keys p z t → forall_keys p x t := by
  unfold forall_keys
  have p_trans:= p_trans.trans
  aesop

end ForallKeys
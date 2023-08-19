import Splay

namespace InsertVerification

open SplayTree
open ForallKeys
open SplayVerification


theorem splay_left_lt_right_gt (t : SplayTree α) (key : Nat) 
(bst_property_t : bst_property t) (splay_match: splay key t = node ls ks vs rs) :
forall_keys (.>.) key ls ∧ forall_keys (.<.) key rs := by 
  cases t 
  . simp [splay] at splay_match
  case node AB k v CD =>
    cases AB
    . cases CD
      . simp [splay] at splay_match; simp[←splay_match]
      case node C cdk cdv D =>
        simp [splay] at splay_match
        simp[bst_property] at bst_property_t
        split at splay_match
        . rename_i key_is_k ; cases key_is_k; cases splay_match; simp [ bst_property_t]
        . split  at splay_match
          . rename_i key_lt_k;
            cases splay_match;
            apply And.intro
            . simp
            . apply(forall_keys_trans (node C cdk cdv D) (.<.) ks key key_lt_k); simp [ bst_property_t]
          . rename_i key_not_k key_ge_k; simp at key_ge_k
            have s := Nat.lt_or_eq_of_le key_ge_k
            have key_gt_k : k < key := by cases s; assumption; aesop
            split at splay_match
            . rename_i key_is_cdk ; cases key_is_cdk; cases splay_match; simp [ bst_property_t]
            . split at splay_match
              . rename_i cdk_lt_key; split at splay_match
                . rename_i splay_empty; cases splay_match; simp [←splay_empty_iff] at splay_empty; cases splay_empty;  simp [ bst_property_t]
                  aesop
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt D key bst_property_t.1.2.1 splay_d
                  simp [splay_d,  bst_property_t,induction_d]
                  aesop
              . rename_i key_not_cdk cdk_le_key; simp at * ; 
                have cdk_gt_key := Nat.lt_or_eq_of_le cdk_le_key
                simp [key_not_cdk] at cdk_gt_key
                split at splay_match
                . rename_i splay_empty; simp [←splay_empty_iff] at splay_empty; cases splay_empty; cases splay_match; simp [ bst_property_t]
                  aesop
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt C key bst_property_t.1.1 splay_d
                  aesop
    case node A abk abv B =>
      cases CD
      . simp [splay] at splay_match
        simp[bst_property] at bst_property_t
        split at splay_match
        . rename_i key_is_k ; cases key_is_k; cases splay_match; simp [ bst_property_t]
        . split  at splay_match
          . rename_i key_lt_k;
            split at splay_match
            . rename_i key_is_k ; cases key_is_k; cases splay_match; simp [ bst_property_t]
            . split at splay_match
              . rename_i key_lt_abk; split at splay_match
                . rename_i splay_empty; simp [←splay_empty_iff] at splay_empty; cases splay_empty; cases splay_match; simp [ bst_property_t]
                  repeat any_goals apply And.intro
                  all_goals first 
                    | linarith 
                    | apply(forall_keys_trans B (.<.) ks key key_lt_abk); simp[bst_property_t]
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt A key bst_property_t.1.1 splay_d
                  simp [splay_d,  bst_property_t, induction_d]
                  repeat any_goals apply And.intro
                  . linarith
                  . apply (forall_keys_trans B (.<.) abk key key_lt_abk); simp[bst_property_t]
                  . linarith
              . rename_i key_not_abk abk_le_key; simp at * ; 
                have s := Nat.lt_or_eq_of_le abk_le_key
                have abk_lt_key : abk < key := by cases s; assumption; aesop
                split at splay_match
                . rename_i splay_empty; simp [←splay_empty_iff] at splay_empty; cases splay_empty; cases splay_match; simp [ bst_property_t]
                  repeat any_goals apply And.intro
                  all_goals first 
                    | linarith 
                    | apply(forall_keys_trans ls (.>.) ks key abk_lt_key); simp[bst_property_t]
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt B key bst_property_t.1.2.1 splay_d
                  simp [splay_d,  bst_property_t,induction_d]
                  repeat any_goals apply And.intro
                  . apply(forall_keys_trans A (.>.) abk key abk_lt_key); simp [bst_property_t]
                  . linarith
                  . linarith
          . rename_i key_not_k key_ge_k; simp at key_ge_k
            have s := Nat.lt_or_eq_of_le key_ge_k
            have k_lt_key : k < key := by cases s; assumption; aesop
            cases splay_match;
            apply And.intro
            . apply(forall_keys_trans (node A abk abv B) (.>.) ks key k_lt_key); simp [ bst_property_t]
            . simp

      case node C cdk cdv D =>
        simp [splay] at splay_match
        simp[bst_property] at bst_property_t; 
        split at splay_match
        . rename_i key_is_k; cases key_is_k
          cases splay_match;simp [bst_property_t]
        . split  at splay_match
          . rename_i key_lt_k;
            split at splay_match
            . rename_i key_is_abk ; cases key_is_abk; cases splay_match; rw [forall_keys_char]; simp [bst_property_t, -forall_keys_char]
              apply (forall_keys_trans (node C cdk cdv D) (.<.) k ks key_lt_k); simp [bst_property_t]
            . split at splay_match
              . rename_i key_lt_abk; split at splay_match
                . rename_i splay_empty; simp [←splay_empty_iff] at splay_empty; cases splay_empty; cases splay_match; rw [forall_keys_char]; simp [bst_property_t,-forall_keys_char]
                  repeat any_goals apply And.intro
                  . apply(forall_keys_trans B (.<.) ks key key_lt_abk); simp[bst_property_t]
                  . linarith
                  . apply (forall_keys_trans (node C cdk cdv D) (.<.) k key key_lt_k); simp [bst_property_t]
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt A key bst_property_t.1.1 splay_d
                  rw [forall_keys_char]; rw [forall_keys_char]; simp [induction_d, bst_property_t, -forall_keys_char]
                  repeat any_goals apply And.intro
                  . linarith
                  . apply (forall_keys_trans B (.<.) abk key key_lt_abk); simp[bst_property_t]
                  . linarith
                  . apply (forall_keys_trans (node C cdk cdv D) (.<.) k key key_lt_k); simp [ bst_property_t]
              . rename_i key_not_abk abk_le_key; simp at * ; 
                have s := Nat.lt_or_eq_of_le abk_le_key
                have abk_lt_key : abk < key := by cases s; assumption; aesop
                split at splay_match
                . rename_i splay_empty; simp [←splay_empty_iff] at splay_empty; cases splay_empty; cases splay_match; rw [forall_keys_char]; simp [bst_property_t,-forall_keys_char]
                  repeat any_goals apply And.intro
                  . apply(forall_keys_trans ls (.>.) ks key abk_lt_key); simp[bst_property_t]
                  . linarith
                  . apply (forall_keys_trans (node C cdk cdv D) (.<.) k key key_lt_k); simp [ bst_property_t]
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt B key bst_property_t.1.2.1 splay_d
                  rw [forall_keys_char]; rw [forall_keys_char]; simp  [induction_d,bst_property_t,-forall_keys_char]
                  repeat any_goals apply And.intro
                  . apply(forall_keys_trans A (.>.) abk key abk_lt_key); simp [bst_property_t]
                  . linarith
                  . linarith
                  . apply (forall_keys_trans (node C cdk cdv D) (.<.) k key key_lt_k); simp [ bst_property_t]
          . rename_i key_not_k key_ge_k; simp at key_ge_k
            have s := Nat.lt_or_eq_of_le key_ge_k
            have k_lt_key : k < key := by cases s; assumption; aesop
            have key_gt_AB : forall_keys  (.>.) key (node A abk abv B) := by
              apply(forall_keys_trans (node A abk abv B) (.>.) k key k_lt_key); simp [ bst_property_t]
            split at splay_match
            . rename_i key_is_cdk ; cases key_is_cdk; cases splay_match; rw [forall_keys_char]; simp [bst_property_t, key_gt_AB,-forall_keys_char]
            . split at splay_match
              . rename_i cdk_lt_key; split at splay_match
                . aesop
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt D key bst_property_t.2.1.2.1 splay_d
                  simp at key_gt_AB; simp [*]
                  apply(forall_keys_trans C (.>.) cdk key cdk_lt_key); simp[bst_property_t]
              . rename_i key_not_cdk cdk_le_key; simp at * ; 
                have cdk_gt_key := Nat.lt_or_eq_of_le cdk_le_key
                simp [key_not_cdk] at cdk_gt_key
                split at splay_match
                . aesop
                . rename_i dl dk dv dr splay_d; cases splay_match;
                  have induction_d := splay_left_lt_right_gt C key bst_property_t.2.1.1 splay_d
                  simp at key_gt_AB; simp [*]
                  apply(forall_keys_trans D (.<.) cdk key cdk_gt_key); simp [bst_property_t]

lemma insert_bst_property : ∀ (t : SplayTree α) key value,
bst_property t → bst_property (insert key value t) := by
  intros t key value bst_property_t
  have bst_property_splay_t := splay_bst_property t key bst_property_t
  unfold SplayTree.insert
  split 
  . simp[bst_property]
  case h_2 ls ks vs rs splay_match => 
      simp [splay_match,bst_property] at bst_property_splay_t;
      have splay_left_rigth_t := splay_left_lt_right_gt t key bst_property_t splay_match
      repeat any_goals split
      all_goals simp[bst_property,splay_left_rigth_t, bst_property_splay_t];
      repeat any_goals apply And.intro
      any_goals linarith
      rename_i key_not_k key_ge_k; simp at key_ge_k
      have cdk_gt_key := Nat.lt_or_eq_of_le key_ge_k
      by_contra; simp_all 


lemma insert_keys_presence (t : SplayTree α) (key: Nat) (value: α)(bst_property_t: bst_property t) :
 ∀ k, is_key_in k t ∨ k = key ↔ is_key_in k (insert key value t) := by
  intro k'
  have is_in_splay_t := is_in_splay key t bst_property_t
  have is_key_in_iff_splay_t := is_key_in_iff_splay k' key t
  unfold SplayTree.insert
  split 
  . simp[is_key_in] at *; aesop
  case h_2 ls ks vs rs splay_match => 
    aesop (add norm simp [is_key_in, is_root])

lemma is_root_insert (key : Nat) (value: α) (t : SplayTree α) (bst_property_t : bst_property t) :
is_root key (insert key value t) := by
  have is_in_splay_t := is_in_splay key t bst_property_t
  unfold SplayTree.insert
  simp [is_key_in, splayed_is_in] at *
  aesop (add norm simp is_root)

end InsertVerification


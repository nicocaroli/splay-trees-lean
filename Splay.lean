import ForallKeys

namespace SplayVerification

open ForallKeys
open SplayTree

@[simp] lemma bst_property_empty (key : Nat)  (p : Nat → Nat → Prop):
 bst_property (@SplayTree.empty α) = True := by rfl

@[simp] lemma splay_empty_iff : ∀ (t : SplayTree α) key,
(splay key t = empty) ↔ (t = empty) := by
  intros t k; rw [splay_code]; aesop

set_option maxHeartbeats 0
lemma is_key_in_iff_splay (elem key : Nat) (t : SplayTree α) :
  is_key_in elem (splay key t) ↔ is_key_in elem t := by
    cases t 
    . rfl
    case node AB k v CD =>
      cases AB
      . cases CD
        . simp [splay]
        case node C cdk cdv D =>
          have is_key_in_splay_D := is_key_in_iff_splay elem key D
          have is_key_in_splay_C := is_key_in_iff_splay elem key C
          simp[splay]
          aesop (add norm simp is_key_in)
      case node A abk abv B =>
        have is_key_in_splay_A := is_key_in_iff_splay elem key A
        have is_key_in_splay_B := is_key_in_iff_splay elem key B
        cases CD
        . simp[splay]
          aesop (add norm simp is_key_in)
        case node C cdk cdv D =>
          have is_key_in_splay_D := is_key_in_iff_splay elem key D
          have is_key_in_splay_C := is_key_in_iff_splay elem key C
          simp [splay]; 
          aesop (add norm simp is_key_in)

lemma forall_keys_splay (key x : Nat) (t : SplayTree α) (p : Nat → Nat → Prop) :
  forall_keys p x t → forall_keys p x (splay key t) := by
  intros h_keys
  cases t 
  . simp [splay]
  case node AB k v CD =>
    cases AB
    . simp at h_keys; cases CD
      . simp [splay, h_keys]
      case node C cdk cdv D =>
        have forall_D := forall_keys_splay key x D p
        have forall_C := forall_keys_splay key x C p
        simp [splay]; aesop?
    case node A abk abv B =>
      have forall_A := forall_keys_splay key x A p
      have forall_B := forall_keys_splay key x B p
      cases CD
      . simp [splay]
        aesop 
      case node C cdk cdv D =>
        have forall_C := forall_keys_splay key x C p
        have forall_D := forall_keys_splay key x D p
        simp [splay]; aesop
        

theorem splay_bst_property : ∀ (t : SplayTree α) key,
bst_property t → bst_property (splay key t) := by
  intros t key_i
  cases t 
  . simp [splay, bst_property];
  case  node AB k v CD =>
    intro h
    simp [bst_property] at h
    unfold bst_property
    split
    . simp
    case h_2 lS keyS valueS rS h' =>
      cases AB
      . cases CD
        simp [splay] at h'; aesop
        case node C cd_key cdv D => 
          simp [splay] at h'
          repeat (any_goals (split at h'))
          all_goals (cases h'; simp [bst_property] at h; simp [bst_property, h])
          . rename_i splay_match
            have splay_D_bst_property := splay_bst_property D key_i
            have splay_D_forall_keys_cd_key := forall_keys_splay key_i cd_key  D (.<.)
            have splay_D_forall_keys_k := forall_keys_splay key_i k D (.<.)
            aesop
          . rename_i splay_match
            have splay_C_bst_property := splay_bst_property C key_i
            have splay_C_forall_keys_cd_key := forall_keys_splay key_i cd_key C (.>.)
            have splay_C_forall_keys_k := forall_keys_splay key_i k C (.<.)
            aesop
      case node A abk abv B =>
        cases CD
        . simp [splay] at h'; split at h'
          . cases h'; simp only [h]
          case inr => --case key_i not key_1
            split at h'
            case inl key_i_lt => --key_i < key_1
              split at h'
              case inl key_eq => --key_i = key_2
                cases h'
                simp [bst_property] at h
                simp [ bst_property, h]
              case inr =>
                split at h'
                case inl key_i_lt_key_2=>
                  split at h'
                  case h_1 splay_A_empty =>
                    cases h'
                    simp [bst_property] at h
                    simp [bst_property, h]
                  case h_2 Al ak av Ar splay_A_node =>
                    cases h'
                    simp [bst_property] at h
                    have splay_A_bst_property := splay_bst_property A key_i
                    simp[h,splay_A_node, bst_property] at splay_A_bst_property
                    have splay_A_forall_keys := forall_keys_splay key_i abk A (.>.) h.1.2.2.1
                    simp [splay_A_node] at splay_A_forall_keys
                    simp[bst_property,splay_A_bst_property, h ,splay_A_forall_keys]
                    have keyS_lt_k: keyS < k := by linarith
                    have keyS_gt_B := forall_keys_trans B (.<.) abk keyS  splay_A_forall_keys.2.1 h.1.2.2.2
                    simp[keyS_lt_k, keyS_gt_B]
                case inr =>
                  split at h'
                  case h_1 =>
                    cases h'
                    simp [bst_property] at h
                    simp [ bst_property, h]
                  case h_2 Bl ak av Br splay_B_node =>
                    cases h'
                    simp [bst_property] at h
                    have splay_B_bst_property := splay_bst_property B key_i
                    simp[h, splay_B_node, bst_property] at splay_B_bst_property
                    have splay_B_forall_keys := forall_keys_splay key_i abk B (.<.) h.1.2.2.2
                    have splay_B_forall_keys_k := forall_keys_splay key_i k B (.>.) h.2.2.2 
                    simp [splay_B_node] at splay_B_forall_keys splay_B_forall_keys_k
                    simp[bst_property,splay_B_bst_property, h, splay_B_forall_keys_k, splay_B_forall_keys]
                    apply forall_keys_trans A (.>.) abk keyS splay_B_forall_keys.2.1; simp [h]
            case inr =>
              cases h'
              simp [bst_property] at h
              simp [ bst_property, h]
        case node C cdk cdv D =>  
          simp[splay] at h'
          simp [bst_property] at h
          have splay_A_bst_property := splay_bst_property A key_i
          have splay_B_bst_property := splay_bst_property B key_i
          have splay_C_bst_property := splay_bst_property C key_i
          have splay_D_bst_property := splay_bst_property D key_i
          have splay_A_forall_keys := forall_keys_splay key_i abk A (.>.)
          have splay_B_forall_keys := forall_keys_splay key_i abk B (.<.)
          have splay_B_forall_keys_k := forall_keys_splay key_i k B (.>.)
          have splay_C_forall_keys := forall_keys_splay key_i k C (.<.)
          have splay_C_forall_keys_cd_key := forall_keys_splay key_i cdk C (.>.)
          have splay_D_forall_keys_k := forall_keys_splay key_i k D (.<.)
          have splay_D_forall_keys_cd_key := forall_keys_splay key_i cdk  D (.<.)
          simp [h] at splay_A_bst_property  splay_B_bst_property splay_C_forall_keys_cd_key splay_B_forall_keys_k splay_C_bst_property splay_D_bst_property splay_A_forall_keys splay_B_forall_keys splay_C_forall_keys splay_D_forall_keys_k splay_D_forall_keys_cd_key
          repeat (any_goals (split at h'))
          all_goals (cases h')
          all_goals (try (rename_i splay_match; simp [splay_match] at *))
          all_goals (simp [bst_property] at *; simp [*])
          repeat any_goals (apply And.intro)
          all_goals (try linarith)
          all_goals aesop

                  
set_option maxHeartbeats 300000

lemma is_in_splay (key : Nat) (t : SplayTree α) (bst_property_t : bst_property t) :
is_key_in key t ↔ splayed_is_in key t := by
  unfold splayed_is_in
  unfold is_root
  cases t
  . simp [is_key_in, splay]
  case node AB k v CD => 
    split
    . rename_i splay_match; simp at splay_match;
    . rename_i splay_match
      cases AB
      . cases CD
        . simp [splay] at splay_match; simp [is_key_in]; aesop
        case node C cdk cdv D =>
          simp [splay] at splay_match
          simp only [bst_property] at bst_property_t
          split at splay_match
          . simp[is_key_in] ; aesop
          . split at splay_match
            . rename_i key_lt_k
              cases splay_match
              have key_not_in_CD : ¬is_key_in key (node C cdk cdv D) := by
                by_contra con
                have h' := forall_keys_trans (node C cdk cdv D) (.<.) k key key_lt_k 
                simp only [bst_property_t] at h'; simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              simp [is_key_in] at key_not_in_CD ⊢; aesop
            . split at splay_match
              . simp [is_key_in]; aesop
              . have is_in_splay_C := is_in_splay key C
                have is_in_splay_D := is_in_splay key D
                simp[bst_property] at bst_property_t
                simp [splayed_is_in,bst_property_t, is_root] at is_in_splay_C is_in_splay_D
                simp[is_key_in]
                split at splay_match
                . rename_i key_gt_cdk
                  have key_not_in_C : ¬is_key_in key C := by
                    by_contra con
                    have h' : forall_keys (.>.) key C := by aesop
                    simp [bst_property_t] at h'; simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
                . rename_i key_not_cdk cdk_le_key
                  simp at cdk_le_key
                  have cdk_gt_key := Nat.lt_or_eq_of_le cdk_le_key
                  simp [key_not_cdk] at cdk_gt_key
                  have key_not_in_D : ¬is_key_in key D := by
                    by_contra con
                    have h' : forall_keys (.<.) key D := by
                      apply forall_keys_trans D (.<.) cdk key cdk_gt_key; simp [bst_property_t]
                    simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
      case node A abk abv B =>
        cases CD
        . simp [splay] at splay_match; 
          have is_in_splay_A := is_in_splay key A
          have is_in_splay_B := is_in_splay key B
          simp[bst_property] at bst_property_t
          simp [splayed_is_in,bst_property_t, is_root] at is_in_splay_A is_in_splay_B
          simp[is_key_in]
          split at splay_match
          . aesop
          . split at splay_match
            . rename_i key_lt_k
              split at splay_match
              . cases splay_match; simp [*]
              . split at splay_match
                . rename_i key_lt_abk
                  have key_not_in_B : ¬is_key_in key B := by
                    by_contra con
                    have h' := forall_keys_trans B (.<.) abk key key_lt_abk 
                    simp [bst_property_t] at h'; simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
                . rename_i key_not_abk abk_le_key
                  simp at abk_le_key
                  have s := Nat.lt_or_eq_of_le abk_le_key
                  have key_not_in_A : ¬is_key_in key A := by
                    by_contra con
                    have abk_lt_key : abk < key := by cases s; assumption; aesop
                    have h' : forall_keys (·>·) key A := by
                      apply forall_keys_trans A (·>·) abk key abk_lt_key; simp [bst_property_t]
                    simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
            . simp [splay] at splay_match; rename_i key_not_k k_le_key
              simp at k_le_key
              have s := Nat.lt_or_eq_of_le k_le_key
              have k_lt_key : k < key := by cases s; assumption; aesop
              have key_not_in_A : ¬is_key_in key A := by
                by_contra con
                have h' : forall_keys (.>.) key A := by
                  apply forall_keys_trans A (.>.) k key k_lt_key; simp [bst_property_t]
                simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              have key_not_in_B : ¬is_key_in key B := by
                by_contra con
                have h' : forall_keys (fun x x_1 => x_1 < x) key B := by
                  apply forall_keys_trans B (.>.) k key k_lt_key; simp [bst_property_t]
                simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              cases splay_match
              have key_not_abk : ¬key = abk := by linarith
              aesop

        case node C cdk cdv D =>
          simp [splay] at splay_match;    
          have is_in_splay_A := is_in_splay key A
          have is_in_splay_B := is_in_splay key B
          have is_in_splay_C := is_in_splay key C
          have is_in_splay_D := is_in_splay key D
          simp[bst_property] at bst_property_t
          simp [splayed_is_in, bst_property_t, is_root] at is_in_splay_A  is_in_splay_B is_in_splay_C is_in_splay_D
          simp [is_key_in]
          split at splay_match
          . aesop
          . split at splay_match
            . rename_i key_lt_k
              have key_not_in_C : ¬is_key_in key C := by
                by_contra con
                have h' := forall_keys_trans C (.<.) k key key_lt_k 
                simp [bst_property_t] at h'; simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              have key_not_in_D : ¬is_key_in key D := by
                by_contra con
                have h' := forall_keys_trans D (.<.) k key key_lt_k 
                simp [bst_property_t] at h'; simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              have key_not_cdk : ¬key = cdk := by linarith
              split at splay_match
              . aesop
              . split at splay_match
                . rename_i key_lt_abk
                  have key_not_in_B : ¬is_key_in key B := by
                    by_contra con
                    have h' := forall_keys_trans B (.<.) abk key key_lt_abk 
                    simp [bst_property_t] at h'; simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
                . rename_i key_not_abk abk_le_key
                  simp at abk_le_key
                  have s := Nat.lt_or_eq_of_le abk_le_key
                  have key_not_in_A : ¬is_key_in key A := by
                    by_contra con
                    have abk_lt_key : abk < key := by cases s; assumption; aesop
                    have h' : forall_keys (fun x x_1 => x_1 < x) key A := by
                      apply forall_keys_trans A (.>.) abk key abk_lt_key; simp [bst_property_t]
                    simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
            . rename_i key_not_k k_le_key
              simp at k_le_key
              have s := Nat.lt_or_eq_of_le k_le_key
              have k_lt_key : k < key := by cases s; assumption; aesop
              have key_not_in_A : ¬is_key_in key A := by
                by_contra con
                have h' : forall_keys (fun x x_1 => x_1 < x) key A := by
                  apply forall_keys_trans A (.>.) k key k_lt_key; simp [bst_property_t]
                simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              have key_not_in_B : ¬is_key_in key B := by
                by_contra con
                have h' : forall_keys (fun x x_1 => x_1 < x) key B := by
                  apply forall_keys_trans B (.>.) k key k_lt_key; simp [bst_property_t]
                simp [forall_keys] at h'                  
                have h1 := h' key con; simp at h1
              have key_not_abk : ¬key = abk := by linarith
              split at splay_match
              . cases splay_match; simp [*]
              . split at splay_match
                . rename_i key_gt_cdk
                  have key_not_in_C : ¬is_key_in key C := by
                    by_contra con
                    have h' : forall_keys (.>.) key C := by
                      apply forall_keys_trans C (.>.) cdk key key_gt_cdk; simp [bst_property_t]
                    simp [bst_property_t] at h'; simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop
                . rename_i key_not_cdk cdk_le_key
                  simp at cdk_le_key
                  have cdk_gt_key := Nat.lt_or_eq_of_le cdk_le_key
                  simp [key_not_cdk] at cdk_gt_key
                  have key_not_in_D : ¬is_key_in key D := by
                    by_contra con
                    have h' : forall_keys (.<.) key D := by
                      apply forall_keys_trans D (.<.) cdk key cdk_gt_key; simp [bst_property_t]
                    simp [forall_keys] at h'                  
                    have h1 := h' key con; simp at h1
                  aesop

theorem splay_to_root (key : Nat) (t: SplayTree α) (splay_match : splay key t = node ls ks vs rs) (bst_property_t : bst_property t) :
is_key_in key t ↔ key = ks := by
  have h := is_in_splay key t  bst_property_t
  simp [is_root , splayed_is_in, splay_match] at h
  simp [h]; tauto


end SplayVerification


theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

(* ================================================================= *)
(* PART 1: ought defined first, opaques via ought                    *)
(* ================================================================= *)

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case => bool" where
  "should_known c = (c = Known_Should)"

definition should_to_be_found :: "knowledge_case => bool" where
  "should_to_be_found c = (~ should_known c)"

(* "The thing you know is the ought." So ought c holds iff either  *)
(* the ought is known, or the ought is still to be found.          *)
definition ought :: "knowledge_case => bool" where
  "ought c = (should_known c | should_to_be_found c)"

theorem should_status_exhaustive:
  "!c. should_known c | should_to_be_found c"
  unfolding should_known_def should_to_be_found_def by blast

lemma ought_always: "ought c"
  unfolding ought_def using should_status_exhaustive by simp

lemma should_to_be_found_no_known: "should_to_be_found No_Known_Should"
  unfolding should_to_be_found_def should_known_def by simp

(* ================================================================= *)
(* PART 2: syntactic layer and eval                                  *)
(* ================================================================= *)

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form

primrec eval :: "syn_form => bool" where
  "eval (Is_Case c)      = True"
| "eval (Ought_Target c) = ought c"
| "eval (Not A)          = (~ eval A)"
| "eval (Imp A C)        = (eval A --> eval C)"

(* ================================================================= *)
(* PART 3: Hilbert calculus, WITH reflection rule                    *)
(* ================================================================= *)

(* Reflection: from factual should_to_be_found c, derive Ought_Target c.
   This is what makes the bridge DERIVABLE rather than DEFINED. *)
inductive provable :: "syn_form set => syn_form set => syn_form => bool"
  ("_ ; _ |- _" [50, 50, 50] 50) where
  ax_base:    "A : B ==> B ; Gamma |- A"
| ax_assm:    "A : Gamma ==> B ; Gamma |- A"
| ax_k:       "B ; Gamma |- Imp A (Imp C A)"
| ax_s:       "B ; Gamma |- Imp (Imp A (Imp C D)) (Imp (Imp A C) (Imp A D))"
| ax_neg:     "B ; Gamma |- Imp (Imp (Not A) (Not C)) (Imp C A)"
| mp:         "B ; Gamma |- Imp A C ==> B ; Gamma |- A ==> B ; Gamma |- C"
| ax_reflect: "should_to_be_found c ==> B ; Gamma |- Ought_Target c"

lemma provable_sound:
  assumes deriv: "B ; Gamma |- psi"
      and base_true: "!beta : B. eval beta"
      and prem_true: "!phi : Gamma. eval phi"
  shows "eval psi"
  using deriv base_true prem_true
proof (induction rule: provable.induct)
  case (ax_base A B Gamma)
  then show ?case using base_true by blast
next
  case (ax_assm A B Gamma)
  then show ?case using prem_true by blast
next
  case (ax_k B Gamma A C)
  then show ?case by simp
next
  case (ax_s B Gamma A C D)
  then show ?case by simp
next
  case (ax_neg B Gamma A C)
  then show ?case by auto
next
  case (mp B Gamma A C)
  from mp.IH(1) have ih1: "eval (Imp A C)" using mp.prems by blast
  from mp.IH(2) have ih2: "eval A" using mp.prems by blast
  show "eval C" using ih1 ih2 by simp
next
  case (ax_reflect B Gamma c)
  then show ?case by (simp add: ought_always)
qed

(* ================================================================= *)
(* PART 4: audit_bridge is DERIVED, not assumed                      *)
(* ================================================================= *)

definition audit_bridge :: syn_form where
  "audit_bridge = Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"

lemma audit_bridge_provable:
  "B ; Gamma |- audit_bridge"
proof -
  have h_refl: "B ; Gamma |- Ought_Target No_Known_Should"
    by (rule provable.ax_reflect[OF should_to_be_found_no_known])
  have h_k: "B ; Gamma
               |- Imp (Ought_Target No_Known_Should)
                     (Imp (Is_Case No_Known_Should)
                          (Ought_Target No_Known_Should))"
    by (rule provable.ax_k)
  show ?thesis
    unfolding audit_bridge_def
    by (rule provable.mp[OF h_k h_refl])
qed

lemma audit_bridge_true: "eval audit_bridge"
  unfolding audit_bridge_def by (simp add: ought_always)

(* ================================================================= *)
(* PART 5: Pigden substitution                                      *)
(* ================================================================= *)

primrec subst_ought :: "(knowledge_case => syn_form) => syn_form => syn_form" where
  "subst_ought R (Is_Case c)      = Is_Case c"
| "subst_ought R (Ought_Target c) = R c"
| "subst_ought R (Not A)          = Not (subst_ought R A)"
| "subst_ought R (Imp A C)        = Imp (subst_ought R A) (subst_ought R C)"

definition R_pigden :: "knowledge_case => syn_form" where
  "R_pigden = (%_. Not (Ought_Target No_Known_Should))"

lemma subst_bridge_eq:
  "subst_ought R_pigden audit_bridge
     = Imp (Is_Case No_Known_Should) (Not (Ought_Target No_Known_Should))"
  unfolding audit_bridge_def R_pigden_def by simp

lemma subst_bridge_false:
  "~ eval (subst_ought R_pigden audit_bridge)"
  unfolding subst_bridge_eq by (simp add: ought_always)

(* ================================================================= *)
(* PART 6: the Pigden closure is FALSE -- this is the real result    *)
(* ================================================================= *)

theorem closure_is_false:
  "~ ({audit_bridge} ; {Is_Case No_Known_Should}
       |- subst_ought R_pigden audit_bridge)"
proof
  assume h: "{audit_bridge} ; {Is_Case No_Known_Should}
               |- subst_ought R_pigden audit_bridge"
  have base_t: "!beta : {audit_bridge}. eval beta"
    using audit_bridge_true by simp
  have prem_t: "!phi : {Is_Case No_Known_Should}. eval phi"
    by simp
  have h_sound: "eval (subst_ought R_pigden audit_bridge)"
    using provable_sound[OF h base_t prem_t] .
  from h_sound subst_bridge_false show False by simp
qed

(* ================================================================= *)
(* PART 7: the user's original theorem, but with closure as         *)
(* an explicit hypothesis -- this is what is actually provable       *)
(* ================================================================= *)

theorem definitional_collision:
  assumes closure: "{audit_bridge} ; {Is_Case No_Known_Should}
                     |- subst_ought R_pigden audit_bridge"
  shows False
proof -
  have h_b: "{audit_bridge} ; {Is_Case No_Known_Should} |- audit_bridge"
    by (rule provable.ax_base) simp
  have h_exp:
    "{audit_bridge} ; {Is_Case No_Known_Should}
       |- Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"
    using h_b unfolding audit_bridge_def .
  have h_p: "{audit_bridge} ; {Is_Case No_Known_Should}
               |- Is_Case No_Known_Should"
    by (rule provable.ax_assm) simp
  have h_ought: "{audit_bridge} ; {Is_Case No_Known_Should}
                   |- Ought_Target No_Known_Should"
    by (rule provable.mp[OF h_exp h_p])
  have h_subst:
    "{audit_bridge} ; {Is_Case No_Known_Should}
       |- Imp (Is_Case No_Known_Should) (Not (Ought_Target No_Known_Should))"
    using closure subst_bridge_eq by simp
  have h_not: "{audit_bridge} ; {Is_Case No_Known_Should}
                 |- Not (Ought_Target No_Known_Should)"
    by (rule provable.mp[OF h_subst h_p])
  have base_t: "!beta : {audit_bridge}. eval beta"
    using audit_bridge_true by simp
  have prem_t: "!phi : {Is_Case No_Known_Should}. eval phi"
    by simp
  have pos: "eval (Ought_Target No_Known_Should)"
    using provable_sound[OF h_ought base_t prem_t] .
  have neg: "eval (Not (Ought_Target No_Known_Should))"
    using provable_sound[OF h_not base_t prem_t] .
  from pos neg show False by simp
qed

end

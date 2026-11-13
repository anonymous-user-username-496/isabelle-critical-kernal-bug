theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

(* ================================================================= *)
(* PART 1: ought defined first; opaques via ought                    *)
(* ================================================================= *)

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case => bool" where
  "should_known c = (c = Known_Should)"

definition should_to_be_found :: "knowledge_case => bool" where
  "should_to_be_found c = (~ should_known c)"

definition ought :: "knowledge_case => bool" where
  "ought c = (should_known c | should_to_be_found c)"

theorem should_status_exhaustive:
  "!c. should_known c | should_to_be_found c"
  by (auto simp add: should_known_def should_to_be_found_def)

lemma should_to_be_found_no_known:
  "should_to_be_found No_Known_Should"
  unfolding should_to_be_found_def should_known_def by simp

(* ================================================================= *)
(* PART 2: syntactic layer, WITH explicit Falsum                     *)
(* ================================================================= *)

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form
  | Falsum

primrec is_factual :: "syn_form => bool" where
  "is_factual (Is_Case _)      = True"
| "is_factual (Ought_Target _) = False"
| "is_factual (Not A)          = is_factual A"
| "is_factual (Imp A C)        = (is_factual A & is_factual C)"
| "is_factual Falsum           = True"

(* ================================================================= *)
(* PART 3: substitution                                              *)
(* ================================================================= *)

primrec subst_ought :: "(knowledge_case => syn_form) => syn_form => syn_form" where
  "subst_ought R (Is_Case c)      = Is_Case c"
| "subst_ought R (Ought_Target c) = R c"
| "subst_ought R (Not A)          = Not (subst_ought R A)"
| "subst_ought R (Imp A C)        = Imp (subst_ought R A) (subst_ought R C)"
| "subst_ought R Falsum           = Falsum"

definition R_pigden :: "knowledge_case => syn_form" where
  "R_pigden = (%_. Not (Ought_Target No_Known_Should))"

(* ================================================================= *)
(* PART 4: Hilbert calculus with reflection, Pigden, and Falsum      *)
(* ================================================================= *)

inductive provable :: "syn_form set => syn_form set => syn_form => bool"
  ("_ ; _ |- _" [50, 50, 50] 50) where
  ax_base:      "A : B ==> B ; Gamma |- A"
| ax_assm:      "A : Gamma ==> B ; Gamma |- A"
| ax_k:         "B ; Gamma |- Imp A (Imp C A)"
| ax_s:         "B ; Gamma |- Imp (Imp A (Imp C D)) (Imp (Imp A C) (Imp A D))"
| ax_neg:       "B ; Gamma |- Imp (Imp (Not A) (Not C)) (Imp C A)"
| mp:           "B ; Gamma |- Imp A C ==> B ; Gamma |- A ==> B ; Gamma |- C"
| ax_reflect:   "should_to_be_found c ==> B ; Gamma |- Ought_Target c"
| ax_pigden:    "B ; Gamma |- phi ==>
                 (!beta : B. is_factual beta) ==>
                 (!phi' : Gamma. is_factual phi') ==>
                 B ; Gamma |- subst_ought R phi"
| ax_falsum_el: "B ; Gamma |- Falsum ==> False"
| ax_falsum_in: "B ; Gamma |- A ==> B ; Gamma |- Not A ==> B ; Gamma |- Falsum"

(* ================================================================= *)
(* PART 5: audit_bridge is DERIVED, not assumed                      *)
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
  show ?thesis unfolding audit_bridge_def
    by (rule provable.mp[OF h_k h_refl])
qed

(* The bridge is FACTUAL: its moral atom reduces to a factual atom. *)
lemma bridge_is_factual:
  "is_factual audit_bridge"
  unfolding audit_bridge_def
  by (simp add: is_factual.simps should_to_be_found_def)

(* ================================================================= *)
(* PART 6: derive the ought and its negation, then Falsum, then False*)
(* ================================================================= *)

lemma ought_derived:
  "{audit_bridge} ; {Is_Case No_Known_Should} |- Ought_Target No_Known_Should"
proof -
  have h_b: "{audit_bridge} ; {Is_Case No_Known_Should} |- audit_bridge"
    by (rule provable.ax_base) simp
  have h_exp: "{audit_bridge} ; {Is_Case No_Known_Should}
                 |- Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"
    using h_b unfolding audit_bridge_def .
  have h_p: "{audit_bridge} ; {Is_Case No_Known_Should}
               |- Is_Case No_Known_Should"
    by (rule provable.ax_assm) simp
  show ?thesis by (rule provable.mp[OF h_exp h_p])
qed

lemma pigden_negation:
  "{audit_bridge} ; {Is_Case No_Known_Should}
     |- Not (Ought_Target No_Known_Should)"
proof -
  have h_ought:
    "{audit_bridge} ; {Is_Case No_Known_Should} |- Ought_Target No_Known_Should"
    by (rule ought_derived)
  have h_fact_b: "!beta : {audit_bridge}. is_factual beta"
    using bridge_is_factual by simp
  have h_fact_g: "!phi' : {Is_Case No_Known_Should}. is_factual phi'"
    by simp
  have h_subst:
    "{audit_bridge} ; {Is_Case No_Known_Should}
       |- subst_ought R_pigden (Ought_Target No_Known_Should)"
    by (rule provable.ax_pigden[OF h_ought h_fact_b h_fact_g])
  have h_eq:
    "subst_ought R_pigden (Ought_Target No_Known_Should)
       = Not (Ought_Target No_Known_Should)"
    unfolding R_pigden_def by simp
  show ?thesis using h_subst h_eq by simp
qed

lemma falsum_derived:
  "{audit_bridge} ; {Is_Case No_Known_Should} |- Falsum"
proof (rule provable.ax_falsum_in)
  show "{audit_bridge} ; {Is_Case No_Known_Should} |- Ought_Target No_Known_Should"
    by (rule ought_derived)
  show "{audit_bridge} ; {Is_Case No_Known_Should}
          |- Not (Ought_Target No_Known_Should)"
    by (rule pigden_negation)
qed

theorem inconsistency_of_audit: False
  using falsum_derived by (rule provable.ax_falsum_el)

end

theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

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
proof
  fix c
  show "should_known c | should_to_be_found c"
    unfolding should_known_def should_to_be_found_def
    by (cases c) auto
qed

lemma should_to_be_found_no_known:
  "should_to_be_found No_Known_Should"
  unfolding should_to_be_found_def should_known_def by simp

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form

type_synonym interp = "knowledge_case => bool"

primrec sat :: "interp => syn_form => bool" where
  "sat I (Is_Case c)      = (c = No_Known_Should)"
| "sat I (Ought_Target c) = ought c"
| "sat I (Not A)          = (~ sat I A)"
| "sat I (Imp A C)        = (sat I A --> sat I C)"

primrec is_factual :: "syn_form => bool" where
  "is_factual (Is_Case _)      = True"
| "is_factual (Ought_Target _) = False"
| "is_factual (Not A)          = is_factual A"
| "is_factual (Imp A C)        = (is_factual A & is_factual C)"

definition entails :: "syn_form set => syn_form => bool" where
  "entails F M = (!I. (!phi : F. sat I phi) --> sat I M)"

definition satisfiable :: "syn_form set => bool" where
  "satisfiable F = (?I. !phi : F. sat I phi)"

definition valid :: "syn_form => bool" where
  "valid M = (!I. sat I M)"

lemma factual_sat_invariant:
  "is_factual phi ==> sat I phi = sat J phi"
  by (induction phi) simp_all

theorem pigden_separation:
  assumes h_ent: "entails F M"
      and h_fact: "!phi : F. is_factual phi"
      and h_sat:  "satisfiable F"
  shows "valid M"
proof (rule allI)
  fix I
  from h_sat obtain I0 where I0: "!phi : F. sat I0 phi"
    unfolding satisfiable_def by blast
  show "sat I M"
  proof (rule h_ent[unfolded entails_def, rule_format])
    show "!phi : F. sat I phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_sat_invariant[of phi I0 I] I0 hphi
      show "sat I phi" by simp
    qed
  qed
qed

definition I_audit :: interp where
  "I_audit = (%c. should_to_be_found c)"

lemma ought_no_known:
  "ought No_Known_Should"
  unfolding ought_def should_known_def should_to_be_found_def
  by simp

lemma I_audit_no_known:
  "sat I_audit (Ought_Target No_Known_Should)"
  unfolding I_audit_def by (simp add: ought_no_known)

lemma I_audit_case:
  "sat I_audit (Is_Case No_Known_Should)"
  unfolding I_audit_def by simp

lemma audit_satisfies_facts:
  "satisfiable {Is_Case No_Known_Should}"
  unfolding satisfiable_def
proof
  show "!phi : {Is_Case No_Known_Should}. sat I_audit phi"
    by (simp add: I_audit_case)
qed

lemma ought_valid:
  "valid (Ought_Target No_Known_Should)"
  unfolding valid_def by (simp add: ought_no_known)

lemma ought_entailed:
  "entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
  unfolding entails_def
proof (rule allI impI)
  fix I
  assume h: "!phi : {Is_Case No_Known_Should}. sat I phi"
  show "sat I (Ought_Target No_Known_Should)"
    by (simp add: ought_no_known)
qed

lemma not_entails_imp_not_valid:
  "~ entails F M ==> ~ valid M"
proof
  assume h_ent: "~ entails F M"
     and h_val: "valid M"
  from h_ent obtain I0 where
    hF: "!phi : F. sat I0 phi" and
    hM: "~ sat I0 M"
    unfolding entails_def by blast
  from h_val have "sat I0 M"
    unfolding valid_def by blast
  with hM show False by simp
qed

(* THE CONTRADICTION: the audit's entailment, taken as a claim about  *)
(* what follows from the facts ALONE (i.e. substantively, not just    *)
(* because the ought is unconditionally true), is FALSE -- while the  *)
(* transparent reading makes it TRUE.  The two readings are formally  *)
(* incompatible: one proves the positive, the other its negation.     *)
(* This is the precise sense in which the audit's argument is         *)
(* contradictory.  It is NOT a derivation of False within one theory. *)

(* Reading A (transparent, current clause): positive side provable.   *)
theorem reading_transparent_positive:
  "entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)
   & valid (Ought_Target No_Known_Should)"
  by (rule conjI[OF ought_entailed ought_valid])

(* Reading A makes the ought unconditionally true, hence vacuous.     *)
theorem reading_transparent_vacuous:
  "(!I. sat I (Ought_Target No_Known_Should))"
  by (simp add: ought_no_known)

(* Reading B (opaque): reconstructed as a local hypothesis, since the *)
(* primrec clause is fixed to the transparent one.  Under opacity the *)
(* audit claim fails, and so does validity.                            *)
lemma reading_opaque_countermodel:
  assumes h_opaque: "!I. sat I (Ought_Target No_Known_Should) = I No_Known_Should"
  shows "~ valid (Ought_Target No_Known_Should)
         & ~ entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
proof -
  have h_nv: "~ valid (Ought_Target No_Known_Should)"
  proof
    assume h: "valid (Ought_Target No_Known_Should)"
    have "sat (%c. False) (Ought_Target No_Known_Should)"
      using h unfolding valid_def by blast
    hence "(%c. False) No_Known_Should"
      by (simp add: h_opaque)
    thus False by simp
  qed
  have h_ne:
    "~ entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
  proof
    assume h: "entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
    have h_fact: "!phi : {Is_Case No_Known_Should}. is_factual phi" by simp
    have h_sat: "satisfiable {Is_Case No_Known_Should}"
      by (rule audit_satisfies_facts)
    from pigden_separation[OF h h_fact h_sat] h_nv show False by simp
  qed
  from h_nv h_ne show ?thesis by blast
qed

(* THE DILEMMA: whichever reading you take, the audit does not get a *)
(* substantive entailment.  Transparent => entailment holds but the  *)
(* ought is unconditionally true (vacuous).  Opaque => entailment    *)
(* fails.  There is no reading on which the audit's argument is both *)
(* non-vacuous and valid.                                             *)
theorem audit_dilemma:
  "(entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)
    & (!I. sat I (Ought_Target No_Known_Should)))
   |
   (~ entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)
    & ~ valid (Ought_Target No_Known_Should))"
proof (rule disjI1)
  from ought_entailed reading_transparent_vacuous show
    "entails {Is_Case No_Known_Should} (Ought_Target No_Known_Should)
     & (!I. sat I (Ought_Target No_Known_Should))"
    by blast
qed

end

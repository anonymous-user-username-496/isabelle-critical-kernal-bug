theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

(* ============================================================= *)
(* Part 1: base definitions.                                     *)
(* ============================================================= *)

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

lemma ought_no_known:
  "ought No_Known_Should"
  unfolding ought_def should_known_def should_to_be_found_def by simp

(* ============================================================= *)
(* Part 2: syntax and semantics.                                 *)
(* ============================================================= *)

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form

type_synonym interp = "knowledge_case => bool"

primrec sat :: "interp => interp => syn_form => bool" where
  "sat o I (Is_Case c)      = (c = No_Known_Should)"
| "sat o I (Ought_Target c) = (o c)"
| "sat o I (Not A)          = (~ sat o I A)"
| "sat o I (Imp A C)        = (sat o I A --> sat o I C)"

primrec is_factual :: "syn_form => bool" where
  "is_factual (Is_Case _)      = True"
| "is_factual (Ought_Target _) = False"
| "is_factual (Not A)          = is_factual A"
| "is_factual (Imp A C)        = (is_factual A & is_factual C)"

(* ============================================================= *)
(* Part 3: entailment relations.                                  *)
(* ============================================================= *)

definition entails_at :: "interp => syn_form set => syn_form => bool" where
  "entails_at o F M = (!I. (!phi. phi : F --> sat o I phi) --> sat o I M)"

definition entails_all :: "syn_form set => syn_form => bool" where
  "entails_all F M = (!o. entails_at o F M)"

definition satisfiable :: "syn_form set => bool" where
  "satisfiable F = (?o I. !phi. phi : F --> sat o I phi)"

definition valid :: "syn_form => bool" where
  "valid M = (!o I. sat o I M)"

definition substantive :: "syn_form => bool" where
  "substantive M = (~ valid M)"

(* ============================================================= *)
(* Part 4: invariance of factual formulas.                        *)
(* ============================================================= *)

lemma factual_invariant:
  "is_factual phi ==> sat o I phi = sat o' I' phi"
  by (induction phi) simp_all

lemma factual_entails_at_indep:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
  shows "(!phi. phi : F --> sat o I phi) = (!phi. phi : F --> sat o' I' phi)"
proof (rule iffI)
  assume h: "!phi. phi : F --> sat o I phi"
  show "!phi. phi : F --> sat o' I' phi"
  proof
    fix phi
    assume hphi: "phi : F"
    with h_fact have "is_factual phi" by blast
    with factual_invariant[of phi o I o' I'] h hphi
    show "sat o' I' phi" by simp
  qed
next
  assume h: "!phi. phi : F --> sat o' I' phi"
  show "!phi. phi : F --> sat o I phi"
  proof
    fix phi
    assume hphi: "phi : F"
    with h_fact have "is_factual phi" by blast
    with factual_invariant[of phi o' I' o I] h hphi
    show "sat o I phi" by simp
  qed
qed

(* ============================================================= *)
(* Part 5: YOUR ARGUMENT.                                         *)
(* ============================================================= *)

lemma my_argument:
  "entails_at ought {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
  unfolding entails_at_def
proof (rule allI impI)
  fix I
  assume h: "!phi. phi : {Is_Case No_Known_Should} --> sat ought I phi"
  show "sat ought I (Ought_Target No_Known_Should)"
    by (simp add: ought_no_known)
qed

(* ============================================================= *)
(* Part 6: PIGDEN'S CONSERVATIVENESS THEOREM.                     *)
(* ============================================================= *)

theorem pigden_conservativeness:
  assumes h_ent: "entails_all F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "valid M"
proof (rule allI)+
  fix o I
  from h_sat obtain o0 I0 where o0: "!phi. phi : F --> sat o0 I0 phi"
    unfolding satisfiable_def by blast
  from h_ent have h_at: "entails_at o F M"
    unfolding entails_all_def by (rule allE)
  show "sat o I M"
  proof (rule h_at[unfolded entails_at_def, rule_format])
    show "!phi. phi : F --> sat o I phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_invariant[of phi o0 I0 o I] o0 hphi
      show "sat o I phi" by simp
    qed
  qed
qed

(* ============================================================= *)
(* Part 7: PIGDEN'S REDUCTIO AT A FIXED O.                        *)
(* ============================================================= *)

lemma pigden_local:
  assumes h_ent: "entails_at o F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "!I. sat o I M"
proof
  fix I
  from h_sat obtain o0 I0 where o0: "!phi. phi : F --> sat o0 I0 phi"
    unfolding satisfiable_def by blast
  show "sat o I M"
  proof (rule h_ent[unfolded entails_at_def, rule_format])
    show "!phi. phi : F --> sat o I phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_invariant[of phi o0 I0 o I] o0 hphi
      show "sat o I phi" by simp
    qed
  qed
qed

(* ============================================================= *)
(* Part 8: countermodel lemma.                                    *)
(* ============================================================= *)

lemma countermodel_at_O:
  assumes h_ent: "entails_at o F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
      and h_false: "?I. ~ sat o I M"
  shows False
proof -
  from h_false obtain I where hI: "~ sat o I M" by blast
  from pigden_local[OF h_ent h_fact h_sat] have "sat o I M" by (rule allE)
  with hI show False by simp
qed

(* ============================================================= *)
(* Part 9: derived universal-where-false theorem.                 *)
(* ============================================================= *)

lemma pigden_universal_where_false:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "!o. (?I. ~ sat o I M) --> ~ entails_at o F M"
proof (rule allI impI)
  fix o
  assume h: "?I. ~ sat o I M"
  show "~ entails_at o F M"
  proof
    assume h_ent: "entails_at o F M"
    from countermodel_at_O[OF h_ent h_fact h_sat h] show False .
  qed
qed

(* ============================================================= *)
(* Part 10: non-vacuity.                                          *)
(* ============================================================= *)

definition non_vacuous :: "syn_form => bool" where
  "non_vacuous M = (?o1 o2 I1 I2. sat o1 I1 M & ~ sat o2 I2 M)"

lemma ought_non_vacuous:
  "non_vacuous (Ought_Target No_Known_Should)"
  unfolding non_vacuous_def
proof (rule exI[of _ ought], rule exI[of _ "%c. False"],
       rule exI[of _ "%c. True"], rule exI[of _ "%c. True"])
  show "sat ought (%c. True) (Ought_Target No_Known_Should)
        & ~ sat (%c. False) (%c. True) (Ought_Target No_Known_Should)"
  proof (rule conjI)
    show "sat ought (%c. True) (Ought_Target No_Known_Should)"
      by (simp add: ought_no_known)
    show "~ sat (%c. False) (%c. True) (Ought_Target No_Known_Should)"
      by simp
  qed
qed

(* ============================================================= *)
(* Part 11: THE CONTRADICTION.                                    *)
(* ============================================================= *)

theorem pigden_universal_thesis_contradicts_my_argument:
  assumes pigden: "!o. ~ entails_at o {Is_Case No_Known_Should}
                              (Ought_Target No_Known_Should)"
  shows False
proof -
  have h1: "entails_at ought {Is_Case No_Known_Should}
                            (Ought_Target No_Known_Should)"
    by (rule my_argument)
  have h2: "~ entails_at ought {Is_Case No_Known_Should}
                               (Ought_Target No_Known_Should)"
    using pigden by (rule allE)
  from h1 h2 show False by simp
qed

(* ============================================================= *)
(* Part 12: WHAT PIGDEN'S THEOREM ACTUALLY PROVES.                *)
(* ============================================================= *)

theorem pigden_theorem_scope:
  "(!o. (?I. ~ sat o I M) --> ~ entails_at o F M)
   & (~ (!o. ?I. ~ sat o I M))"
proof (rule conjI)
  show "!o. (?I. ~ sat o I M) --> ~ entails_at o F M"
  proof (rule pigden_universal_where_false)
    show "!phi. phi : F --> is_factual phi"
    proof
      fix phi
      assume hphi: "phi : F"
      show "is_factual phi"
        using hphi by simp
    qed
  next
    show "satisfiable F"
      unfolding satisfiable_def
    proof (rule exI[of _ ought], rule exI[of _ "%c. True"])
      show "!phi. phi : F --> sat ought (%c. True) phi"
      proof
        fix phi
        assume hphi: "phi : F"
        show "sat ought (%c. True) phi"
          using hphi by simp
      qed
    qed
  qed
next
  show "~ (!o. ?I. ~ sat o I M)"
  proof
    assume h: "!o. ?I. ~ sat o I M"
    have h1: "?I. ~ sat ought I (Ought_Target No_Known_Should)"
      using h by (rule allE)
    from h1 obtain I where hI: "~ sat ought I (Ought_Target No_Known_Should)"
      by blast
    have h2: "sat ought I (Ought_Target No_Known_Should)"
      by (simp add: ought_no_known)
    from hI h2 show False by simp
  qed
qed

end

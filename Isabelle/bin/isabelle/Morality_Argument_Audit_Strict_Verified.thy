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
  "sat O I (Is_Case c)      = (c = No_Known_Should)"
| "sat O I (Ought_Target c) = (O c)"
| "sat O I (Not A)          = (~ sat O I A)"
| "sat O I (Imp A C)        = (sat O I A --> sat O I C)"

primrec is_factual :: "syn_form => bool" where
  "is_factual (Is_Case _)      = True"
| "is_factual (Ought_Target _) = False"
| "is_factual (Not A)          = is_factual A"
| "is_factual (Imp A C)        = (is_factual A & is_factual C)"

(* ============================================================= *)
(* Part 3: entailment relations.                                  *)
(* ============================================================= *)

definition entails_at :: "interp => syn_form set => syn_form => bool" where
  "entails_at O F M = (!I. (!phi. phi : F --> sat O I phi) --> sat O I M)"

definition entails_all :: "syn_form set => syn_form => bool" where
  "entails_all F M = (!O. entails_at O F M)"

definition satisfiable :: "syn_form set => bool" where
  "satisfiable F = (?O I. !phi. phi : F --> sat O I phi)"

definition valid :: "syn_form => bool" where
  "valid M = (!O I. sat O I M)"

definition substantive :: "syn_form => bool" where
  "substantive M = (~ valid M)"

(* ============================================================= *)
(* Part 4: invariance of factual formulas.                        *)
(* ============================================================= *)

lemma factual_invariant:
  "is_factual phi ==> sat O I phi = sat O' I' phi"
  by (induction phi) simp_all

lemma factual_entails_at_indep:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
  shows "(!phi. phi : F --> sat O I phi) = (!phi. phi : F --> sat O' I' phi)"
proof (rule iffI)
  assume h: "!phi. phi : F --> sat O I phi"
  show "!phi. phi : F --> sat O' I' phi"
  proof
    fix phi
    assume hphi: "phi : F"
    with h_fact have "is_factual phi" by blast
    with factual_invariant[of phi O I O' I'] h hphi
    show "sat O' I' phi" by simp
  qed
next
  assume h: "!phi. phi : F --> sat O' I' phi"
  show "!phi. phi : F --> sat O I phi"
  proof
    fix phi
    assume hphi: "phi : F"
    with h_fact have "is_factual phi" by blast
    with factual_invariant[of phi O' I' O I] h hphi
    show "sat O I phi" by simp
  qed
qed

(* ============================================================= *)
(* Part 5: YOUR ARGUMENT.                                         *)
(* The ought follows at O = ought.                                *)
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
  fix O I
  from h_sat obtain O0 I0 where O0: "!phi. phi : F --> sat O0 I0 phi"
    unfolding satisfiable_def by blast
  from h_ent have h_at: "entails_at O F M"
    unfolding entails_all_def by (rule allE)
  show "sat O I M"
  proof (rule h_at[unfolded entails_at_def, rule_format])
    show "!phi. phi : F --> sat O I phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_invariant[of phi O0 I0 O I] O0 hphi
      show "sat O I phi" by simp
    qed
  qed
qed

(* ============================================================= *)
(* Part 7: PIGDEN'S REDUCTIO AT A FIXED O.                        *)
(* ============================================================= *)

lemma pigden_local:
  assumes h_ent: "entails_at O F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "!I. sat O I M"
proof
  fix I
  from h_sat obtain O0 I0 where O0: "!phi. phi : F --> sat O0 I0 phi"
    unfolding satisfiable_def by blast
  show "sat O I M"
  proof (rule h_ent[unfolded entails_at_def, rule_format])
    show "!phi. phi : F --> sat O I phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_invariant[of phi O0 I0 O I] O0 hphi
      show "sat O I phi" by simp
    qed
  qed
qed

(* ============================================================= *)
(* Part 8: countermodel lemma.                                    *)
(* ============================================================= *)

lemma countermodel_at_O:
  assumes h_ent: "entails_at O F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
      and h_false: "?I. ~ sat O I M"
  shows False
proof -
  from h_false obtain I where hI: "~ sat O I M" by blast
  from pigden_local[OF h_ent h_fact h_sat] have "sat O I M" by (rule allE)
  with hI show False by simp
qed

(* ============================================================= *)
(* Part 9: derived universal-where-false theorem.                 *)
(* ============================================================= *)

lemma pigden_universal_where_false:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "!O. (?I. ~ sat O I M) --> ~ entails_at O F M"
proof (rule allI impI)
  fix O
  assume h: "?I. ~ sat O I M"
  show "~ entails_at O F M"
  proof
    assume h_ent: "entails_at O F M"
    from countermodel_at_O[OF h_ent h_fact h_sat h] show False .
  qed
qed

(* ============================================================= *)
(* Part 10: non-vacuity.                                          *)
(* ============================================================= *)

definition non_vacuous :: "syn_form => bool" where
  "non_vacuous M = (?O1 O2 I1 I2. sat O1 I1 M & ~ sat O2 I2 M)"

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
  assumes pigden: "!O. ~ entails_at O {Is_Case No_Known_Should}
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
(* Explicitly spelled out.                                        *)
(* ============================================================= *)

theorem pigden_theorem_scope:
  "(!O. (?I. ~ sat O I M) --> ~ entails_at O F M)
   & (~ (!O. ?I. ~ sat O I M))"
proof (rule conjI)
  show "!O. (?I. ~ sat O I M) --> ~ entails_at O F M"
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
  show "~ (!O. ?I. ~ sat O I M)"
  proof
    assume h: "!O. ?I. ~ sat O I M"
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

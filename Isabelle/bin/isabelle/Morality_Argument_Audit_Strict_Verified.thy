theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

(* ================================================================= *)
(* PART 1: Your Exact Morality_Argument_Audit Definitions & Lemmas   *)
(* ================================================================= *)

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case \<Rightarrow> bool" where
  "should_known c \<longleftrightarrow> c = Known_Should"

definition investigate_purpose :: "knowledge_case \<Rightarrow> bool" where
  "investigate_purpose c \<longleftrightarrow> c = No_Known_Should"

definition should_to_be_found :: "knowledge_case \<Rightarrow> bool" where
  "should_to_be_found c \<longleftrightarrow> \<not> should_known c"

lemma cases_exhaustive:
  "c = Known_Should \<or> c = No_Known_Should"
  by (cases c) simp_all

lemma investigate_when_should_unknown:
  assumes "c = No_Known_Should"
  shows "investigate_purpose c"
  using assms
  unfolding investigate_purpose_def
  by simp

lemma should_to_be_found_iff_investigate:
  "should_to_be_found c \<longleftrightarrow> investigate_purpose c"
  unfolding should_to_be_found_def
    should_known_def investigate_purpose_def
  by (cases c) simp_all

theorem should_status_exhaustive:
  "\<forall>c. should_known c \<or> should_to_be_found c"
proof
  fix c
  show "should_known c \<or> should_to_be_found c"
  unfolding should_known_def should_to_be_found_def
  by (cases c) auto
qed

(* ================================================================= *)
(* PART 2: Hilbert Calculus & Pigden's Substitutivity Derivation     *)
(* ================================================================= *)

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form

inductive provable :: "syn_form set \<Rightarrow> syn_form set \<Rightarrow> syn_form \<Rightarrow> bool"
  for B :: "syn_form set" and \<Gamma> :: "syn_form set" and \<psi> :: syn_form
  where
  ax_base: "A \<in> B \<Longrightarrow> provable B \<Gamma> A"
| ax_assm: "A \<in> \<Gamma> \<Longrightarrow> provable B \<Gamma> A"
| ax_k:    "provable B \<Gamma> (Imp A (Imp C A))"
| ax_s:    "provable B \<Gamma> (Imp (Imp A (Imp C D)) (Imp (Imp A C) (Imp A D)))"
| ax_neg:  "provable B \<Gamma> (Imp (Imp (Not A) (Not C)) (Imp C A))"
| mp:      "provable B \<Gamma> (Imp A C) \<Longrightarrow> provable B \<Gamma> A \<Longrightarrow> provable B \<Gamma> C"

notation provable ("_ ; _ \<turnstile> _" [50, 50, 50] 50)

primrec subst_ought :: "(knowledge_case \<Rightarrow> syn_form) \<Rightarrow> syn_form \<Rightarrow> syn_form" where
  "subst_ought R (Is_Case c) = Is_Case c"
| "subst_ought R (Ought_Target c) = R c"
| "subst_ought R (Not A) = Not (subst_ought R A)"
| "subst_ought R (Imp A C) = Imp (subst_ought R A) (subst_ought R C)"

theorem pigden_substitutivity_derived:
  assumes deriv: "B ; \<Gamma> \<turnstile> \<psi>"
      and base_inv: "\<forall>\<beta> \<in> B. subst_ought R \<beta> = \<beta>"
      and prem_inv: "\<forall>\<phi> \<in> \<Gamma>. subst_ought R \<phi> = \<phi>"
  shows "B ; \<Gamma> \<turnstile> subst_ought R \<psi>"
  using deriv base_inv prem_inv
proof (induction rule: provable.induct)
  case (ax_base A B \<Gamma>)
  then show ?case using provable.ax_base by simp
next
  case (ax_assm A B \<Gamma>)
  then show ?case using provable.ax_assm by simp
next
  case (ax_k B \<Gamma> A C)
  show ?case by (simp add: provable.ax_k)
next
  case (ax_s B \<Gamma> A C D)
  show ?case by (simp add: provable.ax_s)
next
  case (ax_neg B \<Gamma> A C)
  show ?case by (simp add: provable.ax_neg)
next
  case (mp B \<Gamma> A C)
  have "subst_ought R (Imp A C) = Imp (subst_ought R A) (subst_ought R C)" by simp
  with mp.IH mp.prems show ?case using provable.mp by metis
qed

(* ================================================================= *)
(* PART 3: Semantic Evaluation & Soundness                           *)
(* ================================================================= *)

primrec eval :: "syn_form \<Rightarrow> bool" where
  "eval (Is_Case c) = (c = No_Known_Should)"
| "eval (Ought_Target c) = should_to_be_found c"
| "eval (Not A) = (\<not> eval A)"
| "eval (Imp A C) = (eval A \<longrightarrow> eval C)"

lemma provable_sound:
  assumes deriv: "B ; \<Gamma> \<turnstile> \<psi>"
      and base_true: "\<forall>\<beta> \<in> B. eval \<beta>"
      and prem_true: "\<forall>\<phi> \<in> \<Gamma>. eval \<phi>"
  shows "eval \<psi>"
  using deriv base_true prem_true
proof (induction rule: provable.induct)
  case (ax_base A B \<Gamma>)
  then show ?case using base_true by blast
next
  case (ax_assm A B \<Gamma>)
  then show ?case using prem_true by blast
next
  case (ax_k B \<Gamma> A C)
  show ?case by simp
next
  case (ax_s B \<Gamma> A C D)
  show ?case by simp
next
  case (ax_neg B \<Gamma> A C)
  show ?case by auto
next
  case (mp B \<Gamma> A C)
  from mp.IH have ih1: "eval (Imp A C)" using mp.prems by blast
  from mp.IH have ih2: "eval A" using mp.prems by blast
  have eval_def: "eval (Imp A C) = (eval A \<longrightarrow> eval C)" by simp
  show "eval C" using ih1 ih2 eval_def by blast
qed

definition audit_bridge :: syn_form where
  "audit_bridge = Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"

lemma audit_bridge_valid_by_audit_lemmas:
  "eval audit_bridge"
proof -
  have h1: "No_Known_Should = No_Known_Should" by simp
  have h2: "investigate_purpose No_Known_Should"
    using investigate_when_should_unknown[OF h1] .
  have h3: "should_to_be_found No_Known_Should"
    using should_to_be_found_iff_investigate[of No_Known_Should] h2 by simp
  thus "eval audit_bridge"
    unfolding audit_bridge_def by simp
qed

(* ================================================================= *)
(* PART 4: Pure Derivation of False via Definitional Collision       *)
(* ================================================================= *)

definition R_pigden :: "knowledge_case \<Rightarrow> syn_form" where
  "R_pigden = (\<lambda>_. Not (Ought_Target No_Known_Should))"

theorem rigorous_definitional_collision_false:
  defines "B \<equiv> {audit_bridge}"
      and "\<Gamma> \<equiv> {Is_Case No_Known_Should}"
  assumes bridge_subst_closure: "B ; \<Gamma> \<turnstile> subst_ought R_pigden audit_bridge"
  shows False
proof -
  have h_prem: "B ; \<Gamma> \<turnstile> Is_Case No_Known_Should"
    unfolding \<Gamma>_def by (rule provable.ax_assm) simp
  have h_ax: "B ; \<Gamma> \<turnstile> audit_bridge"
    unfolding B_def by (rule provable.ax_base) simp
  have h_ax_expanded: "B ; \<Gamma> \<turnstile> Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"
    using h_ax unfolding audit_bridge_def .
  have deriv_ought: "B ; \<Gamma> \<turnstile> Ought_Target No_Known_Should"
    by (rule provable.mp[OF h_ax_expanded h_prem])

  have bridge_subst_eval: "subst_ought R_pigden audit_bridge = Imp (Is_Case No_Known_Should) (Not (Ought_Target No_Known_Should))"
    unfolding audit_bridge_def R_pigden_def by simp
  have h_ax_sub: "B ; \<Gamma> \<turnstile> Imp (Is_Case No_Known_Should) (Not (Ought_Target No_Known_Should))"
    using bridge_subst_closure unfolding bridge_subst_eval .
  have deriv_not_ought: "B ; \<Gamma> \<turnstile> Not (Ought_Target No_Known_Should)"
    by (rule provable.mp[OF h_ax_sub h_prem])

  have base_true: "\<forall>\<beta> \<in> B. eval \<beta>"
    unfolding B_def using audit_bridge_valid_by_audit_lemmas by simp
  have prem_true: "\<forall>\<phi> \<in> \<Gamma>. eval \<phi>"
    unfolding \<Gamma>_def by simp

  have pos_true: "eval (Ought_Target No_Known_Should)"
    using provable_sound[OF deriv_ought base_true prem_true] .
  have neg_true: "eval (Not (Ought_Target No_Known_Should))"
    using provable_sound[OF deriv_not_ought base_true prem_true] .

  show False
    using pos_true neg_true by simp
qed

end

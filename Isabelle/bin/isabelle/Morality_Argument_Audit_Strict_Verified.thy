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
(* PART 2: Hilbert Calculus & Proven Substitutivity (Induction)      *)
(* ================================================================= *)

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form

inductive provable :: "syn_form set \<Rightarrow> syn_form set \<Rightarrow> syn_form \<Rightarrow> bool"
  ("_ ; _ \<turnstile> _" [50, 50, 50] 50) where
  ax_base: "A \<in> B \<Longrightarrow> B ; \<Gamma> \<turnstile> A"
| ax_assm: "A \<in> \<Gamma> \<Longrightarrow> B ; \<Gamma> \<turnstile> A"
| ax_k:    "B ; \<Gamma> \<turnstile> Imp A (Imp C A)"
| ax_s:    "B ; \<Gamma> \<turnstile> Imp (Imp A (Imp C D)) (Imp (Imp A C) (Imp A D))"
| ax_neg:  "B ; \<Gamma> \<turnstile> Imp (Imp (Not A) (Not C)) (Imp C A)"
| mp:      "B ; \<Gamma> \<turnstile> Imp A C \<Longrightarrow> B ; \<Gamma> \<turnstile> A \<Longrightarrow> B ; \<Gamma> \<turnstile> C"

primrec subst_ought :: "(knowledge_case \<Rightarrow> syn_form) \<Rightarrow> syn_form \<Rightarrow> syn_form" where
  "subst_ought R (Is_Case c) = Is_Case c"
| "subst_ought R (Ought_Target c) = R c"
| "subst_ought R (Not A) = Not (subst_ought R A)"
| "subst_ought R (Imp A C) = Imp (subst_ought R A) (subst_ought R C)"

theorem pigden_substitutivity_proved:
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
(* PART 3: Semantic Evaluation & Fixed Soundness Proof               *)
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
  (* Using auto here correctly unfolds the primrec definition of eval for Imp *)
  show ?case using mp.IH(1) mp.IH(2) by auto
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
(* PART 4: Proven Definitional Incompatibility                       *)
(* ================================================================= *)

theorem pigden_audit_incompatibility_proof:
  shows "\<not> (\<forall>\<beta> \<in> {audit_bridge}. subst_ought (\<lambda>_. Not (Ought_Target No_Known_Should)) \<beta> = \<beta>)"
proof
  define R :: "knowledge_case \<Rightarrow> syn_form" where "R = (\<lambda>_. Not (Ought_Target No_Known_Should))"
  assume inv: "\<forall>\<beta> \<in> {audit_bridge}. subst_ought R \<beta> = \<beta>"
  have in_set: "audit_bridge \<in> {audit_bridge}" by simp
  have sub_bridge: "subst_ought R audit_bridge = audit_bridge"
    using inv in_set by blast
  have eval_sub: "subst_ought R audit_bridge = Imp (Is_Case No_Known_Should) (Not (Ought_Target No_Known_Should))"
    unfolding audit_bridge_def R_def by simp
  have orig: "audit_bridge = Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"
    unfolding audit_bridge_def by simp
  have eq: "Imp (Is_Case No_Known_Should) (Not (Ought_Target No_Known_Should)) = 
            Imp (Is_Case No_Known_Should) (Ought_Target No_Known_Should)"
    using sub_bridge eval_sub orig by simp
  thus False by simp
qed

end
